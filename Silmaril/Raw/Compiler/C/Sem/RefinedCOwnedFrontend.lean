module

public import Silmaril.Compiler.C.Sem.RefinedCOwnedByte.Defs
/-! A narrow elaboration target for one owned u8 singleton pointer and a void
result. Location ghosts have an explicit flat-address view, distinct from integer
ghosts. This is not RefinedC parser, provenance, or Iris adequacy. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedFrontend
open Silmaril.Cerberus.Assertion
open ConcreteResources

abbrev LocEnv := String → Nat

structure Contract where
  parameters : List String
  locations : List String
  pointer : String
  input : Pure.Term
  output : Pure.Term
  requires : Pure.Formula
  ensures : Pure.Formula
  deriving Repr, DecidableEq

def Contract.pre (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (args : List Int) (memory : C1.Memory) : Prop :=
  args = [(locations c.pointer : Int)] ∧ locations c.pointer < 18446744073709551616 ∧
    Holds ρ ((RefinedCOwnedByte.singleton (c.input.eval ρ)).owned
      (locations c.pointer) c.input) memory ∧ c.requires.holds ρ

def Contract.post (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (memory : C1.Memory) : Prop :=
  Holds ρ ((RefinedCOwnedByte.singleton (c.output.eval ρ)).owned
    (locations c.pointer) c.output) memory ∧ c.ensures.holds ρ

def Contract.obligation (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) (initial final : C1.Memory) : Prop :=
  c.pre before locations args initial → c.post after locations final

def Contract.leanGoal (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) (initial final : C1.Memory) : Prop :=
  (args = [(locations c.pointer : Int)] ∧ locations c.pointer < 18446744073709551616 ∧
    LeanGoal before ((RefinedCOwnedByte.singleton (c.input.eval before)).owned
      (locations c.pointer) c.input) initial ∧ c.requires.leanGoal before) →
  LeanGoal after ((RefinedCOwnedByte.singleton (c.output.eval after)).owned
    (locations c.pointer) c.output) final ∧ c.ensures.leanGoal after

theorem Contract.leanGoal_correct (c : Contract) (before after : Pure.Env)
    (locations : LocEnv) (args : List Int) (initial final : C1.Memory) :
    c.leanGoal before after locations args initial final ↔
      c.obligation before after locations args initial final := by
  simp only [leanGoal, obligation, pre, post, ConcreteResources.leanGoal_correct,
    Pure.Formula.leanGoal_correct]

/-- The authored increment fixture, with every supported obligation retained. -/
def incrementContract : Contract :=
  ⟨["n"], ["p"], "p", .var "n", .add (.var "n") (.literal 1),
    .and (.lt (.var "n") (.literal 255)) .truth, .truth⟩

/-- Every admissible byte and arbitrary frame byte has a concrete input witness. -/
theorem increment_pre_pair (v w : UInt8) (safe : v.toNat < 255) :
    incrementContract.pre (fun _ => (v.toNat : Int)) (fun _ => C1.base)
      [(C1.base : Int)] (pairMemory v w) := by
  refine ⟨rfl, by decide, ?_, ?_⟩
  · apply (refinedC_owned_iff _ _ _ _ _).mpr
    refine ⟨?_, v, rfl, pair_left v w⟩
    have range := v.toNat_lt_size
    simp [incrementContract, RefinedCOwnedByte.singleton, RefinedC.IntRefinement.holds,
      RefinedC.IntegerType.admits, RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
      RefinedC.IntegerType.signed, RefinedC.IntegerType.bits, Pure.Term.eval]
    omega
  · change (v.toNat : Int) < 255 ∧ True
    exact ⟨by exact_mod_cast safe, trivial⟩

/-- A generated contract can be used together with actual function execution,
including an arbitrary disjoint finite resource frame. -/
theorem increment_execution (ρ : Pure.Env) (locations : LocEnv) (initial : C1.Env)
    (pre : incrementContract.pre ρ locations [(locations "p" : Int)] initial.mem)
    (frame : Resources.Heap) (concrete : Realizes initial.mem frame)
    (outside : ∀ n, (locations "p", n) ∉ frame) :
    ∃ finalState,
      C1.callFn RefinedCOwnedByte.program 8 RefinedCOwnedByte.fSym
        [(locations "p" : Int)] initial = .ok (0, finalState) ∧
      incrementContract.post ρ locations finalState.mem ∧
      incrementContract.leanGoal ρ ρ locations [(locations "p" : Int)] initial.mem finalState.mem ∧
      Realizes finalState.mem frame ∧ finalState.regs = initial.regs ∧
      finalState.frame = initial.frame ∧ finalState.out = initial.out ∧
      finalState.mem.sp = initial.mem.sp := by
  obtain ⟨_, address, owned, purePre⟩ := pre
  have safe : ρ "n" < 255 := purePre.1
  obtain ⟨finalState, run, result, framed, regs, callerFrame, output, stack⟩ :=
    RefinedCOwnedByte.refinedC_owned_call ρ initial (locations "p") (ρ "n") owned safe
      address frame concrete outside
  have post : incrementContract.post ρ locations finalState.mem := ⟨result, trivial⟩
  refine ⟨finalState, run, post, ?_, framed, regs, callerFrame, output, stack⟩
  apply (Contract.leanGoal_correct _ _ _ _ _ _ _).mpr
  exact fun _ => post

end Silmaril.Compile.C.Sem.RefinedCOwnedFrontend
