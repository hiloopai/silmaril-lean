module

public import Silmaril.Compiler.C.Sem.RefinedCOwnedSwap.Defs
public import Silmaril.Compiler.C.Sem.RefinedCOwnedBundleFrontend.Defs
/-! An exact two-owned-pointer frontend contract, discharged by the actual typed
Ail swap call. The ghost environment is unchanged across the call. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedSwapFrontend
open Silmaril.Cerberus.Assertion ConcreteResources
open RefinedCOwnedBundleFrontend

def swapContract : Contract :=
  { parameters := ["n", "m"]
    locations := ["p", "q"]
    cells := [⟨"p", .var "n", .var "m"⟩, ⟨"q", .var "m", .var "n"⟩]
    requires := .and (.le (.literal 0) (.var "n")) (.and (.le (.var "m") (.literal 255)) .truth)
    ensures := .and (.eq (.var "n") (.var "n")) (.and .truth .truth) }

theorem swap_pre_iff (ρ : Pure.Env) (locations : LocEnv) (args : List Int) (memory : C1.Memory) :
    swapContract.pre ρ locations args memory ↔
    args = [locations "p", locations "q"] ∧ locations "p" ≠ locations "q" ∧
    (locations "p" < 18446744073709551616 ∧ locations "q" < 18446744073709551616) ∧
    (Holds ρ ((RefinedCOwnedByte.singleton (ρ "n")).owned (locations "p") (.var "n")) memory ∧
     Holds ρ ((RefinedCOwnedByte.singleton (ρ "m")).owned (locations "q") (.var "m")) memory) ∧
    (0 ≤ ρ "n" ∧ ρ "m" ≤ 255) := by
  simp [Contract.pre, swapContract, Pure.Term.eval, Pure.Formula.holds]

/-- The generated contract's precondition yields actual execution and its post,
with an arbitrary disjoint finite concrete resource frame. -/
theorem swap_contract_call (ρ : Pure.Env) (locations : LocEnv) (args : List Int)
    (initial : C1.Env) (pre : swapContract.pre ρ locations args initial.mem)
    (frame : Resources.Heap) (concrete : Realizes initial.mem frame)
    (outsideP : ∀ n, (locations "p", n) ∉ frame)
    (outsideQ : ∀ n, (locations "q", n) ∉ frame) :
    ∃ finalState, C1.callFn RefinedCOwnedSwap.program 21 RefinedCOwnedSwap.fSym args initial =
      .ok (0, finalState) ∧ swapContract.post ρ locations finalState.mem ∧
      Realizes finalState.mem frame ∧ finalState.regs = initial.regs ∧
      finalState.frame = initial.frame ∧ finalState.out = initial.out ∧
      finalState.mem.sp = initial.mem.sp := by
  obtain ⟨argsEq, distinct, bounded, ⟨preP, preQ⟩, _⟩ := (swap_pre_iff _ _ _ _).mp pre
  obtain ⟨admitP, v, valueP, hp⟩ := (refinedC_owned_iff _ _ _ _ _).mp preP
  obtain ⟨admitQ, w, valueQ, hq⟩ := (refinedC_owned_iff _ _ _ _ _).mp preQ
  obtain ⟨finalState, run, afterP, afterQ, framed, regs, localFrame, out, sp⟩ :=
    RefinedCOwnedSwap.swap_owned initial (locations "p") (locations "q") v w hp hq distinct
      bounded.1 bounded.2 frame concrete outsideP outsideQ
  refine ⟨finalState, argsEq ▸ run, ?_, framed, regs, localFrame, out, sp⟩
  have postP : Holds ρ ((RefinedCOwnedByte.singleton (ρ "m")).owned
      (locations "p") (.var "m")) finalState.mem :=
    (refinedC_owned_iff _ _ _ _ _).mpr ⟨admitQ, w, valueQ, afterP⟩
  have postQ : Holds ρ ((RefinedCOwnedByte.singleton (ρ "n")).owned
      (locations "q") (.var "n")) finalState.mem :=
    (refinedC_owned_iff _ _ _ _ _).mpr ⟨admitP, v, valueP, afterQ⟩
  simpa [Contract.post, swapContract, Pure.Term.eval, Pure.Formula.holds] using ⟨postP, postQ⟩

def pairGhosts (v w : UInt8) : Pure.Env := fun name =>
  if name = "n" then v.toNat else if name = "m" then w.toNat else 0

def pairLocations : LocEnv := fun name => if name = "p" then C1.base else C1.base + 1

private theorem singleton_admits (n : Int) (bound : 0 ≤ n ∧ n < 256) (ρ : Pure.Env) :
    (RefinedCOwnedByte.singleton n).holds ρ n := by
  simp [RefinedCOwnedByte.singleton, RefinedC.IntRefinement.holds,
    RefinedC.IntegerType.admits, RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.signed, RefinedC.IntegerType.bits, Pure.Term.eval]
  exact bound

/-- The full contract precondition is realized by actual two-byte memory for
all 65536 input pairs, including both endpoints and equal byte values. -/
theorem pair_pre (v w : UInt8) :
    swapContract.pre (pairGhosts v w) pairLocations [C1.base, C1.base + 1] (pairMemory v w) := by
  apply (swap_pre_iff _ _ _ _).mpr
  have pValue : pairGhosts v w "n" = (v.toNat : Int) := by simp [pairGhosts]
  have qValue : pairGhosts v w "m" = (w.toNat : Int) := by simp [pairGhosts]
  refine ⟨rfl, Nat.ne_add_one _, ⟨by decide, by decide⟩, ⟨?_, ?_⟩, ?_⟩
  · apply (refinedC_owned_iff _ _ _ _ _).mpr
    refine ⟨?_, v, ?_, pair_left v w⟩
    · apply singleton_admits
      rw [pValue]
      exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr v.toNat_lt⟩
    · exact pValue
  · apply (refinedC_owned_iff _ _ _ _ _).mpr
    refine ⟨?_, w, ?_, pair_right v w⟩
    · apply singleton_admits
      rw [qValue]
      exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr w.toNat_lt⟩
    · exact qValue
  · rw [pValue, qValue]
    exact ⟨Int.natCast_nonneg _, by have := w.toNat_lt; omega⟩

end Silmaril.Compile.C.Sem.RefinedCOwnedSwapFrontend
