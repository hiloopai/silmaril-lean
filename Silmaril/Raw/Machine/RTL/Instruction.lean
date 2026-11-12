module

public import Silmaril.Raw.Machine.RTL.Syntax
public import Silmaril.SSA.Isotope.Thms

/-!
# RTL's operators as a lambda-SSA instruction signature

`LambdaSSA` is parameterised by an abstract opcode type with a source type, a
target type, an effect and an atomic transition relation. `Opcode` is the
instance that makes RTL and lambda-SSA the same language: one base type, the
64-bit word, with multi-operand and multi-result opcodes using right-nested
products terminated by `unit`, exactly as `MLIR/ToLambdaSSA.lean` does.

Three points deserve emphasis.

* **Partiality is stuckness on both sides.** `Lir.Binop.eval` is `none` on
  division by zero, `Lir.Memory.load` is `none` out of bounds. `step` simply has
  no transition there, which is lambda-SSA's stuckness and RTL's stuckness, so
  the two agree on the nose: neither side needs an error value.
* **`move` is an opcode.** A register copy is the identity on values and on
  memory, but it is still an instruction: giving it an opcode is what makes the
  translation of an op list and the list itself the same length, so that every
  op contributes exactly one binder.
* **A call is atomic here and is not atomic in RTL.** Lambda-SSA instructions are
  single relational steps, while `RTL.SSA.step` pushes an activation and runs the
  callee. The gap is bridged by making the meaning of a call a parameter: a
  `CallOracle` relating a callee, its arguments and the memory to its results and
  the final memory. `Machine/RTL/BigStep.lean` supplies the oracle a program
  induces and relates it to the small-step machine.

The branch opcode `test` is the one piece RTL's `cond` needs and lambda-SSA does
not have primitively: it turns a word into `unit + unit`, nonzero on the left, so
that `Term.cond` becomes `Region.case`.
-/

@[expose] public section

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Isotope (Value)

/-! ## Types -/

/-- The one base type of RTL seen as a lambda-SSA type code: the 64-bit word. -/
abbrev Ty : Type := Silmaril.Ty Unit

/-- The 64-bit word type. -/
abbrev wordTy : Ty := .base ()

/-- A tuple of `n` words, as a right-nested product terminated by `unit`. This
is the packing convention of `MLIR/ToLambdaSSA.lean`, used here for operand
lists, result lists, block parameter lists and returned values alike. -/
def packTy : Nat → Ty
  | 0 => .unit
  | n + 1 => .product wordTy (packTy n)

@[simp] theorem packTy_zero : packTy 0 = .unit := rfl

@[simp] theorem packTy_succ (n : Nat) : packTy (n + 1) = .product wordTy (packTy n) := rfl

/-- A tuple of words as a runtime value, matching `packTy`. -/
def packValues : List Word → Value Word
  | [] => .unit
  | w :: ws => .pair (.atom w) (packValues ws)

@[simp] theorem packValues_nil : packValues [] = .unit := rfl

@[simp] theorem packValues_cons (w : Word) (ws : List Word) :
    packValues (w :: ws) = .pair (.atom w) (packValues ws) := rfl

/-- Distinct word lists pack to distinct values. -/
theorem packValues_injective : Function.Injective packValues := by
  intro xs ys h
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp [packValues] at h
  | cons x xs ih => cases ys with
    | nil => simp [packValues] at h
    | cons y ys =>
      simp only [packValues_cons, Isotope.Value.pair.injEq, Isotope.Value.atom.injEq] at h
      rw [h.1, ih h.2]

/-! ## Effects -/

/-- The two-element effect lattice of RTL: a computation either leaves memory
and the call stack alone or it does not. -/
inductive Eff where
  | pure
  | impure
  deriving DecidableEq, Repr

/-! ## Opcodes -/

/-- The opcodes of RTL, as a lambda-SSA instruction signature. `sigs` is the
program's function table, so that a call opcode knows its arity. -/
inductive Opcode (sigs : List Signature) where
  | const (value : Lir.Word)
  | move
  | unary (op : Lir.Unop)
  | binary (op : Lir.Binop)
  | load (width : Lir.Width) (ext : Lir.Ext) (offset : Nat)
  | store (width : Lir.Width) (offset : Nat)
  | call (callee : FuncId)
  | test
  deriving DecidableEq, Repr

variable {sigs : List Signature}

/-- The signature of a function identifier, defaulting to the empty signature at
an identifier outside the table. -/
def sigAt (sigs : List Signature) (f : FuncId) : Signature := sigs[f]?.getD ⟨0, 0⟩

namespace Opcode

/-- The number of operands an opcode consumes. -/
def arity : Opcode sigs → Nat
  | .const _ => 0
  | .move | .unary _ | .load .. | .test => 1
  | .binary _ | .store .. => 2
  | .call f => (sigAt sigs f).params

/-- The number of results an opcode produces; `test` is the exception, since it
produces a coproduct rather than a tuple. -/
def results : Opcode sigs → Nat
  | .const _ | .move | .unary _ | .binary _ | .load .. => 1
  | .store .. => 0
  | .call f => (sigAt sigs f).results
  | .test => 0

end Opcode

/-- Operands are a packed tuple; results are a packed tuple, except that `test`
produces the coproduct `unit + unit` that `Region.case` eliminates. -/
instance : Silmaril.HasTy (Opcode sigs) Ty where
  src o := packTy o.arity
  trg
    | .test => .coprod .unit .unit
    | o => packTy o.results

/-- Arithmetic and the branch test are pure; memory access and calls are not. -/
instance : Silmaril.HasEff (Opcode sigs) Eff where
  eff
    | .const _ | .move | .unary _ | .binary _ | .test => .pure
    | .load .. | .store .. | .call _ => .impure

instance : Silmaril.Signature (Opcode sigs) Ty Eff where

@[simp] theorem instrSrc_eq (o : Opcode sigs) :
    Silmaril.instrSrc (τ := Ty) o = packTy o.arity := rfl

@[simp] theorem instrTrg_test :
    Silmaril.instrTrg (τ := Ty) (Opcode.test (sigs := sigs)) = .coprod .unit .unit := rfl

theorem instrTrg_eq {o : Opcode sigs} (h : o ≠ .test) :
    Silmaril.instrTrg (τ := Ty) o = packTy o.results := by
  cases o <;> first | rfl | exact absurd rfl h

/-! ## Transitions -/

/-- What a call may do: run `callee` on a list of argument words in a memory and
produce a list of result words and a final memory. A lambda-SSA instruction is a
single atomic relation, so the meaning of a call is supplied from outside rather
than unfolded here. -/
abbrev CallOracle := FuncId → List Word → Memory → List Word → Memory → Prop

/-- The atomic transitions of RTL's opcodes. Every partiality of `Lir` — division
by zero, signed division overflow, an out-of-bounds access — is the *absence* of
a transition, which is exactly what makes a stuck lambda-SSA region and a stuck
RTL state the same thing. -/
inductive Opcode.step (oracle : CallOracle) :
    Opcode sigs → Value Word → Memory → Value Word → Memory → Prop where
  | const {value : Word} {m : Memory} :
      step oracle (.const value) (packValues []) m (packValues [value]) m
  | move {x : Word} {m : Memory} :
      step oracle (Opcode.move (sigs := sigs)) (packValues [x]) m (packValues [x]) m
  | unary {op : Lir.Unop} {x : Word} {m : Memory} :
      step oracle (.unary op) (packValues [x]) m (packValues [op.eval x]) m
  | binary {op : Lir.Binop} {x y z : Word} {m : Memory} :
      op.eval x y = some z →
      step oracle (.binary op) (packValues [x, y]) m (packValues [z]) m
  | load {w : Lir.Width} {e : Lir.Ext} {off : Nat} {a z : Word} {m : Memory} :
      m.load w e (a.toNat + off) = some z →
      step oracle (.load w e off) (packValues [a]) m (packValues [z]) m
  | store {w : Lir.Width} {off : Nat} {a x : Word} {m m' : Memory} :
      m.store w (a.toNat + off) x = some m' →
      step oracle (.store w off) (packValues [a, x]) m (packValues []) m'
  | call {f : FuncId} {args results : List Word} {m m' : Memory} :
      oracle f args m results m' →
      step oracle (.call f) (packValues args) m (packValues results) m'
  | test_nonzero {x : Word} {m : Memory} : x ≠ 0 →
      step oracle (Opcode.test (sigs := sigs)) (packValues [x]) m (.inl .unit) m
  | test_zero {m : Memory} :
      step oracle (Opcode.test (sigs := sigs)) (packValues [0]) m (.inr .unit) m

/-- Which calls run forever. Lambda-SSA's `Semantics.External.Diverges` takes a
predicate naming the primitive computations that diverge; in RTL only a call can.
-/
abbrev DivOracle := FuncId → List Word → Memory → Prop

/-- The divergent primitives of RTL, as `Semantics.External.Diverges` expects
them: a call whose callee runs forever, and nothing else. -/
inductive Opcode.divergent (div : DivOracle) : Opcode sigs → Value Word → Memory → Prop where
  | call {f : FuncId} {args : List Word} {m : Memory} : div f args m →
      divergent div (.call f) (packValues args) m

/-- A call oracle is deterministic when a callee, its arguments and the initial
memory determine its results and the final memory. -/
def CallOracle.Deterministic (oracle : CallOracle) : Prop :=
  ∀ f args m vs₁ m₁ vs₂ m₂, oracle f args m vs₁ m₁ → oracle f args m vs₂ m₂ →
    vs₁ = vs₂ ∧ m₁ = m₂

/-- A call transition is exactly an oracle transition on packed arguments and
packed results. `packValues` is not constructor-headed at a variable list, so
this inversion is what case analysis on a call step has to go through. -/
theorem Opcode.step_call_iff {oracle : CallOracle} {f : FuncId} {x y : Value Word}
    {m m' : Memory} :
    Opcode.step (sigs := sigs) oracle (.call f) x m y m' ↔
      ∃ args results, x = packValues args ∧ y = packValues results ∧ oracle f args m results m' := by
  constructor
  · intro hstep
    cases hstep with | call hc => exact ⟨_, _, rfl, rfl, hc⟩
  · rintro ⟨args, results, rfl, rfl, hc⟩
    exact .call hc

/-- **The opcodes are deterministic** whenever their call oracle is. -/
theorem Opcode.step_deterministic {oracle : CallOracle} (h : oracle.Deterministic) :
    Isotope.LambdaSSA.Semantics.InstrDeterministic (Opcode.step (sigs := sigs) oracle) := by
  intro f a s b s' c s'' one two
  cases one with
  | const => cases two; exact ⟨rfl, rfl⟩
  | move => cases two; exact ⟨rfl, rfl⟩
  | unary => cases two; exact ⟨rfl, rfl⟩
  | binary h₁ =>
    cases two with
    | binary h₂ => obtain rfl := Option.some.inj (h₁.symm.trans h₂); exact ⟨rfl, rfl⟩
  | load h₁ =>
    cases two with
    | load h₂ => obtain rfl := Option.some.inj (h₁.symm.trans h₂); exact ⟨rfl, rfl⟩
  | store h₁ =>
    cases two with
    | store h₂ => obtain rfl := Option.some.inj (h₁.symm.trans h₂); exact ⟨rfl, rfl⟩
  | call h₁ =>
    obtain ⟨args₂, res₂, heq, rfl, h₂⟩ := Opcode.step_call_iff.mp two
    obtain rfl := packValues_injective heq
    obtain ⟨rfl, rfl⟩ := h _ _ _ _ _ _ _ h₁ h₂
    exact ⟨rfl, rfl⟩
  | test_nonzero hx =>
    cases two with
    | test_nonzero => exact ⟨rfl, rfl⟩
    | test_zero => exact absurd rfl hx
  | test_zero =>
    cases two with
    | test_nonzero hx => exact absurd rfl hx
    | test_zero => exact ⟨rfl, rfl⟩

/-- A pure opcode leaves memory alone. -/
theorem Opcode.step_pure {oracle : CallOracle} {o : Opcode sigs}
    {x y : Value Word} {m m' : Memory} (hpure : Silmaril.instrEff (ε := Eff) o = .pure)
    (hstep : Opcode.step oracle o x m y m') : m = m' := by
  cases hstep <;> first | rfl | simp [Silmaril.instrEff, HasEff.eff] at hpure

/-- The branch test never diverges from its specification: on a word it produces
the left injection exactly when the word is nonzero. -/
theorem Opcode.step_test_iff {oracle : CallOracle} {x : Word} {y : Value Word} {m m' : Memory} :
    Opcode.step (sigs := sigs) oracle .test (packValues [x]) m y m' ↔
      m' = m ∧ y = (if x = 0 then .inr .unit else .inl .unit) := by
  constructor
  · intro hstep
    cases hstep with
    | test_nonzero hx =>
      refine ⟨rfl, ?_⟩
      split
      · rename_i h0
        exact absurd h0 hx
      · rfl
    | test_zero =>
      refine ⟨rfl, ?_⟩
      split
      · rfl
      · rename_i h0
        exact absurd rfl h0
  · rintro ⟨rfl, rfl⟩
    split
    · rename_i h0
      subst h0
      exact .test_zero
    · rename_i h0
      exact .test_nonzero h0

end Silmaril.Machine.RTL
