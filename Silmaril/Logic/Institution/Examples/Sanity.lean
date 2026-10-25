module

public import Mathlib.Data.Fin.VecNotation
public import Silmaril.Logic.Institution.Examples.Comorphisms

@[expose] public section

/-!
# Concrete satisfaction in PL, EQ and FOL

Sanity instances for the institutions of `Examples/Propositional`, `Examples/Equational` and
`Examples/FirstOrder`.

## What the headline theorems say

`PL.Formula.eval_rename`, `EQ.Equation.holds_map` and `FOL.Sentence.holds_map` are the
satisfaction conditions: a sentence translated along a signature morphism `σ` holds in a model
iff the sentence holds in the reduct of the model along `σ`. They assume nothing beyond `σ`
being a signature morphism. On their own they would also hold for a satisfaction relation that
is constantly true or constantly false; the instances below rule that out.

## What this file adds

* **PL.** Under the valuation `p ↦ True, q ↦ False` (variables `Bool`, `p = true`), `p ∧ ¬q`
  is true and `q ∧ p` is false; `eval_rename` is instantiated along the non-identity renaming
  `not : Bool → Bool`.
* **EQ.** The one-sorted signature of a binary operation and a constant (`monSig`), the
  signature of groups that extends it (`grpSig`, with a unary operation), the inclusion
  `incl : monSig ⟶ grpSig`, and the algebras `(ℤ, +, 0)` and `(ℤ, +, 0, -)`. Associativity and
  `x + 0 = x` hold; `x + y = x` fails. `holds_map` is instantiated along `incl`: associativity,
  translated to the group signature, holds in `(ℤ, +, 0, -)`.
* **FOL.** On the same carrier (as the relation-free first-order structure
  `EQtoFOL.expansion`), the group-style sentence `∀x ¬∀y ¬(x + y = 0)` (that is, `∀x ∃y`) holds
  and `∀x, x = 0` is refuted. The `EQ → FOL` comorphism (`EQtoFOL.sat`) is instantiated on the
  associativity equation.
-/

namespace Silmaril.Logic.Institution.Examples.Sanity

open CategoryTheory

/-! ### Propositional logic -/

namespace PLSanity

open PL

/-- The valuation `p ↦ True, q ↦ False`, with `p = true` and `q = false`. -/
def val : Bool → Prop := fun b => b = true

/-- `p ∧ ¬q`, with `¬q` as `q → ⊥`. -/
def pAndNotQ : Formula Bool := .and (.var true) (.imp (.var false) .bot)

/-- `q ∧ p`. -/
def qAndP : Formula Bool := .and (.var false) (.var true)

theorem eval_pAndNotQ : Formula.eval val pAndNotQ := by
  simp [Formula.eval, pAndNotQ, val]

theorem not_eval_qAndP : ¬ Formula.eval val qAndP := by
  simp [Formula.eval, qAndP, val]

/-- Renaming along `not` swaps the variables: `p ∧ ¬q` becomes `q ∧ ¬p`. -/
theorem rename_not_pAndNotQ :
    Formula.rename not pAndNotQ = .and (.var false) (.imp (.var true) .bot) := by
  rfl

/-- The satisfaction condition along the non-identity renaming `not`, on real data: the
translated sentence `q ∧ ¬p` is false under `val`, as `p ∧ ¬q` is false under the reduct
valuation `val ∘ not` (`p ↦ False, q ↦ True`). Renaming changes the truth value. -/
theorem not_eval_rename_not : ¬ Formula.eval val (Formula.rename not pAndNotQ) := by
  rw [Formula.eval_rename]
  simp [Formula.eval, pAndNotQ, val]

end PLSanity

/-! ### Equational logic -/

namespace EQSanity

/-- Operation symbols for groups: `add` (binary), `zero` (constant) and `neg` (unary). -/
inductive GrpOp : (n : ℕ) → (Fin n → Unit) → Unit → Type
  | add : GrpOp 2 (fun _ => ()) ()
  | zero : GrpOp 0 (fun _ => ()) ()
  | neg : GrpOp 1 (fun _ => ()) ()

/-- Operation symbols for monoids: `add` and `zero`. -/
inductive MonOp : (n : ℕ) → (Fin n → Unit) → Unit → Type
  | add : MonOp 2 (fun _ => ()) ()
  | zero : MonOp 0 (fun _ => ()) ()

/-- The one-sorted signature of a binary operation and a constant. -/
def monSig : EQ.Signature := ⟨Unit, MonOp⟩

/-- The one-sorted signature of groups. -/
def grpSig : EQ.Signature := ⟨Unit, GrpOp⟩

/-- The operation map of the inclusion `monSig ⟶ grpSig`. -/
def inclOp : ∀ {n : ℕ} {w : Fin n → Unit} {s : Unit}, MonOp n w s → GrpOp n w s
  | _, _, _, .add => .add
  | _, _, _, .zero => .zero

/-- The inclusion of the monoid signature in the group signature (not an identity: `neg` is not
in its image). -/
def incl : monSig ⟶ grpSig := ⟨id, fun o => inclOp o⟩

/-- `(ℤ, +, 0, -)`. -/
def intGrpOp : ∀ {n : ℕ} {w : Fin n → Unit} {s : Unit}, GrpOp n w s → (Fin n → ℤ) → ℤ
  | _, _, _, .add, a => a 0 + a 1
  | _, _, _, .zero, _ => 0
  | _, _, _, .neg, a => -a 0

/-- `(ℤ, +, 0)`. -/
def intMonOp : ∀ {n : ℕ} {w : Fin n → Unit} {s : Unit}, MonOp n w s → (Fin n → ℤ) → ℤ
  | _, _, _, .add, a => a 0 + a 1
  | _, _, _, .zero, _ => 0

/-- The integers as a group-signature algebra. -/
def intGrp : EQ.Algebra grpSig := ⟨fun _ => ℤ, fun o a => intGrpOp o a⟩

/-- The integers as a monoid-signature algebra. -/
def intMon : EQ.Algebra monSig := ⟨fun _ => ℤ, fun o a => intMonOp o a⟩

/-- The context of `k` variables of the only sort. -/
def ctx (k : ℕ) : Fin k → monSig.S := fun _ => ()

/-- `x + y` as a term. -/
def add {k : ℕ} (t u : EQ.Term monSig (ctx k) ()) : EQ.Term monSig (ctx k) () :=
  .app MonOp.add ![t, u]

/-- `0` as a term. -/
def zero {k : ℕ} : EQ.Term monSig (ctx k) () := .app MonOp.zero ![]

/-- Variable `i` as a term. -/
def v {k : ℕ} (i : Fin k) : EQ.Term monSig (ctx k) () := .var i

/-- Associativity, `(x + y) + z = x + (y + z)`. -/
def assoc : EQ.Equation monSig :=
  ⟨3, ctx 3, (), add (add (v 0) (v 1)) (v 2), add (v 0) (add (v 1) (v 2))⟩

/-- Right unit, `x + 0 = x`. -/
def addZero : EQ.Equation monSig := ⟨1, ctx 1, (), add (v 0) zero, v 0⟩

/-- `x + y = x`, false in `ℤ`. -/
def addLeft : EQ.Equation monSig := ⟨2, ctx 2, (), add (v 0) (v 1), v 0⟩

theorem holds_assoc : assoc.Holds intMon := by
  intro ρ
  simp only [assoc, add, v, EQ.Term.eval, intMon, intMonOp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact Int.add_assoc _ _ _

theorem holds_addZero : addZero.Holds intMon := by
  intro ρ
  simp only [addZero, add, zero, v, EQ.Term.eval, intMon, intMonOp]
  exact Int.add_zero _

theorem not_holds_addLeft : ¬ addLeft.Holds intMon := by
  intro h
  -- Counterexample `x = 1`, `y = 1`: `1 + 1 ≠ 1`.
  have h11 := h fun _ => (1 : ℤ)
  simp [addLeft, add, v, EQ.Term.eval, intMon, intMonOp] at h11

/-- The reduct of `(ℤ, +, 0, -)` along the inclusion is `(ℤ, +, 0)`. -/
theorem reduct_intGrp : (EQ.Algebra.reduct incl).obj intGrp = intMon := by
  have h : @Eq (∀ {n : ℕ} {w : Fin n → Unit} {s : Unit}, MonOp n w s → (Fin n → ℤ) → ℤ)
      (fun o args => intGrpOp (inclOp o) args) (fun o args => intMonOp o args) := by
    funext n w s o args
    cases o <;> rfl
  exact congrArg (EQ.Algebra.mk (Sg := monSig) (fun _ => ℤ)) h

/-- The satisfaction condition along `incl`, on real data: associativity translated to the
group signature holds in `(ℤ, +, 0, -)`, obtained from `holds_map` and `holds_assoc`. -/
theorem holds_assoc_map : (assoc.map incl).Holds intGrp := by
  rw [EQ.Equation.holds_map, reduct_intGrp]
  exact holds_assoc

/-- The same along `incl` for the failing equation: its translation fails in `(ℤ, +, 0, -)`. -/
theorem not_holds_addLeft_map : ¬ (addLeft.map incl).Holds intGrp := by
  rw [EQ.Equation.holds_map, reduct_intGrp]
  exact not_holds_addLeft

end EQSanity

/-! ### First-order logic -/

namespace FOLSanity

open EQSanity

/-- The relation-free first-order signature of groups (`EQ → FOL` on signatures). -/
abbrev sig : FOL.Signature := EQtoFOL.sig grpSig

/-- `(ℤ, +, 0, -)` as a first-order structure. -/
def intStr : FOL.Structure sig := EQtoFOL.expansion intGrp

/-- The context of `k` variables. -/
def gctx (k : ℕ) : Fin k → sig.S := fun _ => ()

/-- `x + y` over the group signature. -/
def gadd {k : ℕ} (t u : EQ.Term sig.toSignature (gctx k) ()) : EQ.Term sig.toSignature (gctx k) () :=
  .app GrpOp.add ![t, u]

/-- `0` over the group signature. -/
def gzero {k : ℕ} : EQ.Term sig.toSignature (gctx k) () := .app GrpOp.zero ![]

/-- Variable `i` over the group signature. -/
def gv {k : ℕ} (i : Fin k) : EQ.Term sig.toSignature (gctx k) () := .var i

theorem gctx_succ (k : ℕ) : gctx (k + 1) ∘ Fin.succ = gctx k := rfl

/-- `∀x ∃y, x + y = 0`, with `∃` as `¬∀¬`. In the innermost context, variable `0` is `y` and
variable `1` is `x`. -/
def rightInverse : FOL.Sentence sig :=
  ⟨gctx 0, .all (gctx_succ 0) (.not (.all (gctx_succ 1) (.not (.eq (gadd (gv 1) (gv 0)) gzero))))⟩

/-- `∀x, x = 0`. -/
def allZero : FOL.Sentence sig := ⟨gctx 0, .all (gctx_succ 0) (.eq (gv 0) gzero)⟩

theorem holds_rightInverse : rightInverse.Holds intStr := by
  intro ρ _ h
  -- Witness `y = -x`.
  let x : ℤ := ρ 0
  refine h (![-x, x] : Fin 2 → ℤ) (fun i => ?_) ?_
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact HEq.rfl
  · show x + -x = 0
    omega

theorem not_holds_allZero : ¬ allZero.Holds intStr := by
  intro h
  -- Counterexample `x = 1`.
  have h1 : (1 : ℤ) = 0 := h (fun _ => (1 : ℤ)) (fun i => i.elim0)
  exact absurd h1 (by decide)

/-- The `EQ → FOL` comorphism on real data: the universal closure of associativity holds in the
relation-free structure on `(ℤ, +, 0)`, by `EQtoFOL.sat`. -/
theorem holds_sen_assoc : (EQtoFOL.sen assoc).Holds (EQtoFOL.expansion intMon) := by
  exact (EQtoFOL.sat _ assoc).mpr holds_assoc

end FOLSanity

end Silmaril.Logic.Institution.Examples.Sanity
