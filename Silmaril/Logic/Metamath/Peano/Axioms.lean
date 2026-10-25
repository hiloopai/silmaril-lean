module

public import Silmaril.Logic.Metamath.Peano.Language

@[expose] public section

/-!
# The axioms of `peano.mm`

Every `$a` statement of `peano.mm` that is not a syntax axiom, transcribed as
a tree assertion with the mandatory hypotheses in database order (floating
hypotheses first, in the order of their `$f` statements, then the essential
hypotheses) and the disjoint-variable conditions of its block:

* propositional logic: `ax-1`, `ax-2`, `ax-3`, `ax-mp`, and the definitions
  `bi1`, `bi2`, `bi3`, `df-an`, `df-or` of `iff`, `and` and `or`;
* equality: `eq-refl`, `eq-sym`, `eq-trans`, `eq-congr` (for any binary
  predicate), `eq-suc`, `eq-binop` (for any binary operation);
* quantifiers: the alpha-conversion rules `alpha_1`, `alpha_2`, `alpha_3`, the
  forall-elimination axioms `all_elim`, `all_elim2`, `all_elim3`, and the
  definition `exists_def` of `exists`;
* arithmetic: `pa_ax1` to `pa_ax7` and the induction scheme `induction`.

`PA` is the set of these 30 axioms. Each is well formed (`wellFormed_PA`,
checked by evaluation).
-/

namespace Silmaril.Logic.Metamath.Peano

open Silmaril.Logic.Metamath Grammar T

/-- A floating hypothesis `term v`. -/
abbrev ft (a : V) : THyp L C V := .float .term a
/-- A floating hypothesis `var v`. -/
abbrev fv (a : V) : THyp L C V := .float .var a
/-- A floating hypothesis `wff v`. -/
abbrev fw (a : V) : THyp L C V := .float .wff a

open V

/-- `ax-1`: `|- implies phi implies psi phi`. -/
def ax1 : TAssertion L C V := ⟨[], [fw phi, fw psi], pf (imp (mv phi) (imp (mv psi) (mv phi)))⟩

/-- `ax-2`: `|- implies implies phi implies psi chi implies implies phi psi implies phi chi`. -/
def ax2 : TAssertion L C V := ⟨[], [fw phi, fw psi, fw chi],
  pf (imp (imp (mv phi) (imp (mv psi) (mv chi)))
    (imp (imp (mv phi) (mv psi)) (imp (mv phi) (mv chi))))⟩

/-- `ax-3`: `|- implies implies not phi not psi implies psi phi`. -/
def ax3 : TAssertion L C V := ⟨[], [fw phi, fw psi],
  pf (imp (imp (not (mv phi)) (not (mv psi))) (imp (mv psi) (mv phi)))⟩

/-- `ax-mp`: from `|- phi` and `|- implies phi psi` infer `|- psi`. -/
def axMp : TAssertion L C V :=
  ⟨[], [fw phi, fw psi, .ess (pf (mv phi)), .ess (pf (imp (mv phi) (mv psi)))], pf (mv psi)⟩

/-- `bi1`: `|- implies iff phi psi implies phi psi`. -/
def bi1 : TAssertion L C V := ⟨[], [fw phi, fw psi],
  pf (imp (iff (mv phi) (mv psi)) (imp (mv phi) (mv psi)))⟩

/-- `bi2`: `|- implies iff phi psi implies psi phi`. -/
def bi2 : TAssertion L C V := ⟨[], [fw phi, fw psi],
  pf (imp (iff (mv phi) (mv psi)) (imp (mv psi) (mv phi)))⟩

/-- `bi3`: `|- implies implies phi psi implies implies psi phi iff phi psi`. -/
def bi3 : TAssertion L C V := ⟨[], [fw phi, fw psi],
  pf (imp (imp (mv phi) (mv psi)) (imp (imp (mv psi) (mv phi)) (iff (mv phi) (mv psi))))⟩

/-- `df-an`: `|- iff and phi psi not implies phi not psi`. -/
def dfAn : TAssertion L C V := ⟨[], [fw phi, fw psi],
  pf (iff (and (mv phi) (mv psi)) (not (imp (mv phi) (not (mv psi)))))⟩

/-- `df-or`: `|- iff or phi psi implies not phi psi`. -/
def dfOr : TAssertion L C V := ⟨[], [fw phi, fw psi],
  pf (iff (or (mv phi) (mv psi)) (imp (not (mv phi)) (mv psi)))⟩

/-- `eq-refl`: `|- = t t`. -/
def eqRefl : TAssertion L C V := ⟨[], [ft t], pf (eq (mv t) (mv t))⟩

/-- `eq-sym`: `|- implies = s t = t s`. -/
def eqSym : TAssertion L C V := ⟨[], [ft s, ft t],
  pf (imp (eq (mv s) (mv t)) (eq (mv t) (mv s)))⟩

/-- `eq-trans`: `|- implies and = s t = t u = s u`. -/
def eqTrans : TAssertion L C V := ⟨[], [ft s, ft t, ft u],
  pf (imp (and (eq (mv s) (mv t)) (eq (mv t) (mv u))) (eq (mv s) (mv u)))⟩

/-- `eq-congr`: `|- implies and = s0 s1 = t0 t1 iff binpred s0 t0 binpred s1 t1`. -/
def eqCongr : TAssertion L C V := ⟨[], [ft s0, ft s1, ft t0, ft t1, .float .binpred binpred],
  pf (imp (and (eq (mv s0) (mv s1)) (eq (mv t0) (mv t1)))
    (iff (atom (mv binpred) (mv s0) (mv t0)) (atom (mv binpred) (mv s1) (mv t1))))⟩

/-- `eq-suc`: `|- implies = s t = S s S t`. -/
def eqSuc : TAssertion L C V := ⟨[], [ft s, ft t],
  pf (imp (eq (mv s) (mv t)) (eq (succ (mv s)) (succ (mv t))))⟩

/-- `eq-binop`: `|- implies and = s0 s1 = t0 t1 = binop s0 t0 binop s1 t1`. -/
def eqBinop : TAssertion L C V := ⟨[], [ft s0, ft s1, ft t0, ft t1, .float .binop binop],
  pf (imp (and (eq (mv s0) (mv s1)) (eq (mv t0) (mv t1)))
    (eq (bin (mv binop) (mv s0) (mv t0)) (bin (mv binop) (mv s1) (mv t1))))⟩

/-- `alpha_1`, with `$d phi x`: from `|- implies phi iff psi chi` infer
`|- implies phi iff quant x psi quant x chi`. -/
def alpha1 : TAssertion L C V := ⟨[(phi, x)],
  [fv x, .float .quant quant, fw phi, fw psi, fw chi,
    .ess (pf (imp (mv phi) (iff (mv psi) (mv chi))))],
  pf (imp (mv phi) (iff (qnt (mv quant) x (mv psi)) (qnt (mv quant) x (mv chi))))⟩

/-- `alpha_2`, with `$d phi x`: from `|- implies phi chi` infer
`|- implies phi forall x chi`. -/
def alpha2 : TAssertion L C V := ⟨[(phi, x)],
  [fv x, fw phi, fw chi, .ess (pf (imp (mv phi) (mv chi)))],
  pf (imp (mv phi) (all x (mv chi)))⟩

/-- `alpha_3`, with `$d phi y`, `$d psi x`, `$d x y`:
`|- implies forall x forall y implies = x y iff phi psi iff quant x phi quant y psi`. -/
def alpha3 : TAssertion L C V := ⟨[(phi, y), (psi, x), (x, y)],
  [fv x, fv y, .float .quant quant, fw phi, fw psi],
  pf (imp (all x (all y (imp (eq (tv x) (tv y)) (iff (mv phi) (mv psi)))))
    (iff (qnt (mv quant) x (mv phi)) (qnt (mv quant) y (mv psi))))⟩

/-- `all_elim`, with `$d x t`: `|- implies forall x phi forall x implies = x t phi`. -/
def allElim : TAssertion L C V := ⟨[(x, t)], [ft t, fv x, fw phi],
  pf (imp (all x (mv phi)) (all x (imp (eq (tv x) (mv t)) (mv phi))))⟩

/-- `all_elim2`, with `$d x y`, `$d y t`: from `|- implies = x t iff phi chi`
infer `|- implies = x t iff quant y phi quant y chi`. -/
def allElim2 : TAssertion L C V := ⟨[(x, y), (y, t)],
  [ft t, fv x, fv y, .float .quant quant, fw phi, fw chi,
    .ess (pf (imp (eq (tv x) (mv t)) (iff (mv phi) (mv chi))))],
  pf (imp (eq (tv x) (mv t)) (iff (qnt (mv quant) y (mv phi)) (qnt (mv quant) y (mv chi))))⟩

/-- `all_elim3`, with `$d x chi`, `$d x t`: from `|- implies = x t iff phi chi`
infer `|- implies forall x implies = x t phi chi`. -/
def allElim3 : TAssertion L C V := ⟨[(x, chi), (x, t)],
  [ft t, fv x, fw phi, fw chi, .ess (pf (imp (eq (tv x) (mv t)) (iff (mv phi) (mv chi))))],
  pf (imp (all x (imp (eq (tv x) (mv t)) (mv phi))) (mv chi))⟩

/-- `exists_def`: `|- iff exists x phi not forall x not phi`. -/
def existsDef : TAssertion L C V := ⟨[], [fv x, fw phi],
  pf (iff (ex x (mv phi)) (not (all x (not (mv phi)))))⟩

/-- `pa_ax1`: `|- not = 0 S x`. -/
def paAx1 : TAssertion L C V := ⟨[], [fv x], pf (not (eq zero (succ (tv x))))⟩

/-- `pa_ax2`: `|- implies = S x S y = x y`. -/
def paAx2 : TAssertion L C V := ⟨[], [fv x, fv y],
  pf (imp (eq (succ (tv x)) (succ (tv y))) (eq (tv x) (tv y)))⟩

/-- `pa_ax3`: `|- = x + x 0`. -/
def paAx3 : TAssertion L C V := ⟨[], [fv x], pf (eq (tv x) (plus (tv x) zero))⟩

/-- `pa_ax4`: `|- = S + x y + x S y`. -/
def paAx4 : TAssertion L C V := ⟨[], [fv x, fv y],
  pf (eq (succ (plus (tv x) (tv y))) (plus (tv x) (succ (tv y))))⟩

/-- `pa_ax5`: `|- = 0 * x 0`. -/
def paAx5 : TAssertion L C V := ⟨[], [fv x], pf (eq zero (times (tv x) zero))⟩

/-- `pa_ax6`: `|- = + * x y x * x S y`. -/
def paAx6 : TAssertion L C V := ⟨[], [fv x, fv y],
  pf (eq (plus (times (tv x) (tv y)) (tv x)) (times (tv x) (succ (tv y))))⟩

/-- `pa_ax7`, with `$d z x`, `$d z y`: `|- iff < x y exists z = y + x S z`. -/
def paAx7 : TAssertion L C V := ⟨[(z, x), (z, y)], [fv x, fv y, fv z],
  pf (iff (lt (tv x) (tv y)) (ex z (eq (tv y) (plus (tv x) (succ (tv z))))))⟩

/-- `induction`, with `$d phi x`, `$d x y`: `|- implies and forall y implies = y 0 phi
forall x implies forall y implies = y x phi forall y implies = y S x phi
forall x forall y implies = y x phi`. -/
def induction : TAssertion L C V := ⟨[(phi, x), (x, y)], [fv x, fv y, fw phi],
  pf (imp (and (all y (imp (eq (tv y) zero) (mv phi)))
      (all x (imp (all y (imp (eq (tv y) (tv x)) (mv phi)))
        (all y (imp (eq (tv y) (succ (tv x))) (mv phi))))))
    (all x (all y (imp (eq (tv y) (tv x)) (mv phi)))))⟩

/-- The axioms of `peano.mm`, with their labels, in database order. -/
def axiomList : List (String × TAssertion L C V) :=
  [("ax-1", ax1), ("ax-2", ax2), ("ax-3", ax3), ("ax-mp", axMp), ("bi1", bi1), ("bi2", bi2),
    ("bi3", bi3), ("df-an", dfAn), ("df-or", dfOr), ("eq-refl", eqRefl), ("eq-sym", eqSym),
    ("eq-trans", eqTrans), ("eq-congr", eqCongr), ("eq-suc", eqSuc), ("eq-binop", eqBinop),
    ("alpha_1", alpha1), ("alpha_2", alpha2), ("alpha_3", alpha3), ("all_elim", allElim),
    ("all_elim2", allElim2), ("all_elim3", allElim3), ("exists_def", existsDef),
    ("pa_ax1", paAx1), ("pa_ax2", paAx2), ("pa_ax3", paAx3), ("pa_ax4", paAx4),
    ("pa_ax5", paAx5), ("pa_ax6", paAx6), ("pa_ax7", paAx7), ("induction", induction)]

/-- Peano arithmetic as axiomatized by `peano.mm`. -/
def PA : Set (TAssertion L C V) := {A | ∃ p ∈ axiomList, p.2 = A}

theorem mem_PA {A : TAssertion L C V} : A ∈ PA ↔ A ∈ axiomList.map Prod.snd := by
  simp [PA, eq_comm]

theorem wellFormed_PA : ∀ B ∈ PA, B.WellFormed grammar := by
  intro B hB
  rw [mem_PA] at hB
  have h : ∀ B ∈ axiomList.map Prod.snd, TAssertion.checkWF grammar B = true := by decide
  exact .of_checkWF (h B hB)

end Silmaril.Logic.Metamath.Peano
