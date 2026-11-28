module

public import Silmaril.Logic.ACL2.NatListMeasure.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.NatListMeasure

open Silmaril.Logic.ACL2.Ordinals Silmaril.Logic.ACL2.NatListMeasure

private theorem firstExpt_measure (x : Encoding) :
    (ordinalMeasure x).firstExpt = .natural (len x) := by
  cases x <;> rfl

theorem valid (x : Encoding) : (ordinalMeasure x).oP = true := by
  induction x with
  | natural | otherAtom => rfl
  | cons head tail _ ih =>
    simp [ordinalMeasure, Encoding.makeOrd, Encoding.oP, ih, firstExpt_measure, Encoding.oLt,
      Encoding.cmp, Nat.compare_eq_lt]

theorem lt_cons_cons (x xs y ys : Encoding) :
    lt (.cons x xs) (.cons y ys) ↔
      len xs < len ys ∨ len xs = len ys ∧ (nfix x < nfix y ∨ nfix x = nfix y ∧ lt xs ys) := by
  simp only [lt, ordinalMeasure, Encoding.makeOrd, Encoding.oLt, Encoding.cmp, beq_iff_eq,
    Ordering.then_eq_lt, Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.add_lt_add_iff_right,
    Nat.add_right_cancel_iff]

theorem lt_of_atom (x y : Encoding) (hx : len x = 0) :
    lt x y ↔ len y ≠ 0 ∨ nfix x < nfix y := by
  cases x <;> cases y <;> simp_all [len, lt, nfix, ordinalMeasure, Encoding.makeOrd, Encoding.oLt,
    Encoding.cmp, Nat.compare_eq_lt]

end Silmaril.Proofs.Logic.ACL2.NatListMeasure
