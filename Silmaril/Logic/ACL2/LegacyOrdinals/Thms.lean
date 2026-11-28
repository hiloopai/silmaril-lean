module

public import Silmaril.Logic.ACL2.LegacyOrdinals.Defs
import Silmaril.Logic.ACL2.Recursive.Thms
import Silmaril.Proofs.Logic.ACL2.LegacyOrdinals.Correspondence

@[expose] public section

namespace Silmaril.Logic.ACL2.LegacyOrdinals

open Ordinals Recursive

/-- ATOC takes every E0-ORDINALP value to an O-P value. -/
theorem ordinal_valid (x : Encoding) (h : valid x = true) : (ordinalMeasure x).oP = true :=
  Proofs.Logic.ACL2.LegacyOrdinals.ordinal_valid x h

/-- The Lean counterpart to ACL2 ATOC-<-EQUIV. -/
theorem lt_iff (x y : Encoding) (hx : valid x = true) (hy : valid y = true) :
    lt x y ↔ (ordinalMeasure x).oLt (ordinalMeasure y) = true :=
  Proofs.Logic.ACL2.LegacyOrdinals.lt_iff x y hx hy

theorem cmp_eq_eq (x y : Encoding) (hx : valid x = true) (hy : valid y = true) :
    cmp x y = .eq ↔ x = y :=
  Proofs.Logic.ACL2.LegacyOrdinals.cmp_eq_eq x y hx hy

/-- The comparison continues at the cdr exactly when the valid cars are equal. -/
theorem lt_cons_cons (e r f s : Encoding) (he : valid e = true) (hf : valid f = true) :
    lt (.cons e r) (.cons f s) ↔ lt e f ∨ e = f ∧ lt r s := by
  simp only [lt, cmp, Ordering.then_eq_lt, cmp_eq_eq e f he hf]

/-- E0-ORD-< is well-founded on the domain recognized by E0-ORDINALP. -/
theorem wellFounded : WellFounded (fun x y : {x : Encoding // valid x = true} => lt x.val y.val) :=
  let rank (x : {v : Encoding // valid v = true}) : ValidOrdinal :=
    ⟨ordinalMeasure x.val, ordinal_valid x.val x.property⟩
  Subrelation.wf (fun {a b} h => (lt_iff a.val b.val a.property b.property).1 h)
    (InvImage.wf rank ValidOrdinal.wellFounded)

variable {S : Signature} {B : Block S} {M : Model S} {rank : OrdinalAdmission.Measure B M}

theorem Terminates.toOrdinal (h : Terminates B M rank) :
    OrdinalAdmission.Terminates B M (fun state => ordinalMeasure (rank state)) :=
  ⟨fun _ => ordinal_valid _ (h.valid _),
    fun state => (h.decreases state).mono fun next hn =>
      (lt_iff _ _ (h.valid next) (h.valid state)).1 hn⟩

end Silmaril.Logic.ACL2.LegacyOrdinals
