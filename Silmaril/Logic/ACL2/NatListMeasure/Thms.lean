module

public import Silmaril.Logic.ACL2.NatListMeasure.Defs
import Silmaril.Proofs.Logic.ACL2.NatListMeasure.Measure

@[expose] public section

namespace Silmaril.Logic.ACL2.NatListMeasure

open Ordinals Recursive

/-- ACL2's O-P-OF-NAT-LIST-MEASURE, including atoms and improper lists. -/
theorem valid (x : Encoding) : (ordinalMeasure x).oP = true :=
  Proofs.Logic.ACL2.NatListMeasure.valid x

/-- Among conses, length takes precedence over the NFIXed cars and the tails. -/
theorem lt_cons_cons (x xs y ys : Encoding) :
    lt (.cons x xs) (.cons y ys) ↔
      len xs < len ys ∨ len xs = len ys ∧ (nfix x < nfix y ∨ nfix x = nfix y ∧ lt xs ys) :=
  Proofs.Logic.ACL2.NatListMeasure.lt_cons_cons x xs y ys

/-- Any atom is below any cons. Two atoms are ordered by NFIX. -/
theorem lt_of_atom (x y : Encoding) (hx : len x = 0) :
    lt x y ↔ len y ≠ 0 ∨ nfix x < nfix y :=
  Proofs.Logic.ACL2.NatListMeasure.lt_of_atom x y hx

theorem pair_lt_iff (a b c d : Encoding) :
    lt (pair a b) (pair c d) ↔ nfix a < nfix c ∨ nfix a = nfix c ∧ nfix b < nfix d := by
  simp [pair, lt_cons_cons, len, lt_of_atom .otherAtom .otherAtom rfl, nfix]

theorem wellFounded : WellFounded lt :=
  InvImage.wf (fun x => (⟨ordinalMeasure x, valid x⟩ : ValidOrdinal)) ValidOrdinal.wellFounded

variable {S : Signature} {B : Block S} {M : Model S} {rank : OrdinalAdmission.Measure B M}

/-- Transport the proved NAT-LIST-< decreases into the default ordinal checker. -/
theorem Terminates.toOrdinal (h : Terminates B M rank) :
    OrdinalAdmission.Terminates B M (fun state => ordinalMeasure (rank state)) :=
  ⟨fun _ => valid _, h⟩

end Silmaril.Logic.ACL2.NatListMeasure
