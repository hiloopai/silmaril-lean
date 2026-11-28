module

public import Silmaril.Logic.ACL2.Ordinals.Defs
import Silmaril.Proofs.Logic.ACL2.Ordinals.Correspondence

@[expose] public section

namespace Silmaril.Logic.ACL2.Ordinals

theorem Encoding.oP_iff (x : Encoding) : x.oP = true ↔ ∃ n : ONote, n.NF ∧ ofNote n = x :=
  ⟨fun h => ⟨ValidOrdinal.toNote ⟨x, h⟩, Proofs.Logic.ACL2.Ordinals.toNote_nf ⟨x, h⟩,
      Proofs.Logic.ACL2.Ordinals.ofNote_toNote ⟨x, h⟩⟩,
    fun ⟨_, hn, he⟩ => he ▸ Proofs.Logic.ACL2.Ordinals.oP_ofNote hn⟩

theorem Encoding.oP_ofNote {x : ONote} (h : x.NF) : (Encoding.ofNote x).oP = true :=
  Proofs.Logic.ACL2.Ordinals.oP_ofNote h

theorem ValidOrdinal.ofNote_toNote (x : ValidOrdinal) : Encoding.ofNote x.toNote = x.val :=
  Proofs.Logic.ACL2.Ordinals.ofNote_toNote x

theorem ValidOrdinal.toNote_ofNote (x : ONote) (h : x.NF) :
    (ValidOrdinal.toNote ⟨Encoding.ofNote x, Encoding.oP_ofNote h⟩) = x :=
  Proofs.Logic.ACL2.Ordinals.toNote_ofNote x h

theorem ValidOrdinal.lt_iff (x y : ValidOrdinal) : x.lt y ↔ x.toNote < y.toNote :=
  Proofs.Logic.ACL2.Ordinals.lt_iff x y

/-- Equal exponents in the three-way comparison are identical ACL2 encodings, so comparison
continues with coefficients exactly when ACL2's structural EQUAL test succeeds. -/
theorem ValidOrdinal.cmp_eq_eq (x y : ValidOrdinal) : x.val.cmp y.val = .eq ↔ x.val = y.val :=
  Proofs.Logic.ACL2.Ordinals.cmp_eq_eq x y

/-- The three comparison clauses of ACL2 O< for infinite ordinals. -/
theorem Encoding.oLt_makeOrd_iff (e e' : ValidOrdinal) (c c' : Nat) (r r' : Encoding) :
    (makeOrd e.val c r).oLt (makeOrd e'.val c' r') = true ↔
      e.lt e' ∨ e.val = e'.val ∧ (c < c' ∨ c = c' ∧ r.oLt r' = true) := by
  simp only [makeOrd, oLt, Encoding.cmp, ValidOrdinal.lt, beq_iff_eq, Ordering.then_eq_lt,
    ValidOrdinal.cmp_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_eq]

theorem ValidOrdinal.wellFounded : WellFounded ValidOrdinal.lt :=
  Proofs.Logic.ACL2.Ordinals.wellFounded

end Silmaril.Logic.ACL2.Ordinals
