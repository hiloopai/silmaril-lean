module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Defs

public section

namespace Silmaril.Proofs.Formats.Blake3Cas.RangeFacts

open Silmaril.Crypto.Blake3
open Silmaril.Formats.Blake3Cas (ConcreteCollision)
open Silmaril.Formats.Blake3Cas.RangeFacts
open Silmaril.Semantics.Naming.ByteRange (Slice slice_iff)

theorem suffix_iff {whole bytes : Bytes} {start : Nat} :
    SuffixAt whole start bytes ↔ ExactAt whole start whole.length bytes := by
  unfold SuffixAt ExactAt
  rw [slice_iff]
  constructor
  · rintro ⟨bound, rfl⟩
    simp [List.length_drop, Nat.add_sub_of_le bound]
  · rintro ⟨exactLength, _, read⟩
    have length : (whole.drop start).length = bytes.length := by simp; omega
    exact ⟨by omega, by simpa only [← length, List.take_length] using read⟩

theorem joinSlices {whole left right : Bytes} {start middle : Nat}
    (lhs : Slice whole start left) (rhs : Slice whole middle right)
    (adjacent : start + left.length = middle) : Slice whole start (left ++ right) := by
  subst middle
  obtain ⟨_, readLeft⟩ := slice_iff.mp lhs
  obtain ⟨bound, readRight⟩ := slice_iff.mp rhs
  exact slice_iff.mpr ⟨by simpa [List.length_append, Nat.add_assoc] using bound,
    by simp [List.take_add, readLeft, readRight]⟩

theorem emptyBound {whole : Bytes} {start : Nat} : ExactAt whole start start [] ↔ start ≤ whole.length := by
  simp [ExactAt, slice_iff]

theorem suffixAgainst {digest whole : Bytes} {start : Nat} (suffix : Suffix digest start)
    (named : Named concrete digest whole) : SuffixAt whole start suffix.bytes ∨ ConcreteCollision := by
  rcases suffix.extent.down.concreteExtentOrCollision named with extent | collision
  · exact (suffix.bounded.against named).imp (fun fact => suffix_iff.mpr (extent ▸ fact)) id
  · exact .inr collision

end Silmaril.Proofs.Formats.Blake3Cas.RangeFacts
