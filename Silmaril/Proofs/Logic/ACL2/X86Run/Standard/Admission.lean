module

public import Silmaril.Logic.ACL2.X86Run.Standard.Defs
import Silmaril.Logic.ACL2.Standard.Objects.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.X86Run.Standard

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Standard Silmaril.Logic.ACL2.X86Run

theorem positive_count {n : Object} (h : n.zp = Object.nil) :
    ∃ i, n.integerValue? = some i ∧ 0 < i := by
  obtain ⟨i, hi, hn⟩ := (Object.zp_eq_nil_iff n).1 h
  exact ⟨i, (Object.integerValue?_eq_some_iff n i).2 hn, hi⟩

theorem add_integers {x y : Object} {i j : Int}
    (hi : x.integerValue? = some i) (hj : y.integerValue? = some j) :
    (x.binaryAdd y).integerValue? = some (i + j) := by
  apply (Object.integerValue?_eq_some_iff _ _).2
  rw [(Object.integerValue?_eq_some_iff _ _).1 hi,
    (Object.integerValue?_eq_some_iff _ _).1 hj]
  have add := Rat.intCast_add i j
  change Rat.ofInt (i + j) = Rat.ofInt i + Rat.ofInt j at add
  change Object.ofParts (Rat.ofInt i + Rat.ofInt j) (0 + 0) = .rational (Rat.ofInt (i + j))
  rw [Rat.add_zero, Object.ofParts_zero, ← add]

end Silmaril.Proofs.Logic.ACL2.X86Run.Standard
