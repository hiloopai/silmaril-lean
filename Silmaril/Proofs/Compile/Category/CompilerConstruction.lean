module

public import Silmaril.Compile.Category.Rel

@[expose] public section

namespace Silmaril.Proofs.Compile.Category

open CategoryTheory Silmaril.Compile.Category

universe u

/-- Soundness of partial-function composition, independent of the compiler record. -/
theorem comp_sound {L L' L'' : Language.{u}} {c : L ⟶ L'} {d : L' ⟶ L''}
    {f : L.Prog → Option L'.Prog} {g : L'.Prog → Option L''.Prog}
    (hf : ∀ p q, f p = some q → Valid c p q)
    (hg : ∀ q r, g q = some r → Valid d q r)
    {p : L.Prog} {r : L''.Prog} (h : (f p).bind g = some r) :
    Valid (c ≫ d) p r := by
  cases hq : f p with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some q =>
    rw [hq] at h
    exact valid_comp_le c d p r ⟨q, hf p q hq, hg q r h⟩

end Silmaril.Proofs.Compile.Category
