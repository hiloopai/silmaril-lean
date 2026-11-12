module

/-! # Proof-relevant subtyping independent of type formers -/

@[expose] public section

universe u

namespace Silmaril.Isotope

/-- Coercion witnesses with identity and composition, without type-former rules. -/
class SubtypingCore (τ : Type u) where
  Subty : τ → τ → Type u
  refl (A : τ) : Subty A A
  trans {A B C : τ} : Subty A B → Subty B C → Subty A C

abbrev Subty {τ : Type u} [SubtypingCore τ] (A B : τ) : Type u :=
  SubtypingCore.Subty A B

namespace Subty

variable {τ : Type u} [SubtypingCore τ]

def refl (A : τ) : Subty A A := SubtypingCore.refl A

def trans {A B C : τ} (f : Subty A B) (g : Subty B C) : Subty A C :=
  SubtypingCore.trans f g

end Subty

end Silmaril.Isotope
