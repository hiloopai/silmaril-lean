module

public import Silmaril.X86.Sep.Extra.Defs

/-!
# Proofs: distribution of `∗` over `sor`

Behind `Silmaril/X86/Sep/Extra/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep

open Silmaril.X86.Sep

theorem sor_sep (P Q R : SProp) : (sor P Q ∗ R) = sor (P ∗ R) (Q ∗ R) := by
  funext h
  apply propext
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hpq | hpq, hr⟩
    · exact .inl ⟨h₁, h₂, hd, rfl, hpq, hr⟩
    · exact .inr ⟨h₁, h₂, hd, rfl, hpq, hr⟩
  · rintro (⟨h₁, h₂, hd, rfl, hp, hr⟩ | ⟨h₁, h₂, hd, rfl, hq, hr⟩)
    · exact ⟨h₁, h₂, hd, rfl, .inl hp, hr⟩
    · exact ⟨h₁, h₂, hd, rfl, .inr hq, hr⟩

end Silmaril.Proofs.X86.Sep
