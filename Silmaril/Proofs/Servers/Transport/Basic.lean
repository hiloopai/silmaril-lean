module

public import Silmaril.Servers.Transport.Defs

/-!
# Proofs: transports
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Transport

open Silmaril.Servers.Transport

variable {α β γ : Type}

theorem image_comp (g : PMap β γ) (f : PMap α β) (M : Set α) :
    (g.comp f).image M = g.image (f.image M) := by
  ext c
  constructor
  · rintro ⟨a, ha, he⟩
    simp only [PMap.comp] at he
    cases hf : f a with
    | none => rw [hf] at he; cases he
    | some b => rw [hf] at he; exact ⟨b, ⟨a, ha, hf⟩, he⟩
  · rintro ⟨b, ⟨a, ha, hf⟩, hg⟩
    exact ⟨a, ha, by simp [PMap.comp, hf, hg]⟩

theorem may_reflect_of_total {f : PMap α β} {M : Set α} (ht : f.Total M) {P : α → Prop}
    (h : ∃ a ∈ M, P a) : ∃ b ∈ f.image M, ∃ a ∈ M, P a ∧ f a = some b := by
  obtain ⟨a, ha, hp⟩ := h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (ht a ha)
  exact ⟨b, ⟨a, ha, hb⟩, a, ha, hp, hb⟩

end Silmaril.Proofs.Servers.Transport
