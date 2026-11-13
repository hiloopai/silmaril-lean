module

public import Silmaril.Wasm.Category.LinkSat.Defs
public import Silmaril.Wasm.Category.Linking.Thms

@[expose] public section

/-!
# Play properties and linking: results

* `satA_consumerSenA_iff`, `satE_consumerSenE_iff`, `satA_providerSenA_iff`,
  `satE_providerSenE_iff`: the corridor conditions of linking for a fixed partner;
* `satA_comp_iff_linkSenA`, `satE_comp_iff_linkSenE`: the partner-independent forms;
* `linkCorridorA σ`, `linkCorridorE σ`, `provCorridorA τ`, `provCorridorE τ`: the corridors;
* **for static links of Wasm modules** (M3): `Linking.Setup.linked_satA_iff`,
  `Linking.Setup.linked_satE_iff`: a play property of the linked module's strategy holds iff
  its translation holds of the consumer, for the provider's strategy, at every profile.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution

universe u

variable {E F G : Sig.{u}}

theorem satA_consumerSenA_iff (σ : Strategy E F) (τ : Strategy F G) (φ : PlaySen E G) :
    SatA τ (consumerSenA σ φ) ↔ SatA (σ.comp τ) φ := by
  constructor
  · rintro h p ⟨s, hs, t, ht, hz⟩
    exact h t ht s hs p hz
  · intro h t ht s hs p hz
    exact h p ⟨s, hs, t, ht, hz⟩

theorem satE_consumerSenE_iff (σ : Strategy E F) (τ : Strategy F G) (φ : PlaySen E G) :
    SatE τ (consumerSenE σ φ) ↔ SatE (σ.comp τ) φ := by
  constructor
  · rintro ⟨t, ht, s, hs, p, hp, hz⟩
    exact ⟨p, ⟨s, hs, t, ht, hz⟩, hp⟩
  · rintro ⟨p, ⟨s, hs, t, ht, hz⟩, hp⟩
    exact ⟨t, ht, s, hs, p, hp, hz⟩

theorem satA_providerSenA_iff (σ : Strategy E F) (τ : Strategy F G) (φ : PlaySen E G) :
    SatA σ (providerSenA τ φ) ↔ SatA (σ.comp τ) φ := by
  constructor
  · rintro h p ⟨s, hs, t, ht, hz⟩
    exact h s hs t ht p hz
  · intro h s hs t ht p hz
    exact h p ⟨s, hs, t, ht, hz⟩

theorem satE_providerSenE_iff (σ : Strategy E F) (τ : Strategy F G) (φ : PlaySen E G) :
    SatE σ (providerSenE τ φ) ↔ SatE (σ.comp τ) φ := by
  constructor
  · rintro ⟨s, hs, t, ht, p, hp, hz⟩
    exact ⟨p, ⟨s, hs, t, ht, hz⟩, hp⟩
  · rintro ⟨p, ⟨s, hs, t, ht, hz⟩, hp⟩
    exact ⟨s, hs, t, ht, p, hp, hz⟩

/-- The partner-independent universal form. -/
theorem satA_comp_iff_linkSenA (σ : Strategy E F) (τ : Strategy F G) (φ : PlaySen E G) :
    SatA (σ.comp τ) φ ↔ ∀ s ∈ σ, ∀ t ∈ τ, (s, t) ∈ linkSenA (F := F) φ := by
  constructor
  · intro h s hs t ht p hz
    exact h p ⟨s, hs, t, ht, hz⟩
  · rintro h p ⟨s, hs, t, ht, hz⟩
    exact h s hs t ht p hz

/-- The partner-independent existential form. -/
theorem satE_comp_iff_linkSenE (σ : Strategy E F) (τ : Strategy F G) (φ : PlaySen E G) :
    SatE (σ.comp τ) φ ↔ ∃ s ∈ σ, ∃ t ∈ τ, (s, t) ∈ linkSenE (F := F) φ := by
  constructor
  · rintro ⟨p, ⟨s, hs, t, ht, hz⟩, hp⟩
    exact ⟨s, hs, t, ht, p, hp, hz⟩
  · rintro ⟨s, hs, t, ht, p, hp, hz⟩
    exact ⟨p, ⟨s, hs, t, ht, hz⟩, hp⟩

/-- The universal linking corridor for a fixed provider. -/
def linkCorridorA (σ : Strategy E F) : Corridor (roomA E G) (roomA F G) where
  sen := consumerSenA σ
  mod := Discrete.functor fun τ => Discrete.mk (σ.comp τ)
  sat τ φ := satA_consumerSenA_iff σ τ.as φ

/-- The existential linking corridor for a fixed provider. -/
def linkCorridorE (σ : Strategy E F) : Corridor (roomE E G) (roomE F G) where
  sen := consumerSenE σ
  mod := Discrete.functor fun τ => Discrete.mk (σ.comp τ)
  sat τ φ := satE_consumerSenE_iff σ τ.as φ

/-- The universal linking corridor for a fixed consumer. -/
def provCorridorA (τ : Strategy F G) : Corridor (roomA E G) (roomA E F) where
  sen := providerSenA τ
  mod := Discrete.functor fun σ => Discrete.mk (σ.comp τ)
  sat σ φ := satA_providerSenA_iff σ.as τ φ

/-- The existential linking corridor for a fixed consumer. -/
def provCorridorE (τ : Strategy F G) : Corridor (roomE E G) (roomE E F) where
  sen := providerSenE τ
  mod := Discrete.functor fun σ => Discrete.mk (σ.comp τ)
  sat σ φ := satE_providerSenE_iff σ.as τ φ

namespace Linking.Setup

open Silmaril.Wasm.Game Silmaril.Wasm.Numerics

variable (S : Silmaril.Wasm.Game.Linking.Setup) (P : Profile)

/-- **Universal play properties of a linked Wasm module** hold iff their translation holds of
the consumer, for the provider's strategy (every profile). -/
theorem linked_satA_iff (hS : S.Scalar) (φ : PlaySen (ifaceSig []) (ifaceSig S.exportTypes)) :
    SatA (S.linkedI.σ P) φ ↔ SatA (S.consumerI.σ P) (consumerSenA (S.providerI.σ P) φ) := by
  have e : (S.linkedI.σ P : Strategy (ifaceSig []) (ifaceSig S.exportTypes)) =
      (S.providerI.σ P).comp (S.consumerI.σ P) := S.link_is_composition_profile hS P
  exact (congrArg (fun σ => SatA σ φ) e).to_iff.trans (satA_consumerSenA_iff _ _ φ).symm

/-- **Existential play properties of a linked Wasm module** hold iff their translation holds of
the consumer, for the provider's strategy (every profile). -/
theorem linked_satE_iff (hS : S.Scalar) (φ : PlaySen (ifaceSig []) (ifaceSig S.exportTypes)) :
    SatE (S.linkedI.σ P) φ ↔ SatE (S.consumerI.σ P) (consumerSenE (S.providerI.σ P) φ) := by
  have e : (S.linkedI.σ P : Strategy (ifaceSig []) (ifaceSig S.exportTypes)) =
      (S.providerI.σ P).comp (S.consumerI.σ P) := S.link_is_composition_profile hS P
  exact (congrArg (fun σ => SatE σ φ) e).to_iff.trans (satE_consumerSenE_iff _ _ φ).symm

end Linking.Setup

end Silmaril.Wasm.Category
