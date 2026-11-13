module

public import Silmaril.Games.Composition.Defs
public import Silmaril.Logic.Institution.Room
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# Play properties and their transport along linking

Strategies satisfy play properties in two ways: universally (`SatA`, every play has the
property: safety) and existentially (`SatE`, some play has it: "this program can exhibit this
behaviour"). Linking is composition (`Silmaril.Wasm.Category.Linking`), which changes the
interface, so it is not a signature morphism; what holds is a family of **corridors**, one per
fixed partner:

* for a fixed provider `σ : E ⟶ F`, a property `φ` of the composite's plays holds of
  `σ ≫ τ` iff `consumerSenA σ φ` (resp. `consumerSenE σ φ`) holds of the consumer `τ`;
* for a fixed consumer `τ`, iff `providerSenA τ φ` (resp. `providerSenE`) holds of `σ`;
* partner-independently, iff the pair `(σ, τ)` satisfies `linkSenA φ` (resp. `linkSenE`), a
  property of pairs of plays that synchronise.

These are packaged as corridors of rooms (`Silmaril.Logic.Institution.Room`): `linkCorridorA σ`,
`linkCorridorE σ`, `provCorridorA τ`, `provCorridorE τ`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution

universe u

variable {E F G : Sig.{u}}

/-- A play property of strategies `E ⟶ F`. -/
abbrev PlaySen (E F : Sig.{u}) : Type u := Set (List (Move E F))

/-- Universal satisfaction: every play has the property. -/
def SatA (σ : Strategy E F) (φ : PlaySen E F) : Prop := ∀ p ∈ σ, p ∈ φ

/-- Existential satisfaction: some play has the property. -/
def SatE (σ : Strategy E F) (φ : PlaySen E F) : Prop := ∃ p ∈ σ, p ∈ φ

/-- Universal translation to the consumer, for a fixed provider. -/
def consumerSenA (σ : Strategy E F) (φ : PlaySen E G) : PlaySen F G :=
  {t | ∀ s ∈ σ, ∀ p, Zip s t p → p ∈ φ}

/-- Existential translation to the consumer, for a fixed provider. -/
def consumerSenE (σ : Strategy E F) (φ : PlaySen E G) : PlaySen F G :=
  {t | ∃ s ∈ σ, ∃ p ∈ φ, Zip s t p}

/-- Universal translation to the provider, for a fixed consumer. -/
def providerSenA (τ : Strategy F G) (φ : PlaySen E G) : PlaySen E F :=
  {s | ∀ t ∈ τ, ∀ p, Zip s t p → p ∈ φ}

/-- Existential translation to the provider, for a fixed consumer. -/
def providerSenE (τ : Strategy F G) (φ : PlaySen E G) : PlaySen E F :=
  {s | ∃ t ∈ τ, ∃ p ∈ φ, Zip s t p}

/-- The partner-independent universal translation: pairs of plays every synchronisation of
which has the property. -/
def linkSenA (φ : PlaySen E G) : Set (List (Move E F) × List (Move F G)) :=
  {st | ∀ p, Zip st.1 st.2 p → p ∈ φ}

/-- The partner-independent existential translation: pairs of plays with a synchronisation
having the property. -/
def linkSenE (φ : PlaySen E G) : Set (List (Move E F) × List (Move F G)) :=
  {st | ∃ p ∈ φ, Zip st.1 st.2 p}

/-- The universal room of strategies `E ⟶ F`: play properties, strategies (discrete), `SatA`. -/
def roomA (E F : Sig.{u}) : Room.{u, u, u} where
  Sen := PlaySen E F
  Mod := Cat.of (Discrete (Strategy E F))
  Sat σ φ := SatA (Discrete.as σ) φ

/-- The existential room of strategies `E ⟶ F`. -/
def roomE (E F : Sig.{u}) : Room.{u, u, u} where
  Sen := PlaySen E F
  Mod := Cat.of (Discrete (Strategy E F))
  Sat σ φ := SatE (Discrete.as σ) φ

end Silmaril.Wasm.Category
