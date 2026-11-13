module

public import Silmaril.Wasm.Category.Component.Defs

@[expose] public section

/-!
# Components over Core 3.0 instances: morphisms and results

For every core semantics `C`, in particular the Core 3.0 one
`Silmaril.Wasm.Component.Reference.core3Sem P`:

* `wrapR C : Realiser (modCompLang C) (compLang C)`: the trivial component wrapping a core
  module realises it exactly (`Silmaril.Wasm.Institution.Components.wrap_denU`);
* `optimizeEndo C : EndoPass (compLang C)`: the component optimiser (adapter fusion, dead
  exports and instances, flattening, handler specialisation) preserves the strategy exactly
  (`optimizeComponent_sound'`).

Monotonicity in the profile of the Core 3.0 core semantics and of component denotations is
`Silmaril.Wasm.Component.Reference.{core3Sem_le, denU_core3Sem_le}`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Component
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- **Wrapping a core module as a component is exact.** -/
def wrapR : Realiser (modCompLang C) (compLang C) where
  Φ := id
  prog := Silmaril.Wasm.Institution.Components.wrap
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh m := by
    have e : (Silmaril.Wasm.Institution.Components.wrap m).denU C =
        Silmaril.Wasm.Institution.Components.modU C m :=
      Silmaril.Wasm.Institution.Components.wrap_denU C m
    have hs : (compLang C).beh (Silmaril.Wasm.Institution.Components.wrap m) =
        (modCompLang C).beh m := by
      show {s | s ∈ (Silmaril.Wasm.Institution.Components.wrap m).denU C} =
        {s | s ∈ Silmaril.Wasm.Institution.Components.modU C m}
      rw [e]
    exact (Set.image_id _).trans hs

/-- **The component optimiser as an optimization**: it preserves the strategy exactly. -/
def optimizeEndo : EndoPass (compLang C) where
  run := optimizeComponent
  refines c := by
    have e : (optimizeComponent c).denU C = c.denU C := (optimizeComponent_sound' C c).1
    refine ⟨rfl, ?_⟩
    show {s | s ∈ (optimizeComponent c).denU C} ⊆ {s | s ∈ c.denU C}
    rw [e]

end Silmaril.Wasm.Category
