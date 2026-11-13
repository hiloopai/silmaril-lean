module

public import Silmaril.Wasi.Component.Defs
public import Silmaril.Wasi.World.Thms
public import Silmaril.Games.Handler.Thms

@[expose] public section

/-!
# Components of the component IR as WASI models: refinement

* `Layout.view_mono`: the WASI view is monotone.
* `Layout.ag_of_le`, `Layout.compModel_ag_of_le`: a WASI assume–guarantee sentence of a
  component is inherited by every component refining it (in the strategy order of the component
  logics).
-/

namespace Silmaril.Wasi

open Silmaril.Games Silmaril.Wasm.Component

namespace Layout

/-- The view is monotone. -/
theorem view_mono (L : Layout) {σ τ : Strategy sigU sigU} (h : σ ≤ τ) : L.view σ ≤ L.view τ :=
  Strategy.comp_mono_right _ (Strategy.restrict_mono h _)

/-- WASI safety sentences transfer along refinement. -/
theorem ag_of_le (L : Layout) {A G : List WEv → Prop} {σ τ : Strategy sigU sigU} (h : σ ≤ τ)
    (hτ : (ag A G).holds (L.view τ)) : (ag A G).holds (L.view σ) :=
  ag_mono (L.view_mono h) hτ

/-- **WASI safety sentences transfer along refinement of IR components.** -/
theorem compModel_ag_of_le {M : Type} [CoreModule M] (C : CoreSem M) (L : Layout)
    {A G : List WEv → Prop} {c c' : Comp M} (h : c.denU C ≤ c'.denU C)
    (hc' : (ag A G).holds (compModel C L c')) : (ag A G).holds (compModel C L c) :=
  L.ag_of_le h hc'

end Layout

end Silmaril.Wasi
