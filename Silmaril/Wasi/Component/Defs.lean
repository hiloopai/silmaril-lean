module

public import Silmaril.Wasi.World.Defs
public import Silmaril.Wasm.Component.Semantics.Defs

@[expose] public section

/-!
# Components of the component IR as WASI models

The component logics of `Silmaril.Wasm.Institution.Components` denote a component `c : Comp M`
(for a core semantics `C : CoreSem M`) by a strategy `Comp.denU C c : Strategy sigU sigU`, whose
imports and exports are *positions* with dynamically typed payloads. A **layout** names the
positions: `L.imports[i]` is the WIT function of import `i`, `L.exports[j]` that of export `j`.
It gives the world `L.world` and reads a `sigU` strategy as a model of that world:

* `lowerH L`: the import calls of the component, by position, are forwarded to the named imports
  (an out-of-range position or a flat core payload traps);
* `upH L`: a named export call is offered at its position, with its arguments as component
  values (an answer that is not component values is a trap);
* `view L σ = (ofHandler (lowerH L)).comp (σ.restrict (upH L))`, and `compModel C L c` the view
  of `Comp.denU C c`.

This is the model part of a translation from the component logics into `WasiInst`: every
component of the IR, with any core semantics, is a WASI component, and WASI sentences can be
stated about it. `view` is monotone, so WASI safety sentences (`ag`) transfer along refinement
of components (`Silmaril.Wasi.Component.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasi

open Silmaril.Games Silmaril.Wasm.Component

/-- Names of the import and export positions of a component. -/
structure Layout where
  /-- The function of each import position. -/
  imports : List FnName
  /-- The function of each export position. -/
  exports : List FnName

namespace Layout

/-- The world of a layout. -/
def world (L : Layout) : World := ⟨{f | f ∈ L.imports}, {f | f ∈ L.exports}⟩

/-- Import calls by position, forwarded to the named imports. -/
def lowerH (L : Layout) : Handler (nsig L.world.imports) sigU := fun q =>
  match h : L.imports[q.1]?, q.2 with
  | some f, .vals vs => .call (⟨f, List.mem_of_getElem? h⟩, vs) fun r => .pure (r.map .vals)
  | _, _ => .pure none

/-- Named export calls, offered at their positions. -/
def upH (L : Layout) : Sig.Hom (nsig L.world.exports) sigU :=
  ⟨fun q => (L.exports.idxOf q.1.1, .vals q.2), fun _ r =>
    match r with
    | some (.vals vs) => some vs
    | _ => none⟩

/-- **A `sigU` strategy as a model of the world of a layout.** -/
def view (L : Layout) (σ : Strategy sigU sigU) : L.world.Model :=
  (Strategy.ofHandler L.lowerH).comp (σ.restrict L.upH)

/-- **A component of the IR as a WASI model.** -/
def compModel {M : Type} [CoreModule M] (C : CoreSem M) (L : Layout) (c : Comp M) :
    L.world.Model :=
  L.view (c.denU C)

end Layout

end Silmaril.Wasi
