module

public import Silmaril.Wasm.Component.FXRefV.Defs
public import Silmaril.Wasm.Component.Reference.Link.Defs

/-!
# Discharging `SimpleFX.Typed`: definitions

`FXRefV.refToSpecFX` proves the machine half for components whose modules carry FX functions
under one hypothesis, `SimpleFX.Typed P c`: the values returned by the `fxEV P` engine instance
on a typed call of each lifted export have the export's flat result types. This module states
the per-export pieces of that hypothesis and the fragment in which it is discharged.

* `SimpleFX.TypedAt P c x`: `Typed` for one export `x`;
* `SimpleFX.ArityAt P c x`: the weaker **arity** statement for `x`: returned value lists have
  as many values as the export has flat results;
* `SimpleFX.Frag c`: **the typed fragment**: a lifted Core export requires the Core part to be in
  the split fragment of `Linked2` (`ModSplitOk`: no tags, memories, tables or segments, so that
  its store is related to the store extended by the FX functions); a lifted FX export has no
  flat results.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXTyped

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXRefV
open Silmaril.Wasm.Numerics (Profile)

namespace SimpleFX

/-- **`SimpleFX.Typed` at one export.** -/
def TypedAt (P : Profile) (c : FXRefV.SimpleFX) (x : SimpleExport) : Prop :=
  ∀ J, instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some J →
    ∀ vs, ValTy.checkList x.ty.params vs = true →
      ∀ ys, some ys ∈ engineOut (fxEV P) J x.core (lowerArgs x.ty.params vs) →
        ys.map (·.type) = ValTy.flatList x.ty.results

/-- **Arity at one export**: returned value lists have the export's number of flat results. -/
def ArityAt (P : Profile) (c : FXRefV.SimpleFX) (x : SimpleExport) : Prop :=
  ∀ J, instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some J →
    ∀ vs, ValTy.checkList x.ty.params vs = true →
      ∀ ys, some ys ∈ engineOut (fxEV P) J x.core (lowerArgs x.ty.params vs) →
        ys.length = (ValTy.flatList x.ty.results).length

/-- **The typed fragment**: Core exports over a Core part in the split fragment, and FX exports
without flat results. -/
structure Frag (c : FXRefV.SimpleFX) : Prop where
  /-- A lifted Core export needs the Core part in the split fragment. -/
  core : ∀ x ∈ c.exports, x.core < c.core.exports.length → Linked2.ModSplitOk c.core.mod
  /-- A lifted FX export has no flat results. -/
  fx : ∀ x ∈ c.exports, c.core.exports.length ≤ x.core → ValTy.flatList x.ty.results = []

end SimpleFX

end Silmaril.Wasm.Component.FXTyped
