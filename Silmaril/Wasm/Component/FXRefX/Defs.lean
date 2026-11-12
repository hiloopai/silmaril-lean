module

public import Silmaril.Wasm.Component.FXRefV.Defs

/-!
# The reference-machine half over `fxE P` for components whose modules carry FX functions

`FXRefE.refToSpecE_fx` proves the machine half over the WasmFX engine `fxE P` for Core modules
seen as FX modules (`FXRef.ofCoreFX`, no FX functions), and `FXRefV.refToSpecFX` proves it for
components whose modules **carry FX functions** (`FXRefV.SimpleFX`), over the suspending engine
`fxEV P`, given `SimpleFX.Typed`. The remaining combination, FX functions over `fxE P` itself
(FX functions allocated as host functions outside the function index space, threads run by
`StepFX`), is stated here and frozen:

* `SimpleFX.TypedE P c`: `SimpleFX.Typed` with `fxE P` in place of `fxEV P`: values returned by
  the engine instance's export calls on lowered well-typed arguments have the export's flat
  result types;
* `RefToSpecFXE P`: `FXRefV.RefToSpecFX P` with `fxE P` in place of `fxEV P`, conditional on
  `TypedE`;
* **`Task.refToSpecFXE`** (open, frozen): `RefToSpecFXE P` at every profile. No result depends
  on it.

Plan and obstacle (see "Stretch, fx (ws5 an earlier step)" in `docs/projects/wasm-components.md`): the proof of
`refToSpecFX` (`Silmaril.Proofs.Wasm.Component.FXRefV.{Inst,Map,Run}`, about 940 lines) goes
through `EngineRef.refToSpecE_of_facts` with instantiation facts and run facts. For `fxE P` the
instantiation facts change only in the instance the FX functions see (`prepareFX?` passes the
Core instance where `prepareFXV?` passes `fxInst`), and the run facts need the host renaming of
`StepFX` runs (all rules) and of `InternalFX`, `statusFX`, in place of the `StepFX'` ones of
`FXRefV.Map`. Those proofs live in the proof modules of the topics `FXRefV`, `FXEngine` and
`FXRefE`; reusing them here would import other topics' `Proofs` modules, which the layout rules
forbid, so the port means copying or promoting them to headers.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRefX

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXRefV
open Silmaril.Wasm.Numerics (Profile)

/-- **FX type soundness at the export types, over `fxE P`.** -/
def SimpleFX.TypedE (P : Profile) (c : SimpleFX) : Prop :=
  ∀ J, instOf (fxE P) (c.emb c.mod) [] c.mod.exports = some J →
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      ∀ ys, some ys ∈ engineOut (fxE P) J x.core (lowerArgs x.ty.params vs) →
        ys.map (·.type) = ValTy.flatList x.ty.results

/-- **The machine half over `fxE P` for components whose modules carry FX functions.** -/
def RefToSpecFXE (P : Profile) : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : SimpleFX), c.toSimple.Good →
    c.toSimple.FloatFree → c.Inst → c.toSimple.Arity → SimpleFX.TypedE P c →
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE (fxE P)) () (c.toSimple.toRef.map c.ofCore) [] x.name
          (vs.map toRefVal) ⊆
        exportSpecE (fxE P) c.emb c.toSimple x vs

/-- **Open (frozen)**: `RefToSpecFXE P` at every profile. -/
def Task.refToSpecFXE : Prop := ∀ P : Profile, RefToSpecFXE P

end Silmaril.Wasm.Component.FXRefX
