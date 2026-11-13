module

public import Silmaril.Wasm.Unified.Component.Abi30.Thms
public import Silmaril.Wasm.Unified.Versions.FXEq.Thms
public import Silmaril.Wasm.Unified.Versions.FXsEq.Thms

/-!
# WasmFX as a core semantics of components

The WasmFX models of the unified institution (`fxModelAt`: CoreFX `StepFX`; `fxModelAt'`:
`StepFX'` with continuation values) have the inputs and observations of the other Wasm models
(`List Val`, `Behaviour Val`), so they are core semantics of the component layer through the flat
calling convention `abi30`:

* `coreSem_congr`, `coreSemV_congr`: the core semantics of a model depends only on its
  observations (the core strategy answers with the observations); so an equation of
  observations (`ObsEq`) is an equation of core semantics;
* `coreSemFX`, `coreSemFX'`: **WasmFX as the core semantics of components over `sigFX`**;
* **`fxEmb_comp`**, `fxEmb'_comp`: at the component level `fxEmb` is an **equation**: the core
  semantics of Core 3.0 is the pull-back of WasmFX's at the embedded point along the inclusion
  `3.0 ⊆ FX` (from `fxEmb_obsEq`, although the models differ);
* `fx_denU`: a component over 3.0 modules means, in Core 3.0, what the same component with its
  modules included into WasmFX means in WasmFX at the embedded point;
* `coreSemFXs`, **`fxsEmb_comp`**, `fxs_denU`: the same for the repaired WasmFX model
  `fxModelNsAt` (FX structured forms reachable, `Silmaril.Wasm.Unified.Versions.FXsEq`), with the
  validation `okcLift okc`.

Continuation values do not cross the component boundary: `abi30` answers only numeric results
(a continuation reference among the results is a trap, like any reference).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (Payload CoreSem Comp)
open Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Versions

variable {In B : Type} {S : FSig}

/-- The core semantics of a unified model depends only on its observations. -/
theorem coreSem_congr {M N : PModel S} (h : ∀ x, M.obs x = N.obs x) : coreSem M = coreSem N := by
  have hobs : M.obs = N.obs := funext h
  unfold coreSem coreRed
  rw [hobs]

/-- Equal observations stay equal through a calling convention. -/
theorem abi_obsEq (A : Abi In B) {M N : Model In B S} (h : ObsEq M N) :
    ∀ x, (M.abi A).obs x = (N.abi A).obs x := by
  have hMN : M.obs = N.obs := funext h
  rintro ⟨c, p⟩
  rw [obs_abi, obs_abi, hMN]

/-- **An equation of observations is an equation of core semantics.** -/
theorem coreSemV_congr {M N : Model (List Val) (Behaviour Val) S} (h : ObsEq M N) :
    coreSemV M = coreSemV N :=
  coreSem_congr (abi_obsEq abi30 h)

variable {H : Type}

/-- **WasmFX (`StepFX`) as the core semantics of components.** -/
abbrev coreSemFX (P : Profile) (f : Frame) (okcFX : List FX.InstrFX → Prop) (x : FX.Pt H) :
    CoreSem (UMod sigFX) :=
  coreSemV (fxModelAt P f okcFX x)

/-- **WasmFX with continuation values (`StepFX'`) as the core semantics of components.** -/
abbrev coreSemFX' (P : Profile) (f : Frame) (okcFX : List FX.InstrFX → Prop) (x : FX.Pt H) :
    CoreSem (UMod sigFX) :=
  coreSemV (fxModelAt' P f okcFX x)

variable (f : Frame) (okc : List Instr → Prop)

/-- **`fxEmb` at the component level, as an equation.** -/
theorem fxEmb_comp (P : Profile) (okcFX : List FX.InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map FX.InstrFX.core) ↔ okc is) (x : Core.Pt H) :
    coreSemV (coreSAt v30 P f okc x) =
      pullC (coreSemFX P f okcFX ((FX.fxEmb P H).pt x)) (FSig.incl nsub_30_FX) := by
  rw [← coreSemV_reduct]
  exact coreSemV_congr fun y => (fxEmb_obsEq f okc P okcFX hok x y).symm

/-- `fxEmb'` (`StepFX'`) at the component level, as an equation. -/
theorem fxEmb'_comp (P : Profile) (okcFX : List FX.InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map FX.InstrFX.core) ↔ okc is) (x : Core.Pt H) :
    coreSemV (coreSAt v30 P f okc x) =
      pullC (coreSemFX' P f okcFX ((FXVModel.fxEmb' P H).pt x)) (FSig.incl nsub_30_FX) := by
  rw [← coreSemV_reduct]
  exact coreSemV_congr fun y => (fxEmb'_obsEq f okc P okcFX hok x y).symm

/-- **A 3.0 component is a WasmFX component**: its meaning in Core 3.0 is the meaning of the same
component, modules included into WasmFX, in WasmFX at the embedded point. -/
theorem fx_denU (P : Profile) (okcFX : List FX.InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map FX.InstrFX.core) ↔ okc is) (x : Core.Pt H)
    (c : Comp (UMod (nsig v30))) :
    c.denU (coreSemV (coreSAt v30 P f okc x)) =
      (mapComp (FSig.incl nsub_30_FX) c).denU (coreSemFX P f okcFX ((FX.fxEmb P H).pt x)) := by
  rw [denU_mapComp, fxEmb_comp f okc P okcFX hok]

/-- **The repaired WasmFX model as the core semantics of components.** -/
abbrev coreSemFXs (P : Profile) (f : Frame) (okcFX : List FX.InstrFX → Prop) (x : FX.Pt H) :
    CoreSem (UMod sigFX) :=
  coreSemV (fxModelNsAt P f okcFX x)

/-- **`fxEmb` into the repaired WasmFX model at the component level, as an equation.** -/
theorem fxsEmb_comp (P : Profile) (x : Core.Pt H) :
    coreSemV (coreSAt v30 P f okc x) =
      pullC (coreSemFXs P f (okcLift okc) ((FX.fxEmb P H).pt x)) (FSig.incl nsub_30_FX) := by
  rw [← coreSemV_reduct]
  exact coreSemV_congr fun y => (fxsEmb_obsEq f okc P x y).symm

/-- A 3.0 component means in Core 3.0 what it means in the repaired WasmFX model. -/
theorem fxs_denU (P : Profile) (x : Core.Pt H) (c : Comp (UMod (nsig v30))) :
    c.denU (coreSemV (coreSAt v30 P f okc x)) =
      (mapComp (FSig.incl nsub_30_FX) c).denU
        (coreSemFXs P f (okcLift okc) ((FX.fxEmb P H).pt x)) := by
  rw [denU_mapComp, fxsEmb_comp f okc P]

end Silmaril.Wasm.Unified.Component
