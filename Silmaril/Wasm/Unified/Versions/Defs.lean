module

public import Silmaril.Wasm.Unified.Versions.Named.Thms
public import Silmaril.Wasm.Unified.Versions.FX.Defs
public import Silmaril.Wasm.Models.V10.Thms
public import Silmaril.Wasm.Models.Lime1Core.Thms
public import Silmaril.Wasm.Models.FX.Thms
public import Silmaril.Wasm.Atlas.Wasmi.Defs

/-!
# The Wasm versions as models of the unified institution

Every version model of `Silmaril.Wasm.Models` (and the wasmi and loose charts of
`Silmaril.Wasm.Atlas.Wasmi`) is presented in the unified institution: a **signature** (its named
feature signature `nsig S` inside the core's 3.0 signature, `Versions.Named`, or the WasmFX
signature `sigFX`) and, for each of its configurations, a **model** of that signature. The
models are the unified core's Core 3.0 model (`Silmaril.Wasm.Unified.Core30.model30`), its
reducts and its step-relation variants (`Versions.Run`, `Versions.FX`). Every model takes the
frame `f` code runs in and a validation `okc` of decoded code as parameters.

* `at30`: **Core 3.0** at a Core point; `coreSAt S`: **Core 3.0 restricted to `S`** (the
  charts `core|S`), its reduct to `nsig S`;
* `v10At`, `v20At`, `lime1At`: **Wasm 1.0, 2.0 and Lime1**: the reduct to the version's
  signature of Core 3.0 at the configuration's Core image (the point maps of
  `v10Emb`/`v20Emb`/`lime1Emb`). The versions' *own* semantics (silmaril's 1.0, 2.0 and Lime1
  machines) enter through the existing call-level embeddings
  (`Silmaril.Wasm.Models.V10.v10_core_obs`, `V2Core.obs_sub`, `Lime1Core.obs_sub`): running
  universal code in an own semantics needs opcode algebras over the own syntaxes, which are not
  built (`docs/projects/wasm-wasi.md`);
* `fxModelAt`: **WasmFX** (CoreFX reduction, with the FX function table of the point);
* `looseModelAt`, `wasmiModelAt`: **the loose model** and **wasmi 2.0.0**;
* `Presented A`: a chart of the Atlas presented in the unified institution (a signature and a
  model per point); `Presents PA PB T h`: the Atlas transition `T` is presented by the
  signature inclusion `h`: the reduct of the model of the image point is the model of the
  point; `PresentsLE`: the same up to refinement. `Thms` presents the transitions of the
  version embeddings, of feature restriction, of profiles and of the loose model, and shows that
  presentation composes along paths: **the Atlas charts of the versions are a sub-diagram of the
  unified institution**;
* the presentations: `pV10`, `pV20`, `pV20own`, `pLime1`, `pCoreR`, `pCoreV`, `pCore`, `pFX`,
  `pLoose`, `pWasmi`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## The version models -/

/-- **Core 3.0** at a Core point, with frame `f` and validation `okc` (the core's
`model30`). -/
def at30 (P : Profile) (f : Frame) (okc : List Instr → Prop) (x : Core.Pt H) :
    Model UIn UObs Core30.sig30 :=
  Core30.model30 P x.2 x.1 f okc

/-- **Core 3.0 restricted to `S`**: the reduct of `at30` to the named signature of `S`. -/
def coreSAt (S : FeatureSet) (P : Profile) (f : Frame) (okc : List Instr → Prop)
    (x : Core.Pt H) : Model UIn UObs (nsig S) :=
  (at30 P f okc x).reduct (FSig.incl (nsig_sub30 S))

/-- **Wasm 1.0** at a configuration of the own 1.0 model: the 1.0 reduct of Core 3.0 at its
Core image. -/
def v10At (f : Frame) (okc : List Instr → Prop) (p : V10.Pt H) : Model UIn UObs n10 :=
  coreSAt v10 Profile.spec f okc (V2Core.ptCore (V10.ptV2 p))

/-- **Wasm 2.0** at a configuration of the own 2.0 model. -/
def v20At (P : Profile) (f : Frame) (okc : List Instr → Prop) (p : V2Core.Pt H) :
    Model UIn UObs n20 :=
  coreSAt v20 P f okc (V2Core.ptCore p)

/-- **Lime1** at a configuration of the own Lime1 model. -/
def lime1At (f : Frame) (okc : List Instr → Prop) (p : Lime1Core.Pt H) :
    Model UIn UObs nLime1 :=
  coreSAt lime1 Profile.spec f okc (Lime1Core.ptCore p)

/-- **WasmFX** at a CoreFX point (store, host, FX function table). -/
def fxModelAt (P : Profile) (f : Frame) (okc : List FX.InstrFX → Prop) (x : FX.Pt H) :
    Model UIn UObs sigFX :=
  fxModelN P x.2.1 x.1 x.2.2 f okc

/-- **The loose model** (Core 3.0 syntax). -/
def looseModelAt (P : Profile) (f : Frame) (okc : List Instr → Prop) (x : Core.Pt H) :
    Model UIn UObs Core30.sig30 :=
  looseR P x.2 x.1 f okc

/-- **wasmi 2.0.0**, on the named wasmi signature. -/
def wasmiModelAt (P : Profile) (f : Frame) (okc : List Instr → Prop) (x : Core.Pt H) :
    Model UIn UObs nWasmi :=
  (wasmiR P x.2 x.1 f okc).reduct (FSig.incl (nsig_sub30 wasmi200))

/-! ## Presenting Atlas charts -/

/-- A chart of the Atlas **presented** in the unified institution: a signature and a model of it
for every point. -/
structure Presented (A : Chart.{0, 0}) where
  /-- The signature. -/
  K : FSig
  /-- The model of a point. -/
  model : A.Pt → Model UIn UObs K

/-- An Atlas transition is **presented** by a signature inclusion: on the domain, the reduct of
the model of the image point is the model of the point. -/
def Presents {A B : Chart.{0, 0}} (PA : Presented A) (PB : Presented B) (T : Transition A B)
    (h : FSig.Sub PA.K PB.K) : Prop :=
  ∀ p, A.dom p → (PB.model (T.pt p)).reduct (FSig.incl h) = PA.model p

/-- An Atlas transition is presented **up to refinement**: the model of the point refines the
reduct of the model of the image point. -/
def PresentsLE {A B : Chart.{0, 0}} (PA : Presented A) (PB : Presented B) (T : Transition A B)
    (h : FSig.Sub PA.K PB.K) : Prop :=
  ∀ p, A.dom p → Refines (PA.model p) ((PB.model (T.pt p)).reduct (FSig.incl h))

/-- The own 1.0 chart. -/
def pV10 (f : Frame) (okc : List Instr → Prop) : Presented (V10.v10own H).chart :=
  ⟨n10, v10At f okc⟩

/-- The own 2.0 chart, read back (`v10Trans`'s target). -/
def pV20 (f : Frame) (okc : List Instr → Prop) :
    Presented ((V2Core.v20own Profile.spec H).viewChart some) :=
  ⟨n20, v20At Profile.spec f okc⟩

/-- The own 2.0 chart at profile `P`. -/
def pV20own (P : Profile) (f : Frame) (okc : List Instr → Prop) :
    Presented (V2Core.v20own P H).chart :=
  ⟨n20, v20At P f okc⟩

/-- The own Lime1 chart. -/
def pLime1 (f : Frame) (okc : List Instr → Prop) : Presented (Lime1Core.lime1own H).chart :=
  ⟨nLime1, lime1At f okc⟩

/-- The chart `core|S` (`Silmaril.Wasm.Models.coreR`). -/
def pCoreR (S : FeatureSet) (P : Profile) (f : Frame) (okc : List Instr → Prop) :
    Presented (coreR P H S) :=
  ⟨nsig S, coreSAt S P f okc⟩

/-- The model `core|S`, read back (the target of `v20Trans`, `lime1Trans`). -/
def pCoreV (S : FeatureSet) (P : Profile) (f : Frame) (okc : List Instr → Prop) :
    Presented ((coreModel P H S).viewChart some) :=
  ⟨nsig S, coreSAt S P f okc⟩

/-- The model `core|S` (the source of `fxTrans`). -/
def pCoreM (S : FeatureSet) (P : Profile) (f : Frame) (okc : List Instr → Prop) :
    Presented (coreModel P H S).chart :=
  ⟨nsig S, coreSAt S P f okc⟩

/-- The Core chart, over the 3.0 signature. -/
def pCore (P : Profile) (f : Frame) (okc : List Instr → Prop) : Presented (Core.chart P H) :=
  ⟨Core30.sig30, at30 P f okc⟩

/-- The CoreFX model, read back (the target of `fxTrans`). -/
def pFX (P : Profile) (f : Frame) (okc : List FX.InstrFX → Prop) :
    Presented ((FX.fxModel P H).viewChart some) :=
  ⟨sigFX, fxModelAt P f okc⟩

/-- The loose chart. -/
def pLoose (P : Profile) (f : Frame) (okc : List Instr → Prop) :
    Presented (Wasmi.looseChart P H) :=
  ⟨Core30.sig30, looseModelAt P f okc⟩

/-- The wasmi chart. -/
def pWasmi (P : Profile) (f : Frame) (okc : List Instr → Prop) : Presented (Wasmi.chart P H) :=
  ⟨nWasmi, wasmiModelAt P f okc⟩

end Silmaril.Wasm.Unified.Versions
