module

public import Silmaril.Wasm.Unified.Component.Abi30.Defs
public import Silmaril.Wasm.Unified.Core30Faithful.Thms
public import Silmaril.Wasm.Unified.Versions.Thms

/-!
# The Wasm models at the component boundary: results

* `obs_abi`: the observations of `M.abi A` are the answers of the observations of `M` on the
  input of the payload. `abi_reduct`: `Model.abi` commutes with reducts (definitionally), so
  `coreSemV_reduct`: the core semantics of a reduct is the pulled-back core semantics.
* `obs_core30`: **Core 3.0 at the component boundary**: the one-export module of an encoded
  Core 3.0 program answers a flat call exactly with the `abi30` answers of silmaril's Core 3.0
  behaviours of the program on the corresponding numeric arguments (`obs_single`,
  `Core30.obs_encCode`).
* **The embeddings at the component level**: `v10Emb_comp`, `lime1Emb_comp`, `coreEmb_comp`: the
  core semantics of the 1.0 (Lime1, `core|S`) model is the pull-back of the 2.0 (3.0, `core|T`)
  model's along the signature inclusion; `v10_denU`: a component over 1.0 modules means, in the
  1.0 model, what the same component with its modules included into 2.0 means in the 2.0
  model at the embedded point (`denU_mapComp`).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (Flat Payload CoreSem Comp)
open Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Versions

variable {In B : Type} {S S' : FSig}

/-- The observations of a model through a calling convention. -/
theorem obs_abi (A : Abi In B) (M : Model In B S) (c : S.Code) (p : Payload) :
    (M.abi A).obs (c, p) = {r | ∃ i, A.arg p = some i ∧ ∃ b ∈ M.obs (c, i), A.ret b = some r} := by
  ext r
  constructor
  · rintro ⟨hok, i, hi, b, hb, hr⟩
    exact ⟨i, hi, b, ⟨hok, hb⟩, hr⟩
  · rintro ⟨i, hi, b, ⟨hok, hb⟩, hr⟩
    exact ⟨hok, i, hi, b, hb, hr⟩

/-- `Model.abi` commutes with reducts. -/
theorem abi_reduct (A : Abi In B) (σ : S ⟶ S') (M : Model In B S') :
    (M.reduct σ).abi A = (M.abi A).reduct σ := rfl

/-- The core semantics of a reduct of a Wasm model is the pulled-back core semantics. -/
theorem coreSemV_reduct (σ : S ⟶ S') (M : Model (List Val) (Behaviour Val) S') :
    coreSemV (M.reduct σ) = pullC (coreSemV M) σ := by
  rw [coreSemV, abi_reduct, coreSem_reduct]

/-- **Core 3.0 at the component boundary.** -/
theorem obs_core30 (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (is : List Instr) (xs : List Flat) :
    obs ((Core30.model30 P host s f okc).abi abi30)
        (.core (UMod.single (Core30.encCode is)), 0, .flat xs) =
      {r | okc is ∧ ∃ b ∈ Core30.behCode P host s f is (xs.map flatVal), abi30.ret b = some r} := by
  rw [obs_single, obs_abi]
  ext r
  constructor
  · rintro ⟨i, hi, b, hb, hr⟩
    have hi' : i = xs.map flatVal := (Option.some.inj hi).symm
    rw [hi', Core30.obs_encCode] at hb
    exact ⟨hb.1, b, hb.2, hr⟩
  · rintro ⟨hok, b, hb, hr⟩
    refine ⟨xs.map flatVal, rfl, b, ?_, hr⟩
    rw [Core30.obs_encCode]
    exact ⟨hok, hb⟩

/-! ## The embeddings at the component level -/

variable {H : Type} (f : Frame) (okc : List Instr → Prop)

/-- `v10Emb` at the component level. -/
theorem v10Emb_comp (p : V10.Pt H) :
    coreSemV (v10At f okc p) =
      pullC (coreSemV (v20At Profile.spec f okc ((V10.v10Emb H).pt p))) (FSig.incl nsub_10_20) := by
  rw [← v10Emb_reduct, coreSemV_reduct]

/-- `lime1Emb` at the component level. -/
theorem lime1Emb_comp (p : Lime1Core.Pt H) :
    coreSemV (lime1At f okc p) =
      pullC (coreSemV (coreSAt v30 Profile.spec f okc ((Lime1Core.lime1Emb H).pt p)))
        (FSig.incl nsub_lime1_30) := by
  rw [← lime1Emb_reduct, coreSemV_reduct]

/-- `coreEmb` at the component level. -/
theorem coreEmb_comp (P : Profile) {S T : FeatureSet} (h : S ≤ T) (x : Core.Pt H) :
    coreSemV (coreSAt S P f okc x) =
      pullC (coreSemV (coreSAt T P f okc ((coreEmb P H h).pt x))) (FSig.incl (nsig_sub h)) := by
  rw [← coreEmb_reduct, coreSemV_reduct]

/-- **A 1.0 component is a 2.0 component**: its meaning in the 1.0 model is the meaning of the
same component, modules included into 2.0, in the 2.0 model at the embedded point. -/
theorem v10_denU (p : V10.Pt H) (c : Comp (UMod n10)) :
    c.denU (coreSemV (v10At f okc p)) =
      (mapComp (FSig.incl nsub_10_20) c).denU
        (coreSemV (v20At Profile.spec f okc ((V10.v10Emb H).pt p))) := by
  rw [denU_mapComp, v10Emb_comp]

end Silmaril.Wasm.Unified.Component
