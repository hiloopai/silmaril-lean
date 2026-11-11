module

public import Silmaril.Wasm.Binaryen.Pipeline.Defs
public import Silmaril.Wasm.Binaryen.NeutralOps.Thms
public import Silmaril.Wasm.Binaryen.EqzPair.Thms
public import Silmaril.Wasm.Binaryen.RseLine.Thms
public import Silmaril.Wasm.Binaryen.DropGet.Thms
public import Silmaril.Wasm.Binaryen.TeeForm.Thms
public import Silmaril.Wasm.Binaryen.SsaStage.Thms
public import Silmaril.Wasm.Binaryen.Exe.PipelineSound
public import Silmaril.Wasm.Binaryen.Exe.SelectedCleanupSound
public import Silmaril.Wasm.Binaryen.Exe.CompactInputSound

@[expose] public section

/-! # Soundness of the verified-stage pipelines, through silmaril's pass API

Kept apart from `Pipeline/Defs.lean` so that the executable does not import
`Inline.lean` (through `Exe.PipelineSound`).

* **Executable contract.** Each verified stage is `Exe.guardedP` of its
  `Exe.StageOk` certificate (`ExtraStageId.stageOk`). A round is
  `Pass.pipeline (functionPassesP ++ extraPassesP)`, and the pipeline is the
  product `inlineP budget * extraRoundP ^ rounds * rumeP` in the pass monoid.
  `extraPipelineP_run` identifies its run function with the executable
  `extraPipelineWith`; `extra_pipeline_sound` is the analogue of silmaril's
  `Exe.pipeline_sound`, obtained from `Pass.sound` with no composition proof.
* **The selected-stage driver.** Each selectable stage is an
  `ArbitraryProfile.EquivPass` (silmaril's `selectedValidStageP`, the verified stages'
  `ExtraStageId.equivP` or `ExtraStageId.detP`). `extraSelectedCompatBytes_sound`
  is the byte-level theorem of `wasm-opt` for selections of every-profile
  stages: the input bytes encode a valid module, the output bytes encode a valid
  module, and the two are exactly export-equivalent at every numerical profile
  under the closed host. Every verified stage is an every-profile stage, so
  `extraSelectedCompatBytes_sound_exact` states the same for every selection;
  `extraSelectedCompatBytes_sound_det` is its deterministic-profile form, through the
  deterministic-profile passes `ExtraStageId.detP`.
* **The `ssa` stage** is the shared pass `SsaStage.ssaP` (exact export equivalence at every
  numerical profile, closed host, `SsaStage.ssaRun_exportEquiv`), so the theorems above
  cover selections containing it. `ssaOnlyCompatBytes_sound` gives, for `--ssa` alone, in
  addition the per-function guarantees `SsaStage.SsaSpec` (fragment equivalence and equal
  Core 3.0 behaviours of the rewritten function's invocations in the allocated stores).
-/

namespace Silmaril.Wasm.Binaryen.Pipeline

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.Exe
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-! ## The executable contract `ExeC` -/

section ExeC

open Silmaril.Wasm.Binaryen.PassAPI

variable (o : GrowKind → Nat → Nat → Nat → Bool) (H : Type)

/-- Each verified-stage transformation has its exact-equivalence certificate. -/
theorem ExtraStageId.stageOk : ∀ stage : ExtraStageId, StageOk o H stage.transform
  | .neutralOps => NeutralOps.neutralOps_stageOk
  | .eqzPair => EqzPair.eqzPair_stageOk
  | .rseLine => RseLine.rseLine_stageOk
  | .dropGet => DropGet.dropGet_stageOk
  | .teeForm => TeeForm.teeForm_stageOk

/-- A verified stage as a guarded pass for `ExeC`. -/
def ExtraStageId.toPass (stage : ExtraStageId) : Pass (ExeC o H) :=
  guardedP stage.transform (stage.stageOk o H)

@[simp] theorem ExtraStageId.toPass_run (stage : ExtraStageId) :
    (stage.toPass o H).run = stage.run :=
  guardedP_run stage.transform (stage.stageOk o H)

def extraPassesP : List (Pass (ExeC o H)) := extraStageIds.map (ExtraStageId.toPass o H)

/-- One round: silmaril's function passes, then the verified stages. -/
def extraRoundP : Pass (ExeC o H) := Pass.pipeline (functionPassesP o H ++ extraPassesP o H)

theorem extraRoundP_runs :
    (functionPassesP o H ++ extraPassesP o H).map Pass.run = extraRoundStages.map Prod.snd := by
  rw [List.map_append, functionPassesP_run, extraRoundStages, List.map_append]
  simp only [extraPassesP, extraFunctionStages, List.map_map, Function.comp_def,
    ExtraStageId.toStage, ExtraStageId.toPass_run]

variable {o H}

/-- **The verified-stage pipeline, as a product in the pass monoid.** -/
def extraPipelineP (hH : H → False) (budget rounds : Nat) : Pass (ExeC o H) :=
  inlineP hH budget * extraRoundP o H ^ rounds * rumeP

theorem extraRoundP_pow_run (rounds : Nat) (m : BModule) :
    (extraRoundP o H ^ rounds).run m =
      runStages (List.replicate rounds extraRoundStages).flatten m := by
  induction rounds generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Pass.mul_run, ih, List.replicate_succ', List.flatten_append,
      List.flatten_singleton, runStages_append]
    exact pipeline_run_stages _ _ (extraRoundP_runs o H) _

/-- **The verified-stage pipeline's run function is the executable one.** -/
theorem extraPipelineP_run (hH : H → False) (budget rounds : Nat) :
    (extraPipelineP (o := o) hH budget rounds).run = extraPipelineWith budget rounds := by
  funext m
  simp only [extraPipelineP, Pass.mul_run, extraRoundP_pow_run, extraPipelineWith,
    extraPipelineStages, List.cons_append]
  simp only [runStages, List.foldl_cons, List.foldl_append, List.foldl_nil, inlineStage,
    rumeStage, inlineP, rumeP, guardedP_run]

/-- **Verified-stage pipeline soundness**, with exactly the premises of silmaril's
`Exe.pipeline_sound`: the result keeps the executable invariant and is
export-equivalent to the input. -/
theorem extra_pipeline_sound {m : BModule} (hp : m.inProfile = true) (hok : m.Ok)
    (hty : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, profileValType t = true)
    (rounds : Nat) (hH : H → False) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (extraPipeline rounds m).lower m.lower ∧ ExeInv (extraPipeline rounds m) := by
  have hm : ExeInv m := ⟨profileOk_of_inProfile hp (typesInProfile_complete fun st hst ft hft t ht =>
      sigValType_of_profileValType (hty st hst ft hft t ht)), hok⟩
  have h₁ := (extraPipelineP (o := o) hH inlineBudget rounds).sound hm
  have h₂ := (extraPipelineP (o := o) hH inlineBudget rounds).inv_run hm
  rw [extraPipelineP_run] at h₁ h₂
  exact ⟨h₁, h₂⟩

end ExeC

/-! ## Every numerical profile: the selected-stage driver -/

section ArbitraryProfile

variable {H : Type}

/-- A certified selection: any shared pass whose run is the selected round gives
validity and exact equivalence for any number of rounds. -/
theorem selected_iterate_of {P : Profile} {stages : List ExtraStage}
    (p : ArbitraryProfile.EquivPass P (closedHost (H := H)))
    (hrun : p.run = extraSelectedRound stages) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    ((extraSelectedRound stages)^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((extraSelectedRound stages)^[rounds] m).lower m.lower := by
  have h := Silmaril.Compile.PassAPI.Pass.pow_run p rounds
  rw [hrun] at h
  have result : ((p ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) ((p ^ rounds).run m).lower m.lower :=
    ⟨(p ^ rounds).inv_run hm, (p ^ rounds).sound hm⟩
  rw [h] at result
  exact result

/-! ### Every numerical profile, for every-profile stages -/

/-- Every-profile verified stages as shared passes at an arbitrary profile. -/
def ExtraStageId.equivP (P : Profile) :
    (stage : ExtraStageId) → stage.anyProfile = true →
      ArbitraryProfile.EquivPass P (closedHost (H := H))
  | .neutralOps, _ => NeutralOps.neutralOpsP P
  | .eqzPair, _ => EqzPair.eqzPairP P
  | .rseLine, _ => RseLine.rseLineP P
  | .dropGet, _ => DropGet.dropGetP P
  | .teeForm, _ => TeeForm.teeFormP P

theorem ExtraStageId.equivP_run (P : Profile) (stage : ExtraStageId) (h : stage.anyProfile = true) :
    (stage.equivP (H := H) P h).run = stage.transform := by
  cases stage <;> rfl

def ExtraStage.equivP (P : Profile) :
    (stage : ExtraStage) → stage.anyProfile = true → ArbitraryProfile.EquivPass P (closedHost (H := H))
  | .silmaril stage, _ => ArbitraryProfile.selectedValidStageP P stage
  | .verified stage, h => stage.equivP P h
  | .ssa, _ => SsaStage.ssaP P

theorem ExtraStage.equivP_run (P : Profile) (stage : ExtraStage) (h : stage.anyProfile = true) :
    (stage.equivP (H := H) P h).run = stage.runValid := by
  cases stage with
  | silmaril stage => exact ArbitraryProfile.selectedValidStageP_run P stage
  | verified stage => exact ExtraStageId.equivP_run P stage h
  | ssa => rfl

/-- A selection of every-profile stages as a product in the pass monoid. -/
def extraSelectedP (P : Profile) :
    (stages : List ExtraStage) → (∀ s ∈ stages, s.anyProfile = true) →
      ArbitraryProfile.EquivPass P (closedHost (H := H))
  | [], _ => 1
  | stage :: stages, h =>
    stage.equivP P (h stage (by simp)) * extraSelectedP P stages (fun s hs => h s (by simp [hs]))

theorem extraSelectedP_run (P : Profile) (stages : List ExtraStage)
    (h : ∀ s ∈ stages, s.anyProfile = true) (m : BModule) :
    (extraSelectedP (H := H) P stages h).run m = extraSelectedRound stages m := by
  induction stages generalizing m with
  | nil => rfl
  | cons stage stages ih =>
    simp only [extraSelectedP, Silmaril.Compile.PassAPI.Pass.mul_run, ExtraStage.equivP_run,
      extraSelectedRound, List.foldl_cons]
    exact ih _ _

/-! ### Every deterministic profile, for every selection -/

/-- Every verified stage as a shared pass at a deterministic profile. -/
def ExtraStageId.detP (o : GrowKind → Nat → Nat → Nat → Bool) :
    ExtraStageId → ArbitraryProfile.EquivPass (Profile.deterministic o) (closedHost (H := H))
  | .neutralOps => NeutralOps.neutralOpsP _
  | .eqzPair => EqzPair.eqzPairP _
  | .rseLine => RseLine.rseLineP _
  | .dropGet => DropGet.dropGetP _
  | .teeForm => TeeForm.teeFormP _

@[simp] theorem ExtraStageId.detP_run (o : GrowKind → Nat → Nat → Nat → Bool) (stage : ExtraStageId) :
    (stage.detP (H := H) o).run = stage.transform := by
  cases stage <;> rfl

def ExtraStage.detP (o : GrowKind → Nat → Nat → Nat → Bool) :
    (stage : ExtraStage) → stage.exact = true →
      ArbitraryProfile.EquivPass (Profile.deterministic o) (closedHost (H := H))
  | .silmaril stage, _ => ArbitraryProfile.selectedValidStageP _ stage
  | .verified stage, _ => stage.detP o
  | .ssa, _ => SsaStage.ssaP _

theorem ExtraStage.detP_run (o : GrowKind → Nat → Nat → Nat → Bool) (stage : ExtraStage)
    (h : stage.exact = true) : (stage.detP (H := H) o h).run = stage.runValid := by
  cases stage with
  | silmaril stage => exact ArbitraryProfile.selectedValidStageP_run _ stage
  | verified stage => exact ExtraStageId.detP_run o stage
  | ssa => rfl

/-- A selection of export-certified stages at a deterministic profile. -/
def extraSelectedDetP (o : GrowKind → Nat → Nat → Nat → Bool) :
    (stages : List ExtraStage) → (∀ s ∈ stages, s.exact = true) →
      ArbitraryProfile.EquivPass (Profile.deterministic o) (closedHost (H := H))
  | [], _ => 1
  | stage :: stages, h =>
    stage.detP o (h stage (by simp)) * extraSelectedDetP o stages (fun s hs => h s (by simp [hs]))

theorem extraSelectedDetP_run (o : GrowKind → Nat → Nat → Nat → Bool) (stages : List ExtraStage)
    (h : ∀ s ∈ stages, s.exact = true) (m : BModule) :
    (extraSelectedDetP (H := H) o stages h).run m = extraSelectedRound stages m := by
  induction stages generalizing m with
  | nil => rfl
  | cons stage stages ih =>
    simp only [extraSelectedDetP, Silmaril.Compile.PassAPI.Pass.mul_run, ExtraStage.detP_run,
      extraSelectedRound, List.foldl_cons]
    exact ih _ _

/-! ### Byte endpoints -/

theorem extraSelectedBytes_sound_of {P : Profile} {stages : List ExtraStage} {rounds : Nat}
    (p : ArbitraryProfile.EquivPass P (closedHost (H := H)))
    (hrun : p.run = extraSelectedRound stages)
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : extraSelectedCompatBytes stages rounds input = .ok artifact) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source :=
  CompactInput.optimizeUsing_sound (fun accepted =>
    cleanupTransformBytes_sound_hostState (H := H) accepted P
      fun valid => selected_iterate_of p hrun rounds valid) accepted

/-- **The `wasm-opt` byte endpoint, every numerical profile**: for a selection
of every-profile stages (all of silmaril's and all verified stages, `ssa` included), the input
bytes (standard or with compact import groups) encode a valid module, the output
bytes encode a valid module, and the output is exactly export-equivalent to the input
at every numerical profile under the closed host. -/
theorem extraSelectedCompatBytes_sound {stages : List ExtraStage} {rounds : Nat}
    (hany : ∀ s ∈ stages, s.anyProfile = true)
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : extraSelectedCompatBytes stages rounds input = .ok artifact) (P : Profile) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source :=
  extraSelectedBytes_sound_of (extraSelectedP P stages hany)
    (funext (extraSelectedP_run P stages hany)) accepted

/-- **The `wasm-opt` byte endpoint, deterministic profiles**: for every
selection, the same conclusion at every
deterministic numerical profile `Profile.deterministic o`. Implied by
`extraSelectedCompatBytes_sound_exact`; kept for the deterministic-profile pass
interface `ExtraStage.detP`. -/
theorem extraSelectedCompatBytes_sound_det {stages : List ExtraStage} {rounds : Nat}
    (hexact : ∀ s ∈ stages, s.exact = true)
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : extraSelectedCompatBytes stages rounds input = .ok artifact)
    (o : GrowKind → Nat → Nat → Nat → Bool) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      artifact.result artifact.source :=
  extraSelectedBytes_sound_of (extraSelectedDetP o stages hexact)
    (funext (extraSelectedDetP_run o stages hexact)) accepted

/-- Every export-certified stage (every stage) is an every-profile stage. -/
theorem ExtraStage.anyProfile_of_exact : ∀ stage : ExtraStage, stage.exact = true →
    stage.anyProfile = true
  | .silmaril _, _ => rfl
  | .verified stage, _ => by cases stage <;> rfl
  | .ssa, _ => rfl

/-- **The `wasm-opt` byte endpoint for every selection, every numerical profile**: the input bytes (standard or with compact import groups) encode a
valid module, the output bytes encode a valid module, and the output is exactly
export-equivalent to the input at every numerical profile under the closed host. -/
theorem extraSelectedCompatBytes_sound_exact {stages : List ExtraStage} {rounds : Nat}
    (hexact : ∀ s ∈ stages, s.exact = true)
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : extraSelectedCompatBytes stages rounds input = .ok artifact) (P : Profile) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source :=
  extraSelectedCompatBytes_sound (fun s hs => s.anyProfile_of_exact (hexact s hs)) accepted P

/-! ### Selections containing the `ssa` stage -/

/-- Every selectable stage keeps validity. -/
theorem ExtraStage.runValid_ok (stage : ExtraStage) {m : BModule} (hm : m.Ok) :
    (stage.runValid m).Ok := by
  cases stage with
  | ssa => exact (SsaStage.ssaRun_spec hm).1
  | silmaril s =>
    have := (ExtraStage.detP_run (H := Empty) (fun _ _ _ _ => true) (.silmaril s) rfl)
    rw [← this]; exact (ExtraStage.detP (H := Empty) _ (.silmaril s) rfl).inv_run hm
  | verified s =>
    have := (ExtraStage.detP_run (H := Empty) (fun _ _ _ _ => true) (.verified s) rfl)
    rw [← this]; exact (ExtraStage.detP (H := Empty) _ (.verified s) rfl).inv_run hm

theorem extraSelectedRound_ok (stages : List ExtraStage) {m : BModule} (hm : m.Ok) :
    (extraSelectedRound stages m).Ok := by
  induction stages generalizing m with
  | nil => exact hm
  | cons stage stages ih => exact ih (stage.runValid_ok hm)

theorem extraSelectedRound_iterate_ok (stages : List ExtraStage) :
    ∀ (rounds : Nat) {m : BModule}, m.Ok → ((extraSelectedRound stages)^[rounds] m).Ok
  | 0, _, hm => hm
  | n + 1, _, hm => extraSelectedRound_iterate_ok stages n (extraSelectedRound_ok stages hm)

/-- The byte boundary with a validity-preserving transform and a per-module property. -/
theorem transformBytes_of {transform : BModule → BModule} {Q : BModule → BModule → Prop}
    (hT : ∀ {m : BModule}, m.Ok → (transform m).Ok ∧ Q m (transform m))
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (h : cleanupTransformBytes transform input = .ok artifact) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ∃ m : BModule, m.lower = artifact.source ∧ m.Ok ∧
      artifact.result = (transform m).lower ∧ Q m (transform m) := by
  unfold cleanupTransformBytes at h
  cases decoded : Binary.Core.Decode.decodeModule input with
  | error e => simp [decoded, Except.mapError, bind, Except.bind] at h
  | ok source =>
    simp only [decoded, Except.mapError, Except.bind, bind] at h
    cases validated : Validation.validate? source with
    | none => simp [validated] at h
    | some mt =>
      simp only [validated] at h
      obtain ⟨bytes, encoded, h⟩ := bind_ok h
      cases Except.ok.inj h
      have hv := Validation.validate?_sound validated
      have liftedOk : (checkedLift source).1.Ok := by
        simpa only [BModule.Ok, checkedLift_lower] using
          (show ∃ t, Validation.ModuleOk source t from ⟨mt, hv⟩)
      have hs := hT liftedOk
      exact ⟨Binary.Core.Decode.decodeModule_sound decoded, ⟨mt, hv⟩,
        by simpa using encodeModule?_sound encoded, hs.1,
        (checkedLift source).1, checkedLift_lower source, liftedOk, rfl, hs.2⟩

/-- **Any selection: validity.** The input bytes encode a valid module and the output
bytes encode a valid module (the semantic statement is `extraSelectedCompatBytes_sound`). -/
theorem extraSelectedCompatBytes_valid {stages : List ExtraStage} {rounds : Nat}
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : extraSelectedCompatBytes stages rounds input = .ok artifact) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result :=
  let r := CompactInput.optimizeUsing_sound (Q := fun a =>
      Validation.ModuleValid a.source ∧ Binary.Core.Encodes a.bytes.data.toList a.result ∧
        Validation.ModuleValid a.result)
    (fun accepted =>
      let t := transformBytes_of (Q := fun _ _ => True)
        (fun hm => ⟨extraSelectedRound_iterate_ok stages rounds hm, trivial⟩) accepted
      ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1⟩) accepted
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩

/-- **`--ssa` alone (one round).** The input bytes encode a valid module `m` (as lifted), the
output bytes encode the valid module `ssaRun m`, which is **exactly export-equivalent** to `m`
at every numerical profile under the closed host (`SsaStage.ssaRun_exportEquiv`), has the same
non-function sections and function count, and every function of it is the original or a
replacement that is fragment-equivalent (`SsaStage.FragEquivAt`) and Core-equivalent on
invocations (`SsaStage.CoreEquivAt`: in the stores silmaril's executable instantiation
allocates for `m` and `ssaRun m`, every typed invocation of it has the same Core 3.0
behaviours, closed host, at every numerical profile, divergence included). -/
theorem ssaOnlyCompatBytes_sound {H : Type} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : extraSelectedCompatBytes [.ssa] 1 input = .ok artifact) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    (∀ P : Profile, ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source) ∧
    ∃ m : BModule, m.lower = artifact.source ∧ m.Ok ∧
      artifact.result = (SsaStage.ssaRun m).lower ∧ SsaStage.SsaSpec m (SsaStage.ssaRun m) := by
  refine CompactInput.optimizeUsing_sound (Q := fun a =>
      Validation.ModuleValid a.source ∧ Binary.Core.Encodes a.bytes.data.toList a.result ∧
        Validation.ModuleValid a.result ∧
        (∀ P : Profile, ExportEquiv (· = ·) P (closedHost (H := H)) a.result a.source) ∧
        ∃ m : BModule, m.lower = a.source ∧ m.Ok ∧
          a.result = (SsaStage.ssaRun m).lower ∧ SsaStage.SsaSpec m (SsaStage.ssaRun m))
    (fun accepted => ?_) accepted
  obtain ⟨e1, v1, e2, v2, m, h1, h2, h3, h4, h5⟩ :=
    transformBytes_of (transform := (extraSelectedRound [.ssa])^[1])
      (Q := fun m m' => m' = SsaStage.ssaRun m ∧ SsaStage.SsaSpec m (SsaStage.ssaRun m))
      (fun hm => ⟨(SsaStage.ssaRun_spec hm).1, rfl, (SsaStage.ssaRun_spec hm).2⟩) accepted
  have hres : _ = (SsaStage.ssaRun m).lower := h3.trans (by rw [h4])
  refine ⟨e1, v1, e2, v2, fun P => ?_, m, h1, h2, hres, h5⟩
  rw [hres, ← h1]
  exact SsaStage.ssaRun_exportEquiv h2 P

end ArbitraryProfile

end Silmaril.Wasm.Binaryen.Pipeline
