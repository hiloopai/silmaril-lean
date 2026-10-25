module

public import Silmaril.Wasm.Binaryen.Exe.SelectedCleanup
public import Silmaril.Wasm.Binaryen.Exe.AllFunctionBytesSound
public import Silmaril.Wasm.Binaryen.Exe.InlineProfileSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- All selectable identifiers are certified at the same arbitrary profile. -/
def selectedStageP (P : Profile) : Exe.CleanupStage → EquivPass P (closedHost (H := H))
  | .function stage => functionStageP P stage
  | .rume => outputGuardedP (rumeP P)
  | .inlining => outputGuardedP (Exe.inlineProfileSharedP P H Exe.inlineBudget Exe.inlineFuel)

@[simp] theorem selectedStageP_run (P : Profile) (stage : Exe.CleanupStage) :
    (selectedStageP (H := H) P stage).run = stage.run := by
  cases stage with
  | function stage => exact functionStageP_run P stage
  | rume => rfl
  | inlining => rfl

def selectedStagesP (P : Profile) : List Exe.CleanupStage → EquivPass P (closedHost (H := H))
  | [] => 1
  | stage :: stages => selectedStageP P stage * selectedStagesP P stages

theorem selectedStagesP_run (P : Profile) (stages : List Exe.CleanupStage) (m : BModule) :
    (selectedStagesP (H := H) P stages).run m = Exe.cleanupSelectedRound stages m := by
  induction stages generalizing m with
  | nil => rfl
  | cons stage stages ih =>
    simp only [selectedStagesP, Silmaril.Compile.PassAPI.Pass.mul_run,
      selectedStageP_run, Exe.cleanupSelectedRound, List.foldl_cons]
    exact ih _

/-- Order, repetition, empty selection and round count impose no new semantic
premises: every actual selected pipeline preserves validity and exact closed-host
admission, initialization and shared-state export observations at the same P. -/
theorem selectedCleanup_iterate_sound (P : Profile) (stages : List Exe.CleanupStage)
    (rounds : Nat) {m : BModule} (hm : m.Ok) :
    ((Exe.cleanupSelectedRound stages)^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((Exe.cleanupSelectedRound stages)^[rounds] m).lower m.lower := by
  have run : (selectedStagesP (H := H) P stages).run = Exe.cleanupSelectedRound stages :=
    funext (selectedStagesP_run P stages)
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (selectedStagesP (H := H) P stages) rounds
  rw [run] at hrun
  have result : ((selectedStagesP (H := H) P stages ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((selectedStagesP (H := H) P stages ^ rounds).run m).lower m.lower :=
    ⟨(selectedStagesP (H := H) P stages ^ rounds).inv_run hm,
      (selectedStagesP (H := H) P stages ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

/-- Validity-only selected stages retain the actual transformations and their
internal checks, without the legacy whole-module guards. Inlining also omits
the unrelated type-section wrapper, using the same certified finite-fuel loop. -/
def selectedValidStageP (P : Profile) : Exe.CleanupStage → EquivPass P (closedHost (H := H))
  | .function stage => functionTransformP P stage
  | .rume => rumeP P
  | .inlining => Exe.inlineValidProfileSharedP P H Exe.inlineBudget Exe.inlineFuel

@[simp] theorem selectedValidStageP_run (P : Profile) (stage : Exe.CleanupStage) :
    (selectedValidStageP (H := H) P stage).run = stage.runValid := by
  cases stage with
  | function stage => exact functionTransformP_run P stage
  | rume => rfl
  | inlining => rfl

def selectedValidStagesP (P : Profile) : List Exe.CleanupStage → EquivPass P (closedHost (H := H))
  | [] => 1
  | stage :: stages => selectedValidStageP P stage * selectedValidStagesP P stages

theorem selectedValidStagesP_run (P : Profile) (stages : List Exe.CleanupStage) (m : BModule) :
    (selectedValidStagesP (H := H) P stages).run m = Exe.cleanupSelectedValidRound stages m := by
  induction stages generalizing m with
  | nil => rfl
  | cons stage stages ih =>
    simp only [selectedValidStagesP, Silmaril.Compile.PassAPI.Pass.mul_run,
      selectedValidStageP_run, Exe.cleanupSelectedValidRound, List.foldl_cons]
    exact ih _

/-- The broader selected pipeline has the same exact closed-host contract at
every numerical profile, with validity as its only module input invariant. -/
theorem selectedValidCleanup_iterate_sound (P : Profile) (stages : List Exe.CleanupStage)
    (rounds : Nat) {m : BModule} (hm : m.Ok) :
    ((Exe.cleanupSelectedValidRound stages)^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((Exe.cleanupSelectedValidRound stages)^[rounds] m).lower m.lower := by
  have run : (selectedValidStagesP (H := H) P stages).run = Exe.cleanupSelectedValidRound stages :=
    funext (selectedValidStagesP_run P stages)
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (selectedValidStagesP (H := H) P stages) rounds
  rw [run] at hrun
  have result : ((selectedValidStagesP (H := H) P stages ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((selectedValidStagesP (H := H) P stages ^ rounds).run m).lower m.lower :=
    ⟨(selectedValidStagesP (H := H) P stages ^ rounds).inv_run hm,
      (selectedValidStagesP (H := H) P stages ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics Optimization

theorem cleanupSelectedBytes_sound_hostState {H : Type}
    {stages : List CleanupStage} {rounds : Nat}
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : cleanupSelectedBytes stages rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  apply cleanupTransformBytes_sound_hostState (H := H) accepted P
  intro m valid
  exact ArbitraryProfile.selectedValidCleanup_iterate_sound (H := H) P stages rounds valid

/-- Compatibility specialization to the original empty host-state type. -/
theorem cleanupSelectedBytes_sound {stages : List CleanupStage} {rounds : Nat}
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : cleanupSelectedBytes stages rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  cleanupSelectedBytes_sound_hostState (H := Empty) accepted P

theorem optimizeSelectedTrapGrowBytes_sound_hostState {H : Type}
    {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedTrapGrowBytes stages options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_sound_hostState (H := H)
    (cleanupSelectedBytes_sound_hostState (H := H)) accepted nd r

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeSelectedTrapGrowBytes_sound {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedTrapGrowBytes stages options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeSelectedTrapGrowBytes_sound_hostState (H := Empty) accepted nd r

theorem optimizeSelectedTrapGrowBytes_enabled_sound_hostState {H : Type}
    {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeSelectedTrapGrowBytes stages options input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_enabled_sound_hostState (H := H)
    (cleanupSelectedBytes_sound_hostState (H := H)) enabled accepted P

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeSelectedTrapGrowBytes_enabled_sound {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeSelectedTrapGrowBytes stages options input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeSelectedTrapGrowBytes_enabled_sound_hostState (H := Empty) enabled accepted P

/-- The default exact route has no weaker-mode or deterministic-profile premise. -/
theorem optimizeSelectedTrapGrowBytes_exact_hostState {H : Type}
    {stages : List CleanupStage} {mode : Mode}
    {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedTrapGrowBytes stages ⟨⟨mode, rounds, false⟩, false⟩ input =
      .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  rw [optimizeSelectedTrapGrowBytes, optimizeTrapGrowBytesUsing_disabled,
    optimizeModeBytesUsing_no_growth] at accepted
  exact cleanupSelectedBytes_sound_hostState (H := H) accepted P

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeSelectedTrapGrowBytes_exact {stages : List CleanupStage} {mode : Mode}
    {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedTrapGrowBytes stages ⟨⟨mode, rounds, false⟩, false⟩ input =
      .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  optimizeSelectedTrapGrowBytes_exact_hostState (H := Empty) accepted P

end Silmaril.Wasm.Binaryen.Exe
