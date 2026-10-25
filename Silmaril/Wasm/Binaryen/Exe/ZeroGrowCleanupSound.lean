module

public import Silmaril.Wasm.Binaryen.Exe.ZeroGrowCleanup
public import Silmaril.Wasm.Binaryen.Exe.SelectedCleanupSound
public import Silmaril.Wasm.Binaryen.GrowZeroSuccessPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics Optimization

/-- The optional success selector has a refinement certificate, never an exact
one. The standard specification permits successful zero growth; an arbitrary
profile that forbids that success would not justify this rewrite. -/
theorem selectedZeroGrowth_sound_hostState {H : Type}
    (options : TrapGrowOptions)
    (allowed : zeroGrowOptionsCheck options = .ok ()) (nd : Bool) (r : RelaxedChoice)
    {m : BModule} (valid : m.Ok) :
    (GrowZeroSuccess.optimize m).Ok ∧
      Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
        m.lower (GrowZeroSuccess.optimize m).lower := by
  have result := GrowZeroSuccess.optimize_sound (H := H) nd r valid
  cases mode : options.base.mode with
  | equivalence =>
    cases checked : options.check <;>
      simp [zeroGrowOptionsCheck, checked, mode, bind, Except.bind] at allowed
  | refinement => simpa only [mode] using result
  | trapInsertion =>
    exact ⟨result.1, by simpa only [mode] using result.2.refinement_trapInsertion⟩

/-- Compatibility specialization to the original empty host-state type. -/
theorem selectedZeroGrowth_sound (options : TrapGrowOptions)
    (allowed : zeroGrowOptionsCheck options = .ok ()) (nd : Bool) (r : RelaxedChoice)
    {m : BModule} (valid : m.Ok) :
    (GrowZeroSuccess.optimize m).Ok ∧
      Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
        m.lower (GrowZeroSuccess.optimize m).lower :=
  selectedZeroGrowth_sound_hostState (H := Empty) options allowed nd r valid

/-- Original/output byte meanings, validity, admission, persistent session
refinement and feasibility for the actual byte runner. This retains source
nonvacuity instead of deleting every behavior to eliminate a trap. -/
theorem optimizeZeroGrowBytesUsing_sound_hostState {H : Type}
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source)
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeZeroGrowBytesUsing cleanup options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result := by
  unfold optimizeZeroGrowBytesUsing at accepted
  obtain ⟨checked, allowed, accepted⟩ := bind_ok accepted
  cases checked
  obtain ⟨clean, cleaned, accepted⟩ := bind_ok accepted
  obtain ⟨bytes, encoded, accepted⟩ := bind_ok accepted
  cases Except.ok.inj accepted
  have hs := sound cleaned (Profile.spec nd r)
  have valid : (checkedLift clean.result).1.Ok := by
    simpa only [BModule.Ok, checkedLift_lower, Validation.ModuleValid] using hs.2.2.2.1
  have selected := selectedZeroGrowth_sound_hostState (H := H) options allowed nd r valid
  refine ⟨hs.1, hs.2.1, ?_, selected.1, ?_⟩
  · simpa using encodeModule?_sound encoded
  · exact (Modes.ExportCorrect.of_equiv options.base.mode hs.2.2.2.2).trans
      (by simpa only [checkedLift_lower] using selected.2)

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeZeroGrowBytesUsing_sound
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source)
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeZeroGrowBytesUsing cleanup options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeZeroGrowBytesUsing_sound_hostState (H := Empty) sound accepted nd r

/-- Ordered selected cleanup followed by the explicit refinement-only rewrite. -/
theorem optimizeSelectedZeroGrowBytes_sound_hostState {H : Type}
    {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedZeroGrowBytes stages options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeZeroGrowBytesUsing_sound_hostState (H := H)
    (cleanupSelectedBytes_sound_hostState (H := H)) accepted nd r

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeSelectedZeroGrowBytes_sound {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedZeroGrowBytes stages options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeSelectedZeroGrowBytes_sound_hostState (H := Empty) accepted nd r

end Silmaril.Wasm.Binaryen.Exe
