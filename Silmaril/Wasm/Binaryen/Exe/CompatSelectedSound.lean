module

public import Silmaril.Wasm.Binaryen.Exe.CompatSelected
public import Silmaril.Wasm.Binaryen.Exe.CompactInputSound
public import Silmaril.Wasm.Binaryen.Exe.ZeroGrowCleanupSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics Optimization

/-- The actual selected CLI endpoint, including original compact-import bytes,
retains all existing specification-profile mode contracts and feasibility. -/
theorem optimizeSelectedCompatBytes_sound {H : Type} {stages : List CleanupStage}
    {options : TrapGrowOptions} {selectZeroGrowSuccess : Bool}
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedCompatBytes stages options selectZeroGrowSuccess input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result := by
  cases selectZeroGrowSuccess with
  | false =>
    exact CompactInput.optimizeUsing_sound
      (fun accepted => optimizeSelectedTrapGrowBytes_sound_hostState (H := H) accepted nd r) accepted
  | true =>
    exact CompactInput.optimizeUsing_sound
      (fun accepted => optimizeSelectedZeroGrowBytes_sound_hostState (H := H) accepted nd r) accepted

/-- With no growth policy, exact same-profile equivalence remains available at
every numerical profile and host-state type, for standard and compact inputs. -/
theorem optimizeSelectedCompatBytes_exact {H : Type} {stages : List CleanupStage}
    {mode : Mode} {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeSelectedCompatBytes stages ⟨⟨mode, rounds, false⟩, false⟩ false input =
      .ok artifact) (P : Profile) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  exact CompactInput.optimizeUsing_sound
    (fun accepted => optimizeSelectedTrapGrowBytes_exact_hostState (H := H) accepted P) accepted

/-- The insertion-only policy keeps its arbitrary-profile certificate. -/
theorem optimizeSelectedCompatBytes_trapInsertion {H : Type} {stages : List CleanupStage}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeSelectedCompatBytes stages options false input = .ok artifact)
    (P : Profile) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := H))
      artifact.source artifact.result := by
  exact CompactInput.optimizeUsing_sound
    (fun accepted => optimizeSelectedTrapGrowBytes_enabled_sound_hostState (H := H) enabled accepted P)
    accepted

end Silmaril.Wasm.Binaryen.Exe
