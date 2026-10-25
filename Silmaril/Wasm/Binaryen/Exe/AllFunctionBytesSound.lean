module

public import Silmaril.Wasm.Binaryen.Exe.AllFunctionBytes
public import Silmaril.Wasm.Binaryen.ArbitraryProfileAllFunctions
public import Silmaril.Wasm.Binaryen.Exe.TrapGrowCleanupSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics Optimization

/-- Successful full-registry cleanup retains the meanings and validity of the
original and output bytes, with exact closed-host export-session equivalence
at every same numerical profile. No determinism premise is used. -/
theorem cleanupAllFunctionBytes_sound_hostState {H : Type}
    {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : cleanupAllFunctionBytes rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  apply cleanupTransformBytes_sound_hostState (H := H) accepted P
  intro m valid
  exact ArbitraryProfile.cleanupAllFunctions_iterate_sound (H := H) P rounds valid

/-- Compatibility specialization to the original empty host-state type. -/
theorem cleanupAllFunctionBytes_sound {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : cleanupAllFunctionBytes rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  cleanupAllFunctionBytes_sound_hostState (H := Empty) accepted P

/-- The existing feasible-refinement policy composes with all function stages. -/
theorem optimizeAllFunctionModeBytes_sound_hostState {H : Type}
    {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeAllFunctionModeBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeModeBytesUsing_sound_hostState (H := H)
    (cleanupAllFunctionBytes_sound_hostState (H := H)) accepted nd r

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeAllFunctionModeBytes_sound {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeAllFunctionModeBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeAllFunctionModeBytes_sound_hostState (H := Empty) accepted nd r

/-- The existing trap-insertion guard and refinement selector retain their
respective contracts when composed with the larger exact pipeline. -/
theorem optimizeAllFunctionTrapGrowBytes_sound_hostState {H : Type}
    {options : TrapGrowOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeAllFunctionTrapGrowBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_sound_hostState (H := H)
    (cleanupAllFunctionBytes_sound_hostState (H := H)) accepted nd r

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeAllFunctionTrapGrowBytes_sound {options : TrapGrowOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeAllFunctionTrapGrowBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeAllFunctionTrapGrowBytes_sound_hostState (H := Empty) accepted nd r

/-- With the insertion-only guard enabled, the same-profile certificate holds
for every numerical profile, not only specification profiles. -/
theorem optimizeAllFunctionTrapGrowBytes_enabled_sound_hostState {H : Type}
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeAllFunctionTrapGrowBytes options input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_enabled_sound_hostState (H := H)
    (cleanupAllFunctionBytes_sound_hostState (H := H)) enabled accepted P

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeAllFunctionTrapGrowBytes_enabled_sound
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeAllFunctionTrapGrowBytes options input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeAllFunctionTrapGrowBytes_enabled_sound_hostState (H := Empty) enabled accepted P

/-- Choosing a weaker mode alone does not weaken the available exact contract. -/
theorem optimizeAllFunctionModeBytes_exact_hostState {H : Type}
    {mode : Mode} {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeAllFunctionModeBytes ⟨mode, rounds, false⟩ input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  rw [optimizeAllFunctionModeBytes, optimizeModeBytesUsing_no_growth] at accepted
  exact cleanupAllFunctionBytes_sound_hostState (H := H) accepted P

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeAllFunctionModeBytes_exact {mode : Mode} {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeAllFunctionModeBytes ⟨mode, rounds, false⟩ input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  optimizeAllFunctionModeBytes_exact_hostState (H := Empty) accepted P

end Silmaril.Wasm.Binaryen.Exe
