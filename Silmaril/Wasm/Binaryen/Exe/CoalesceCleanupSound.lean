module

public import Silmaril.Wasm.Binaryen.Exe.CoalesceCleanup
public import Silmaril.Wasm.Binaryen.Exe.ProfileCleanupSound
public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithCoalesce

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics

theorem profileCleanupCoalesceRound_eq :
    profileCleanupCoalesceRound = ArbitraryProfile.cleanupWithCoalesce := by
  funext m
  simp only [profileCleanupCoalesceRound, profileCleanupRound_eq,
    ArbitraryProfile.cleanupWithCoalesce]

/-- The larger byte pipeline retains original/output correspondence, both module
validities and exact closed-host observations at every same arbitrary profile. -/
theorem cleanupCoalesceBytes_sound_hostState {H : Type}
    {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (h : cleanupCoalesceBytes rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  apply cleanupTransformBytes_sound_hostState (H := H) h P
  intro m valid
  simpa only [profileCleanupCoalesceRound_eq] using
    ArbitraryProfile.cleanupWithCoalesce_iterate_sound (H := H) P rounds valid

/-- Compatibility specialization to the original empty host-state type. -/
theorem cleanupCoalesceBytes_sound {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (h : cleanupCoalesceBytes rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  cleanupCoalesceBytes_sound_hostState (H := Empty) h P

end Silmaril.Wasm.Binaryen.Exe
