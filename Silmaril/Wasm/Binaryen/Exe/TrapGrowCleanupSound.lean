module

public import Silmaril.Wasm.Binaryen.Exe.TrapGrowCleanup
public import Silmaril.Wasm.Binaryen.Exe.ModeCleanupSound
public import Silmaril.Wasm.Binaryen.GrowOOMLiteralPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics Optimization

theorem TrapGrowOptions.check_enabled {options : TrapGrowOptions}
    (enabled : options.trapGrowthFailure = true) (checked : options.check = .ok ()) :
    options.base.mode = .trapInsertion ∧ options.base.selectGrowthFailure = false := by
  cases options with
  | mk base flag =>
    cases flag
    · cases enabled
    · cases base with
      | mk mode rounds select =>
        cases mode <;> cases select <;>
          simp_all [TrapGrowOptions.check, ModeCleanupOptions.check, bind, Except.bind]

/-- A supplied exact byte-cleanup certificate composes with the actual inserted
OOM guard. This theorem retains every same profile, not just spec/deterministic
profiles. Successful bytes denote valid retained source and output modules. -/
theorem optimizeTrapGrowBytesUsing_enabled_sound_hostState {H : Type}
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source)
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeTrapGrowBytesUsing cleanup options input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := H))
      artifact.source artifact.result := by
  unfold optimizeTrapGrowBytesUsing at accepted
  rw [enabled] at accepted
  simp only [↓reduceIte] at accepted
  obtain ⟨checked, allowed, accepted⟩ := bind_ok accepted
  cases checked
  obtain ⟨clean, cleaned, accepted⟩ := bind_ok accepted
  obtain ⟨bytes, encoded, accepted⟩ := bind_ok accepted
  cases Except.ok.inj accepted
  have hs := sound cleaned P
  have mode := (TrapGrowOptions.check_enabled enabled allowed).1
  have valid : (checkedLift clean.result).1.Ok := by
    simpa only [BModule.Ok, checkedLift_lower, Validation.ModuleValid] using hs.2.2.2.1
  have guarded := (GrowOOMLiteral.trapInsertionP (H := H) P).sound valid
  change Modes.ExportCorrect .trapInsertion P closedHost (checkedLift clean.result).1.lower
    (GrowOOMLiteral.optimize (checkedLift clean.result).1).lower at guarded
  refine ⟨hs.1, hs.2.1, ?_, ?_, ?_⟩
  · simpa using encodeModule?_sound encoded
  · exact (GrowOOMLiteral.trapInsertionP (H := H) P).inv_run valid
  · rw [mode]
    exact (Modes.ExportCorrect.of_equiv .trapInsertion hs.2.2.2.2).trans
      (by simpa only [checkedLift_lower] using guarded)

/-- Compatibility specialization to an empty host-state type. -/
theorem optimizeTrapGrowBytesUsing_enabled_sound
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source)
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (enabled : options.trapGrowthFailure = true)
    (accepted : optimizeTrapGrowBytesUsing cleanup options input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode P (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_enabled_sound_hostState (H := Empty) sound enabled accepted P

/-- Uniform CLI-facing certificate over any closed-host state type, also
preserving the specification profile certificate when the additive guard is
disabled. -/
theorem optimizeTrapGrowBytesUsing_sound_hostState {H : Type}
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source)
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeTrapGrowBytesUsing cleanup options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result := by
  cases enabled : options.trapGrowthFailure with
  | false =>
    have previous : optimizeModeBytesUsing cleanup options.base input = .ok artifact := by
      simpa only [optimizeTrapGrowBytesUsing, enabled, Bool.false_eq_true, ↓reduceIte] using accepted
    exact optimizeModeBytesUsing_sound_hostState (H := H) sound previous nd r
  | true =>
    exact optimizeTrapGrowBytesUsing_enabled_sound_hostState (H := H)
      sound enabled accepted (Profile.spec nd r)

/-- Compatibility specialization to an empty host-state type. -/
theorem optimizeTrapGrowBytesUsing_sound
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source)
    {options : TrapGrowOptions} {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeTrapGrowBytesUsing cleanup options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_sound_hostState (H := Empty) sound accepted nd r

theorem optimizeTrapGrowBytes_sound_hostState {H : Type}
    {options : TrapGrowOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeTrapGrowBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_sound_hostState (H := H)
    cleanupBytes_sound_hostState accepted nd r

/-- Compatibility specialization to an empty host-state type. -/
theorem optimizeTrapGrowBytes_sound {options : TrapGrowOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeTrapGrowBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeTrapGrowBytes_sound_hostState (H := Empty) accepted nd r

theorem optimizeCoalesceTrapGrowBytes_sound_hostState {H : Type}
    {options : TrapGrowOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeCoalesceTrapGrowBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeTrapGrowBytesUsing_sound_hostState (H := H)
    cleanupCoalesceBytes_sound_hostState accepted nd r

/-- Compatibility specialization to an empty host-state type. -/
theorem optimizeCoalesceTrapGrowBytes_sound {options : TrapGrowOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeCoalesceTrapGrowBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.base.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeCoalesceTrapGrowBytes_sound_hostState (H := Empty) accepted nd r

end Silmaril.Wasm.Binaryen.Exe
