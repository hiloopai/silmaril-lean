module

public import Silmaril.Wasm.Binaryen.Exe.ModeCleanup
public import Silmaril.Wasm.Binaryen.Exe.ProfileCleanupSound
public import Silmaril.Wasm.Binaryen.Exe.CoalesceCleanupSound
public import Silmaril.Wasm.Binaryen.GrowWrapperPass

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics Optimization

/-- The runtime growth selector has exactly the registered mode certificate.
Specification profiles permit growth failure, including for zero growth; no
determinism premise is needed. Exact mode cannot select this rewrite. -/
theorem selectedGrowth_sound_hostState {H : Type}
    (options : ModeCleanupOptions)
    (allowed : options.check = .ok ()) (enabled : options.selectGrowthFailure = true)
    (nd : Bool) (r : RelaxedChoice)
    {m : BModule} (valid : m.Ok) :
    (GrowWrapper.optimize m).Ok ∧
      Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := H))
        m.lower (GrowWrapper.optimize m).lower := by
  cases options with
  | mk mode rounds select =>
    cases mode with
    | equivalence =>
      cases select
      · cases enabled
      · cases allowed
    | refinement =>
      exact ⟨(GrowWrapper.refinementP (H := H) nd r).inv_run valid,
        (GrowWrapper.refinementP (H := H) nd r).sound valid⟩
    | trapInsertion =>
      exact ⟨(GrowWrapper.modeP (H := H) .trapInsertion nd r).inv_run valid,
        (GrowWrapper.modeP (H := H) .trapInsertion nd r).sound valid⟩

/-- Compatibility specialization to the original empty host-state type. -/
theorem selectedGrowth_sound (options : ModeCleanupOptions)
    (allowed : options.check = .ok ()) (enabled : options.selectGrowthFailure = true)
    (nd : Bool) (r : RelaxedChoice)
    {m : BModule} (valid : m.Ok) :
    (GrowWrapper.optimize m).Ok ∧
      Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := Empty))
        m.lower (GrowWrapper.optimize m).lower :=
  selectedGrowth_sound_hostState (H := Empty) options allowed enabled nd r valid

/-- Successful byte optimization certifies both original/output modules and
the selected feasible correctness policy. This covers every specification
profile's numerical/relaxed choices, without numerical determinism. It proves
neither file IO nor native compiler correctness. -/
theorem optimizeModeBytesUsing_sound_hostState {H : Type}
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source)
    {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeModeBytesUsing cleanup options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result := by
  unfold optimizeModeBytesUsing at accepted
  obtain ⟨checked, allowed, accepted⟩ := bind_ok accepted
  cases checked
  obtain ⟨clean, cleaned, accepted⟩ := bind_ok accepted
  have hs := sound cleaned (Profile.spec nd r)
  split at accepted
  · rename_i enabled
    obtain ⟨bytes, encoded, accepted⟩ := bind_ok accepted
    cases Except.ok.inj accepted
    have liftedValid : (checkedLift clean.result).1.Ok := by
      simpa only [BModule.Ok, checkedLift_lower, Validation.ModuleValid] using hs.2.2.2.1
    have hg := selectedGrowth_sound_hostState (H := H) options allowed enabled nd r liftedValid
    refine ⟨hs.1, hs.2.1, ?_, hg.1, ?_⟩
    · simpa using encodeModule?_sound encoded
    · exact (Modes.ExportCorrect.of_equiv options.mode hs.2.2.2.2).trans
        (by simpa only [checkedLift_lower] using hg.2)
  · cases Except.ok.inj accepted
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
      Modes.ExportCorrect.of_equiv options.mode hs.2.2.2.2⟩

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeModeBytesUsing_sound
    {cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact}
    (sound : ∀ {rounds : Nat} {input : ByteArray} {artifact : ProfileCleanupArtifact},
      cleanup rounds input = .ok artifact → ∀ P : Profile,
      Binary.Core.Encodes input.data.toList artifact.source ∧
      Validation.ModuleValid artifact.source ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
      Validation.ModuleValid artifact.result ∧
      ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source)
    {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeModeBytesUsing cleanup options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeModeBytesUsing_sound_hostState (H := Empty) sound accepted nd r

/-- The original twelve-stage byte driver retains its selected-mode contract. -/
theorem optimizeModeBytes_sound_hostState {H : Type}
    {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeModeBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeModeBytesUsing_sound_hostState (H := H)
    (cleanupBytes_sound_hostState (H := H)) accepted nd r

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeModeBytes_sound {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeModeBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeModeBytes_sound_hostState (H := Empty) accepted nd r

/-- The larger thirteen-stage driver has the same mode contract and profile
boundary; no numerical determinism is introduced by the added dead-store pass. -/
theorem optimizeCoalesceModeBytes_sound_hostState {H : Type}
    {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeCoalesceModeBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := H))
      artifact.source artifact.result :=
  optimizeModeBytesUsing_sound_hostState (H := H)
    (cleanupCoalesceBytes_sound_hostState (H := H)) accepted nd r

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeCoalesceModeBytes_sound {options : ModeCleanupOptions} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeCoalesceModeBytes options input = .ok artifact)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    Modes.ExportCorrect options.mode (Profile.spec nd r) (closedHost (H := Empty))
      artifact.source artifact.result :=
  optimizeCoalesceModeBytes_sound_hostState (H := Empty) accepted nd r

/-- Without growth selection, the exact arbitrary-profile theorem remains
available even when the user requested a weaker policy. -/
theorem optimizeModeBytes_exact_hostState {H : Type}
    {mode : Mode} {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeModeBytes ⟨mode, rounds, false⟩ input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  rw [optimizeModeBytes_no_growth] at accepted
  exact cleanupBytes_sound_hostState (H := H) accepted P

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeModeBytes_exact {mode : Mode} {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeModeBytes ⟨mode, rounds, false⟩ input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  optimizeModeBytes_exact_hostState (H := Empty) accepted P

/-- Without growth selection, thirteen-stage modes retain exact equivalence at
every arbitrary numerical profile, not just the specification profiles. -/
theorem optimizeCoalesceModeBytes_exact_hostState {H : Type}
    {mode : Mode} {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeCoalesceModeBytes ⟨mode, rounds, false⟩ input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  rw [optimizeCoalesceModeBytes, optimizeModeBytesUsing_no_growth] at accepted
  exact cleanupCoalesceBytes_sound_hostState (H := H) accepted P

/-- Compatibility specialization to the original empty host-state type. -/
theorem optimizeCoalesceModeBytes_exact {mode : Mode} {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (accepted : optimizeCoalesceModeBytes ⟨mode, rounds, false⟩ input = .ok artifact)
    (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  optimizeCoalesceModeBytes_exact_hostState (H := Empty) accepted P

end Silmaril.Wasm.Binaryen.Exe
