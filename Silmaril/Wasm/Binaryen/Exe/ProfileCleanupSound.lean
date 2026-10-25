module

public import Silmaril.Wasm.Binaryen.Exe.ProfileCleanup
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binaryen.Exe.DCESound
public import Silmaril.Wasm.Binaryen.ArbitraryProfileWithDirectize

/-! The `*_hostState` certificates quantify over any host-state type under
`closedHost`. This widens the state parameter only; it does not admit host calls,
reentrancy or external state mutation. Existing theorem names retain their
original `Empty` signatures as compatibility specializations. -/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics

/-- Runtime/proof separation changes no stage, order, guard or fallback. -/
theorem profileCleanupRound_eq :
    profileCleanupRound = ArbitraryProfile.cleanupWithDirectize := by
  funext m
  simp only [profileCleanupRound, Dce.dceChecked_eq,
    ArbitraryProfile.cleanupWithDirectize, ArbitraryProfile.cleanupWithGlobals,
    ArbitraryProfile.cleanupWithGuards, ArbitraryProfile.cleanupWithSelect,
    ArbitraryProfile.extendedCleanup, ArbitraryProfile.cleanupWithTee,
    ArbitraryProfile.localCleanupWithTee, ArbitraryProfile.localCleanup]

/-- Compose an exact module-transform certificate through the shared byte
boundary. The transform must preserve validity and the same profile. -/
theorem cleanupTransformBytes_sound_hostState {H : Type}
    {transform : BModule → BModule} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (h : cleanupTransformBytes transform input = .ok artifact) (P : Profile)
    (sound : ∀ {m : BModule}, m.Ok → (transform m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (transform m).lower m.lower) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
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
        simpa only [BModule.Ok, checkedLift_lower] using (show ∃ t, Validation.ModuleOk source t from ⟨mt, hv⟩)
      have hs := sound liftedOk
      refine ⟨Binary.Core.Decode.decodeModule_sound decoded, ⟨mt, hv⟩,
        ?_, hs.1, ?_⟩
      · simpa using encodeModule?_sound encoded
      · simpa only [checkedLift_lower] using hs.2

/-- Compatibility specialization to the original empty host-state type. -/
theorem cleanupTransformBytes_sound {transform : BModule → BModule} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (h : cleanupTransformBytes transform input = .ok artifact) (P : Profile)
    (sound : ∀ {m : BModule}, m.Ok → (transform m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := Empty)) (transform m).lower m.lower) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  cleanupTransformBytes_sound_hostState (H := Empty) h P sound

/-- Every success preserves exact closed-host export behavior at an arbitrary
numerical profile, including divergence and repeated calls. Both original and
output bytes denote retained valid modules. No round-trip assumption, untrusted
decoder flag or determinism premise is used. IO/native compilation are separate. -/
theorem cleanupBytes_sound_hostState {H : Type}
    {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (h : cleanupBytes rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := H)) artifact.result artifact.source := by
  apply cleanupTransformBytes_sound_hostState (H := H) h P
  intro m valid
  simpa only [profileCleanupRound_eq] using
    ArbitraryProfile.cleanupWithDirectize_iterate_sound (H := H) P rounds valid

/-- Compatibility specialization to the original empty host-state type. -/
theorem cleanupBytes_sound {rounds : Nat} {input : ByteArray}
    {artifact : ProfileCleanupArtifact}
    (h : cleanupBytes rounds input = .ok artifact) (P : Profile) :
    Binary.Core.Encodes input.data.toList artifact.source ∧
    Validation.ModuleValid artifact.source ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.result ∧
    Validation.ModuleValid artifact.result ∧
    ExportEquiv (· = ·) P (closedHost (H := Empty)) artifact.result artifact.source :=
  cleanupBytes_sound_hostState (H := Empty) h P

end Silmaril.Wasm.Binaryen.Exe
