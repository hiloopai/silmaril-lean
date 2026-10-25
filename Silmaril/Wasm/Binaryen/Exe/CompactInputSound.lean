module

public import Silmaril.Wasm.Binaryen.Exe.CompactInput
public import Silmaril.Wasm.Binary.Core.CompactImportsDecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe.CompactInput

/-- Exact original extension bytes and prepared standard bytes denote the same
complete module. This does not identify the extension with standard Core bytes. -/
theorem prepare_sound {input : ByteArray} {prepared : Prepared}
    (accepted : prepare input = .ok prepared) :
    Binary.Core.CompactImports.Encodes input.data.toList prepared.source ∧
      Binary.Core.Encodes prepared.bytes.data.toList prepared.source := by
  unfold prepare at accepted
  cases decoded : Binary.Core.Decode.decodeModule input with
  | ok source =>
    simp only [decoded] at accepted
    cases Except.ok.inj accepted
    exact ⟨Binary.Core.CompactImports.of_standard (Binary.Core.Decode.decodeModule_sound decoded),
      Binary.Core.Decode.decodeModule_sound decoded⟩
  | error error =>
    simp only [decoded] at accepted
    obtain ⟨source, decodedCompact, accepted⟩ := bind_ok accepted
    obtain ⟨encoded, encodedSource, accepted⟩ := bind_ok accepted
    cases Except.ok.inj accepted
    exact ⟨Binary.Core.CompactImports.Decode.decodeModule_sound decodedCompact,
      by simpa using encodeModule?_sound encodedSource⟩

/-- Lift an existing actual byte driver's full contract unchanged. Its input
witness and the preparation witness prove complete source identity; every
property in `Q` (including mode, profile, output validity and semantics) is retained. -/
theorem optimizeUsing_sound
    {driver : ByteArray → Except String ProfileCleanupArtifact}
    {Q : ProfileCleanupArtifact → Prop}
    (sound : ∀ {input : ByteArray} {artifact : ProfileCleanupArtifact},
      driver input = .ok artifact →
      Binary.Core.Encodes input.data.toList artifact.source ∧ Q artifact)
    {input : ByteArray} {artifact : ProfileCleanupArtifact}
    (accepted : optimizeUsing driver input = .ok artifact) :
    Binary.Core.CompactImports.Encodes input.data.toList artifact.source ∧ Q artifact := by
  obtain ⟨prepared, preparedInput, ran⟩ := bind_ok accepted
  have inputMeaning := prepare_sound preparedInput
  have result := sound ran
  have sameSource := Binary.Core.functional inputMeaning.2 result.1
  exact ⟨sameSource ▸ inputMeaning.1, result.2⟩

end Silmaril.Wasm.Binaryen.Exe.CompactInput
