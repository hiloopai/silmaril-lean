module

public import Silmaril.Wasm.Binaryen.Toolkit.MergeSource
public import Silmaril.Wasm.Binaryen.Toolkit.AsBinaryenSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def MergeSourceArtifact.Certifies (input : ByteArray) : MergeSourceArtifact → Prop
  | .binary bytes => input = bytes
  | .text source artifact =>
      String.fromUTF8? input = some source ∧
      (Text.Core.Encodes source artifact.module ∨
        Text.Extensions.BinaryenMacros.Encodes source artifact.module) ∧
      Validation.ModuleValid artifact.module ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.module

/-- Every accepted text input retains a checked original-source derivation;
binary inputs are retained byte-for-byte. -/
theorem prepareMergeSource_sound {input : ByteArray} {a : MergeSourceArtifact}
    (accepted : prepareMergeSource input = .ok a) : a.Certifies input := by
  unfold prepareMergeSource at accepted
  split at accepted
  · cases Except.ok.inj accepted
    rfl
  · cases utf8 : String.fromUTF8? input with
    | none => simp only [utf8] at accepted; cases accepted
    | some source =>
        simp only [utf8] at accepted
        obtain ⟨source', sourceEq, accepted⟩ := Exe.bind_ok accepted
        cases Except.ok.inj sourceEq
        obtain ⟨artifact, assembled, accepted⟩ := Exe.bind_ok accepted
        cases Except.ok.inj accepted
        exact ⟨utf8, assembleBinaryenText_sound assembled⟩

end Silmaril.Wasm.Binaryen.Toolkit
