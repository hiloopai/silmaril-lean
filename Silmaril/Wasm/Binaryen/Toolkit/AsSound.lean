module

public import Silmaril.Wasm.Binaryen.Toolkit.As
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Accepted original WAT text and emitted binary both denote the artifact's
same validated module in the existing formal text and binary grammars. The
candidate parser is justified by the original-source grammar certificate, and contributes
no additional correctness assumption. File IO is outside this pure theorem. -/
theorem assembleText_sound {input : String} {artifact : AssembledArtifact}
    (h : assembleText input = .ok artifact) :
    Text.Core.Encodes input artifact.module ∧ Validation.ModuleValid artifact.module ∧
      Binary.Core.Encodes artifact.bytes.data.toList artifact.module := by
  cases lexical : Formats.SExpEncoding.Wat.sexpWatByteExec? .core3 input with
  | none => simp [assembleText, lexical] at h
  | some tree =>
    cases canonical : Wat.parseSupported? tree with
    | none => simp [assembleText, lexical, canonical] at h
    | some m =>
      cases validated : Validation.validate? m with
      | none => simp [assembleText, lexical, canonical, validated] at h
      | some mt =>
        simp only [assembleText, lexical, canonical, validated] at h
        obtain ⟨bytes, hbytes, h⟩ := Exe.bind_ok h
        cases h
        exact ⟨⟨tree, Formats.SExpEncoding.Wat.sexpWat_of_byteExec lexical,
            Wat.parseSupported?_sound canonical⟩,
          ⟨mt, Validation.validate?_sound validated⟩,
          by simpa using Exe.encodeModule?_sound hbytes⟩

end Silmaril.Wasm.Binaryen.Toolkit
