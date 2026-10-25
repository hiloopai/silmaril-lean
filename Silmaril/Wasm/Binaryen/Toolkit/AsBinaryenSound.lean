module

public import Silmaril.Wasm.Binaryen.Toolkit.AsBinaryen
public import Silmaril.Wasm.Binaryen.Toolkit.AsSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Existing Core assembly successes, including the artifact, are preserved. -/
theorem assembleBinaryenText_of_core {input : String} {artifact : AssembledArtifact}
    (h : assembleText input = .ok artifact) :
    assembleBinaryenText input = .ok artifact := by
  simp [assembleBinaryenText, h]

/-- The original source is certified either directly by Core WAT or by the
independent source-macro grammar. Both routes emit the same validated Core
module in the existing Core binary grammar. -/
theorem assembleBinaryenText_sound {input : String} {artifact : AssembledArtifact}
    (h : assembleBinaryenText input = .ok artifact) :
    (Text.Core.Encodes input artifact.module ∨
      Text.Extensions.BinaryenMacros.Encodes input artifact.module) ∧
    Validation.ModuleValid artifact.module ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.module := by
  cases original : assembleText input with
  | ok a =>
      simp only [assembleBinaryenText, original] at h
      cases h
      obtain ⟨ht, hv, hb⟩ := assembleText_sound original
      exact ⟨.inl ht, hv, hb⟩
  | error originalError =>
      cases lexical : Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 input with
      | none => simp [assembleBinaryenText, original, lexical] at h
      | some tree =>
          cases parsed : checkBinaryenSource tree with
          | error error => simp [assembleBinaryenText, original, lexical, parsed] at h
          | ok result =>
              simp only [assembleBinaryenText, original, lexical, parsed] at h
              obtain ⟨bytes, hbytes, h⟩ := Exe.bind_ok h
              cases h
              exact ⟨.inr ⟨tree, Formats.SExpEncoding.Wat.sexpWat_of_fullExec lexical,
                  result.source⟩,
                result.valid, by simpa using Exe.encodeModule?_sound hbytes⟩

end Silmaril.Wasm.Binaryen.Toolkit
