module

public import Silmaril.Wasm.Binaryen.Toolkit.Disassemble
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound

@[expose] public section

/-! # Specification guarantee for accepted binary-to-WAT disassembly

The original bytes and emitted WAT denote the same Core module under the
independent binary and text specifications. No re-encoding, stripped input,
or unproved general printer is substituted for the original input.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Successful disassembly preserves the exact specified module from the
original binary bytes to the emitted WAT text. -/
theorem disassembleBytes_sound {bytes : ByteArray} {artifact : DisassembledArtifact}
    (h : disassembleBytes bytes = .ok artifact) :
    Binary.Core.Encodes bytes.data.toList artifact.module ∧
      Text.Core.Encodes artifact.text artifact.module := by
  unfold disassembleBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : Binary.Core.Decode.decodeModule bytes = .ok m := by
    cases hd : Binary.Core.Decode.decodeModule bytes with
    | error e => rw [hd] at hm; cases hm
    | ok result => rw [hd] at hm; cases hm; rfl
  change (match Wat.moduleSyntax? m with
    | none => Except.error "wasm-dis: module is outside the certified canonical WAT fragment"
    | some tree => match renderWatDocument? tree with
      | none => Except.error "wasm-dis: canonical WAT needs an unsupported lexical representation"
      | some text => Except.ok (DisassembledArtifact.mk m text)) = .ok artifact at h
  cases hs : Wat.moduleSyntax? m with
  | none => rw [hs] at h; cases h
  | some tree =>
    simp only [hs] at h
    cases hr : renderWatDocument? tree with
    | none => rw [hr] at h; cases h
    | some text =>
      rw [hr] at h
      cases h
      exact ⟨Binary.Core.Decode.decodeModule_sound decoded,
        ⟨tree, renderWatDocument?_sound hr, Wat.moduleSyntax?_sound hs⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
