module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleCompat
public import Silmaril.Wasm.Binary.Core.CompactImportsDecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Original standard-or-compact binary bytes and emitted WAT denote the same
complete Core module. The input grammar explicitly includes import grouping;
this is not a claim that the extension's bytes are standard Core encodings. -/
theorem disassembleCompatBytes_sound {bytes : ByteArray} {artifact : DisassembledArtifact}
    (h : disassembleCompatBytes bytes = .ok artifact) :
    Binary.Core.CompactImports.Encodes bytes.data.toList artifact.module ∧
      Text.Core.Encodes artifact.text artifact.module := by
  unfold disassembleCompatBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : Binary.Core.CompactImports.Decode.decodeModule bytes = .ok m := by
    cases hd : Binary.Core.CompactImports.Decode.decodeModule bytes with
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
      exact ⟨Binary.Core.CompactImports.Decode.decodeModule_sound decoded,
        ⟨tree, renderWatDocument?_sound hr, Wat.moduleSyntax?_sound hs⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
