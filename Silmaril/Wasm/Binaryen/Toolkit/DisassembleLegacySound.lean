module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleLegacy
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleBinaryenMemorySound
public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.DecodeSound
public import Silmaril.Wasm.Text.Extensions.LegacyExceptions.RenderSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Original extension binary bytes and emitted text retain the same complete
module, including complete legacy try/catch/delegate bodies. This certifies syntax, not concurrency or
Core validity. -/
theorem disassembleLegacyBytes_sound {bytes : ByteArray} {a : LegacyDisassembledArtifact}
    (h : disassembleLegacyBytes bytes = .ok a) :
    Binary.Extensions.LegacyExceptions.Encodes bytes.data.toList a.module ∧
      Text.Extensions.LegacyExceptions.Encodes a.text a.module := by
  unfold disassembleLegacyBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : Binary.Extensions.LegacyExceptions.Decode.decodeModule bytes = .ok m := by
    cases hd : Binary.Extensions.LegacyExceptions.Decode.decodeModule bytes with
    | error e => rw [hd] at hm; cases hm
    | ok result => rw [hd] at hm; cases hm; rfl
  change (match Text.Extensions.LegacyExceptions.moduleSyntax? m with
    | none => Except.error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => match renderWatDocument? tree with
      | none => Except.error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
      | some text => Except.ok (LegacyDisassembledArtifact.mk m text)) = .ok a at h
  cases hs : Text.Extensions.LegacyExceptions.moduleSyntax? m with
  | none => rw [hs] at h; cases h
  | some tree =>
    simp only [hs] at h
    cases hr : renderWatDocument? tree with
    | none => rw [hr] at h; cases h
    | some text =>
      rw [hr] at h
      cases h
      exact ⟨Binary.Extensions.LegacyExceptions.Decode.decodeModule_sound decoded,
        ⟨tree, renderWatDocument?_sound hr, Text.Extensions.LegacyExceptions.moduleSyntax?_sound hs⟩⟩

def ToolkitDisassembly.Certifies (bytes : ByteArray) : ToolkitDisassembly → Prop
  | .previous a => a.Certifies bytes
  | .legacy a => Binary.Extensions.LegacyExceptions.Encodes bytes.data.toList a.module ∧
      Text.Extensions.LegacyExceptions.Encodes a.text a.module

/-- Every success selects the retained AST's explicit grammar contract. -/
theorem disassembleToolkitBytes_sound {bytes : ByteArray} {a : ToolkitDisassembly}
    (h : disassembleToolkitBytes bytes = .ok a) : a.Certifies bytes := by
  unfold disassembleToolkitBytes at h
  cases hc : disassembleProposalBytes bytes with
  | ok old =>
    rw [hc] at h
    cases h
    exact disassembleProposalBytes_sound hc
  | error e =>
    rw [hc] at h
    cases he : disassembleLegacyBytes bytes with
    | error e => rw [he] at h; cases h
    | ok ext =>
      rw [he] at h
      cases h
      exact disassembleLegacyBytes_sound he

end Silmaril.Wasm.Binaryen.Toolkit
