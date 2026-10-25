module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleBinaryenMemory
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleAtomicSound
public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.DecodeSound
public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.RenderSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Original extension binary bytes and emitted text retain the same complete
module, including array backing and explicit atomic memory order. This certifies syntax, not concurrency or
Core validity. -/
theorem disassembleBinaryenMemoryBytes_sound {bytes : ByteArray} {a : MemoryDisassembledArtifact}
    (h : disassembleBinaryenMemoryBytes bytes = .ok a) :
    Binary.Extensions.BinaryenMemory.Encodes bytes.data.toList a.module ∧
      Text.Extensions.BinaryenMemory.Encodes a.text a.module := by
  unfold disassembleBinaryenMemoryBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : Binary.Extensions.BinaryenMemory.Decode.decodeModule bytes = .ok m := by
    cases hd : Binary.Extensions.BinaryenMemory.Decode.decodeModule bytes with
    | error e => rw [hd] at hm; cases hm
    | ok result => rw [hd] at hm; cases hm; rfl
  change (match Text.Extensions.BinaryenMemory.moduleSyntax? m with
    | none => Except.error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => match renderWatDocument? tree with
      | none => Except.error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
      | some text => Except.ok (MemoryDisassembledArtifact.mk m text)) = .ok a at h
  cases hs : Text.Extensions.BinaryenMemory.moduleSyntax? m with
  | none => rw [hs] at h; cases h
  | some tree =>
    simp only [hs] at h
    cases hr : renderWatDocument? tree with
    | none => rw [hr] at h; cases h
    | some text =>
      rw [hr] at h
      cases h
      exact ⟨Binary.Extensions.BinaryenMemory.Decode.decodeModule_sound decoded,
        ⟨tree, renderWatDocument?_sound hr, Text.Extensions.BinaryenMemory.moduleSyntax?_sound hs⟩⟩

def ProposalDisassembly.Certifies (bytes : ByteArray) : ProposalDisassembly → Prop
  | .full a => a.Certifies bytes
  | .memory a => Binary.Extensions.BinaryenMemory.Encodes bytes.data.toList a.module ∧
      Text.Extensions.BinaryenMemory.Encodes a.text a.module

/-- Every success selects the retained AST's explicit grammar contract. -/
theorem disassembleProposalBytes_sound {bytes : ByteArray} {a : ProposalDisassembly}
    (h : disassembleProposalBytes bytes = .ok a) : a.Certifies bytes := by
  unfold disassembleProposalBytes at h
  cases hc : disassembleFullBytes bytes with
  | ok old =>
    rw [hc] at h
    cases h
    exact disassembleFullBytes_sound hc
  | error e =>
    rw [hc] at h
    cases he : disassembleBinaryenMemoryBytes bytes with
    | error e => rw [he] at h; cases h
    | ok ext =>
      rw [he] at h
      cases h
      exact disassembleBinaryenMemoryBytes_sound he

end Silmaril.Wasm.Binaryen.Toolkit
