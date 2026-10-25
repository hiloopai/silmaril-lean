module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleAtomic
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleExtendedSound
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.DecodeSound
public import Silmaril.Wasm.Text.Extensions.AtomicMemory.RenderSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Original extension binary bytes and emitted text retain the same complete
module, including standard atomic operations and shared memories. This certifies syntax, not concurrency or
Core validity. -/
theorem disassembleAtomicBytes_sound {bytes : ByteArray} {a : AtomicDisassembledArtifact}
    (h : disassembleAtomicBytes bytes = .ok a) :
    Binary.Extensions.AtomicMemory.Encodes bytes.data.toList a.module ∧
      Text.Extensions.AtomicMemory.Encodes a.text a.module := by
  unfold disassembleAtomicBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : Binary.Extensions.AtomicMemory.Decode.decodeModule bytes = .ok m := by
    cases hd : Binary.Extensions.AtomicMemory.Decode.decodeModule bytes with
    | error e => rw [hd] at hm; cases hm
    | ok result => rw [hd] at hm; cases hm; rfl
  change (match Text.Extensions.AtomicMemory.moduleSyntax? m with
    | none => Except.error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => match renderWatDocument? tree with
      | none => Except.error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
      | some text => Except.ok (AtomicDisassembledArtifact.mk m text)) = .ok a at h
  cases hs : Text.Extensions.AtomicMemory.moduleSyntax? m with
  | none => rw [hs] at h; cases h
  | some tree =>
    simp only [hs] at h
    cases hr : renderWatDocument? tree with
    | none => rw [hr] at h; cases h
    | some text =>
      rw [hr] at h
      cases h
      exact ⟨Binary.Extensions.AtomicMemory.Decode.decodeModule_sound decoded,
        ⟨tree, renderWatDocument?_sound hr, Text.Extensions.AtomicMemory.moduleSyntax?_sound hs⟩⟩

def FullDisassembly.Certifies (bytes : ByteArray) : FullDisassembly → Prop
  | .supported a => a.Certifies bytes
  | .atomic a => Binary.Extensions.AtomicMemory.Encodes bytes.data.toList a.module ∧
      Text.Extensions.AtomicMemory.Encodes a.text a.module

/-- Every success selects the retained AST's explicit grammar contract. -/
theorem disassembleFullBytes_sound {bytes : ByteArray} {a : FullDisassembly}
    (h : disassembleFullBytes bytes = .ok a) : a.Certifies bytes := by
  unfold disassembleFullBytes at h
  cases hc : disassembleSupportedBytes bytes with
  | ok old =>
    rw [hc] at h
    cases h
    exact disassembleSupportedBytes_sound hc
  | error e =>
    rw [hc] at h
    cases he : disassembleAtomicBytes bytes with
    | error e => rw [he] at h; cases h
    | ok ext =>
      rw [he] at h
      cases h
      exact disassembleAtomicBytes_sound he

end Silmaril.Wasm.Binaryen.Toolkit
