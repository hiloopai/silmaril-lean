module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleExtended
public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleCompatSound
public import Silmaril.Wasm.Binary.Extensions.SharedMemory.DecodeSound
public import Silmaril.Wasm.Text.Extensions.SharedMemory.RenderSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Original extension binary bytes and emitted text retain the same complete
module, including flags of all retained memory imports and definitions. This certifies syntax, not concurrency or
Core validity. -/
theorem disassembleExtendedBytes_sound {bytes : ByteArray} {a : ExtendedDisassembledArtifact}
    (h : disassembleExtendedBytes bytes = .ok a) :
    Binary.Extensions.SharedMemory.Encodes bytes.data.toList a.module ∧
      Text.Extensions.SharedMemory.Encodes a.text a.module := by
  unfold disassembleExtendedBytes at h
  obtain ⟨m, hm, h⟩ := Exe.bind_ok h
  have decoded : Binary.Extensions.SharedMemory.Decode.decodeModule bytes = .ok m := by
    cases hd : Binary.Extensions.SharedMemory.Decode.decodeModule bytes with
    | error e => rw [hd] at hm; cases hm
    | ok result => rw [hd] at hm; cases hm; rfl
  change (match Text.Extensions.SharedMemory.moduleSyntax? m with
    | none => Except.error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => match renderWatDocument? tree with
      | none => Except.error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
      | some text => Except.ok (ExtendedDisassembledArtifact.mk m text)) = .ok a at h
  cases hs : Text.Extensions.SharedMemory.moduleSyntax? m with
  | none => rw [hs] at h; cases h
  | some tree =>
    simp only [hs] at h
    cases hr : renderWatDocument? tree with
    | none => rw [hr] at h; cases h
    | some text =>
      rw [hr] at h
      cases h
      exact ⟨Binary.Extensions.SharedMemory.Decode.decodeModule_sound decoded,
        ⟨tree, renderWatDocument?_sound hr, Text.Extensions.SharedMemory.moduleSyntax?_sound hs⟩⟩

def SupportedDisassembly.Certifies (bytes : ByteArray) : SupportedDisassembly → Prop
  | .core a => Binary.Core.CompactImports.Encodes bytes.data.toList a.module ∧ Text.Core.Encodes a.text a.module
  | .extended a => Binary.Extensions.SharedMemory.Encodes bytes.data.toList a.module ∧
      Text.Extensions.SharedMemory.Encodes a.text a.module

/-- The result selects its explicit grammar contract; the extended case is
never mislabeled as a Core certificate. -/
theorem disassembleSupportedBytes_sound {bytes : ByteArray} {a : SupportedDisassembly}
    (h : disassembleSupportedBytes bytes = .ok a) : a.Certifies bytes := by
  unfold disassembleSupportedBytes at h
  cases hc : disassembleCompatBytes bytes with
  | ok old =>
    rw [hc] at h
    cases h
    exact disassembleCompatBytes_sound hc
  | error e =>
    rw [hc] at h
    cases he : disassembleExtendedBytes bytes with
    | error e => rw [he] at h; cases h
    | ok ext =>
      rw [he] at h
      cases h
      exact disassembleExtendedBytes_sound he

end Silmaril.Wasm.Binaryen.Toolkit
