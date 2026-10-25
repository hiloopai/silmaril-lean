module

public import Silmaril.Wasm.Binaryen.Toolkit.Disassemble
public import Silmaril.Wasm.Binary.Core.CompactImportsDecode

@[expose] public section

/-! # Disassembly with the compact-imports binary extension

The original `disassembleBytes` keeps its standard-Core input contract. This
additive endpoint recognizes the existing, independently specified compact-import
grouping extension and constructs canonical text for the same complete module.
No re-encoding or upstream normalization replaces the original input bytes.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- The compact-import decoder extends ordinary Core import encodings without
changing module meaning. All other decoder and renderer boundaries remain. -/
def disassembleCompatBytes (bytes : ByteArray) : Except String DisassembledArtifact := do
  let m ← (Binary.Core.CompactImports.Decode.decodeModule bytes).mapError ("wasm-dis: " ++ ·)
  let tree ← match Wat.moduleSyntax? m with
    | none => .error "wasm-dis: module is outside the certified canonical WAT fragment"
    | some tree => .ok tree
  let text ← match renderWatDocument? tree with
    | none => .error "wasm-dis: canonical WAT needs an unsupported lexical representation"
    | some text => .ok text
  pure ⟨m, text⟩

end Silmaril.Wasm.Binaryen.Toolkit
