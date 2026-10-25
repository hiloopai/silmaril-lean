module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax
public import Silmaril.Wasm.Binaryen.Toolkit.WatRender

@[expose] public section

/-! # Checked binary-to-WAT disassembly

Accepted binary and text are certified against the same actual Core module.
The canonical tree builder determines the supported fragment; unsupported
modules and lexical representations fail explicitly. File IO and the Lean
runtime are outside the pure theorem in `DisassembleSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

structure DisassembledArtifact where
  module : Wasm.Module
  text : String

/-- Decode the original bytes, construct canonical tree, and certify its
rendering. Nothing is emitted for malformed or unsupported input. -/
def disassembleBytes (bytes : ByteArray) : Except String DisassembledArtifact := do
  let m ← (Binary.Core.Decode.decodeModule bytes).mapError ("wasm-dis: " ++ ·)
  let tree ← match Wat.moduleSyntax? m with
    | none => .error "wasm-dis: module is outside the certified canonical WAT fragment"
    | some tree => .ok tree
  let text ← match renderWatDocument? tree with
    | none => .error "wasm-dis: canonical WAT needs an unsupported lexical representation"
    | some text => .ok text
  pure ⟨m, text⟩

end Silmaril.Wasm.Binaryen.Toolkit
