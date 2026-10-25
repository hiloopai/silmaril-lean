module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleExtended
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.Decode
public import Silmaril.Wasm.Text.Extensions.AtomicMemory.Render

/-! # Atomic extension-aware disassembly

The previous Core/shared-memory route runs first. Atomic instructions have a
separate retained AST, original-byte grammar and canonical text grammar.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

structure AtomicDisassembledArtifact where
  module : Wasm.Extensions.AtomicMemory.Module
  text : String
  deriving Repr

def disassembleAtomicBytes (bytes : ByteArray) : Except String AtomicDisassembledArtifact := do
  let m ← (Binary.Extensions.AtomicMemory.Decode.decodeModule bytes).mapError ("wasm-dis: " ++ ·)
  let tree ← match Text.Extensions.AtomicMemory.moduleSyntax? m with
    | none => .error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => .ok tree
  let text ← match renderWatDocument? tree with
    | none => .error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
    | some text => .ok text
  pure ⟨m, text⟩

inductive FullDisassembly where
  | supported (artifact : SupportedDisassembly)
  | atomic (artifact : AtomicDisassembledArtifact)

def FullDisassembly.text : FullDisassembly → String
  | .supported a => a.text
  | .atomic a => a.text

/-- Preserve every previous Core/shared successful result exactly. -/
def disassembleFullBytes (bytes : ByteArray) : Except String FullDisassembly :=
  match disassembleSupportedBytes bytes with
  | .ok a => .ok (.supported a)
  | .error _ => (disassembleAtomicBytes bytes).map .atomic

theorem disassembleFullBytes_of_supported {bytes : ByteArray} {a : SupportedDisassembly}
    (h : disassembleSupportedBytes bytes = .ok a) :
    disassembleFullBytes bytes = .ok (.supported a) := by
  simp [disassembleFullBytes, h]

end Silmaril.Wasm.Binaryen.Toolkit
