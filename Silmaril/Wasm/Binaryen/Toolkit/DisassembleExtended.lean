module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleCompat
public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Decode
public import Silmaril.Wasm.Text.Extensions.SharedMemory.Render

/-! # Explicit extension-aware disassembly

Shared memories are retained in a distinct artifact and carry extension grammar
certificates. The dispatcher first runs the existing Core/compact endpoint, so
every existing successful Core result follows exactly its original code path.
No projected shared module is passed to the Core validator or optimizer.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

structure ExtendedDisassembledArtifact where
  module : Wasm.Extensions.SharedMemory.Module
  text : String
  deriving Repr

def disassembleExtendedBytes (bytes : ByteArray) : Except String ExtendedDisassembledArtifact := do
  let m ← (Binary.Extensions.SharedMemory.Decode.decodeModule bytes).mapError ("wasm-dis: " ++ ·)
  let tree ← match Text.Extensions.SharedMemory.moduleSyntax? m with
    | none => .error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => .ok tree
  let text ← match renderWatDocument? tree with
    | none => .error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
    | some text => .ok text
  pure ⟨m, text⟩

inductive SupportedDisassembly where
  | core (artifact : DisassembledArtifact)
  | extended (artifact : ExtendedDisassembledArtifact)

def SupportedDisassembly.text : SupportedDisassembly → String
  | .core a => a.text
  | .extended a => a.text

/-- Old-Core-first routing preserves every previous successful result. -/
def disassembleSupportedBytes (bytes : ByteArray) : Except String SupportedDisassembly :=
  match disassembleCompatBytes bytes with
  | .ok a => .ok (.core a)
  | .error _ => (disassembleExtendedBytes bytes).map .extended

theorem disassembleSupportedBytes_of_core {bytes : ByteArray} {a : DisassembledArtifact}
    (h : disassembleCompatBytes bytes = .ok a) :
    disassembleSupportedBytes bytes = .ok (.core a) := by
  simp [disassembleSupportedBytes, h]

end Silmaril.Wasm.Binaryen.Toolkit
