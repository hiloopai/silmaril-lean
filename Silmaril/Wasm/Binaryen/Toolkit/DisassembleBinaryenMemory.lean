module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleAtomic
public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Decode
public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.Render

/-! # Binaryen memory-proposal disassembly

The previous Core/shared/atomic route runs first. Array backing and explicit memory order have a
separate retained AST, original-byte grammar and canonical text grammar.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

structure MemoryDisassembledArtifact where
  module : Wasm.Extensions.BinaryenMemory.Module
  text : String
  deriving Repr

def disassembleBinaryenMemoryBytes (bytes : ByteArray) : Except String MemoryDisassembledArtifact := do
  let m ← (Binary.Extensions.BinaryenMemory.Decode.decodeModule bytes).mapError ("wasm-dis: " ++ ·)
  let tree ← match Text.Extensions.BinaryenMemory.moduleSyntax? m with
    | none => .error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => .ok tree
  let text ← match renderWatDocument? tree with
    | none => .error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
    | some text => .ok text
  pure ⟨m, text⟩

inductive ProposalDisassembly where
  | full (artifact : FullDisassembly)
  | memory (artifact : MemoryDisassembledArtifact)

def ProposalDisassembly.text : ProposalDisassembly → String
  | .full a => a.text
  | .memory a => a.text

/-- Preserve every previous Core/shared successful result exactly. -/
def disassembleProposalBytes (bytes : ByteArray) : Except String ProposalDisassembly :=
  match disassembleFullBytes bytes with
  | .ok a => .ok (.full a)
  | .error _ => (disassembleBinaryenMemoryBytes bytes).map .memory

theorem disassembleProposalBytes_of_full {bytes : ByteArray} {a : FullDisassembly}
    (h : disassembleFullBytes bytes = .ok a) :
    disassembleProposalBytes bytes = .ok (.full a) := by
  simp [disassembleProposalBytes, h]

end Silmaril.Wasm.Binaryen.Toolkit
