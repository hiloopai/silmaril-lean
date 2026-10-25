module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleBinaryenMemory
public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode
public import Silmaril.Wasm.Text.Extensions.LegacyExceptions.Render

/-! # Legacy exception-aware disassembly

The previous Core/shared/atomic/memory-proposal route runs first. Legacy exception bodies have a
separate retained AST, original-byte grammar and canonical text grammar.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

structure LegacyDisassembledArtifact where
  module : Wasm.Extensions.LegacyExceptions.Module
  text : String
  deriving Repr

def disassembleLegacyBytes (bytes : ByteArray) : Except String LegacyDisassembledArtifact := do
  let m ← (Binary.Extensions.LegacyExceptions.Decode.decodeModule bytes).mapError ("wasm-dis: " ++ ·)
  let tree ← match Text.Extensions.LegacyExceptions.moduleSyntax? m with
    | none => .error "wasm-dis: extension module is outside the certified canonical WAT fragment"
    | some tree => .ok tree
  let text ← match renderWatDocument? tree with
    | none => .error "wasm-dis: canonical extension WAT needs an unsupported lexical representation"
    | some text => .ok text
  pure ⟨m, text⟩

inductive ToolkitDisassembly where
  | previous (artifact : ProposalDisassembly)
  | legacy (artifact : LegacyDisassembledArtifact)

def ToolkitDisassembly.text : ToolkitDisassembly → String
  | .previous a => a.text
  | .legacy a => a.text

/-- Preserve every previous Core/shared successful result exactly. -/
def disassembleToolkitBytes (bytes : ByteArray) : Except String ToolkitDisassembly :=
  match disassembleProposalBytes bytes with
  | .ok a => .ok (.previous a)
  | .error _ => (disassembleLegacyBytes bytes).map .legacy

theorem disassembleToolkitBytes_of_previous {bytes : ByteArray} {a : ProposalDisassembly}
    (h : disassembleProposalBytes bytes = .ok a) :
    disassembleToolkitBytes bytes = .ok (.previous a) := by
  simp [disassembleToolkitBytes, h]

end Silmaril.Wasm.Binaryen.Toolkit
