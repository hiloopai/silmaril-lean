module

public import Silmaril.Wasm.Text.Extensions.AtomicMemory.Instructions
public import Silmaril.Wasm.Text.Extensions.Structured.RenderInstructions

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.AtomicMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Wasm.Extensions.AtomicMemory Binaryen.Toolkit

def atomicSyntax? : AtomicInstr → Option (List SExp)
  | .access op memory arg => do
    let index ← Wat.indexSyntax? memory
    let args ← Wat.memoryArgSyntax? arg
    pure (K op.mnemonic :: index :: args)
  | .fence => some [K "atomic.fence"]
  | .pause => some [K "pause"]

def leafSyntax? (I : Core.IdCtx) : Leaf → Option (List SExp)
  | .core i => Wat.instructionSyntaxAt? I i
  | .atomic i => atomicSyntax? i

def instructionTree? := Structured.instructionTree? leafSyntax?

end Silmaril.Wasm.Text.Extensions.AtomicMemory
