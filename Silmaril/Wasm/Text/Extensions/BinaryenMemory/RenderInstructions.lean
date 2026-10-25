module

public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.Instructions
public import Silmaril.Wasm.Text.Extensions.AtomicMemory.RenderInstructions

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.BinaryenMemory

open Silmaril Silmaril.Formats.SExpEncoding Binaryen.Toolkit Wasm.Extensions.BinaryenMemory

def leafSyntax? (I : Core.IdCtx) : Wasm.Extensions.BinaryenMemory.Leaf → Option (List SExp)
  | .base i => AtomicMemory.leafSyntax? I i
  | .arrayAccess op type arg => do
    let index ← Wat.indexSyntax? type
    let args ← Wat.memoryArgSyntax? arg
    pure (K op.mnemonic :: L [K "type", index] :: args)
  | .vectorArrayAccess store type arg => do
    let index ← Wat.indexSyntax? type
    let args ← Wat.memoryArgSyntax? arg
    pure (K (if store then "v128.store" else "v128.load") :: L [K "type", index] :: args)
  | .orderedAccess op memory arg order => do
    if !(orderable op) then none else do
      let index ← Wat.indexSyntax? memory
      let args ← Wat.memoryArgSyntax? arg
      pure (K op.mnemonic :: index :: K order.name :: args)
  | .orderedFence order => some [K "atomic.fence", K order.name]

def instructionTree? := Structured.instructionTree? leafSyntax?

end Silmaril.Wasm.Text.Extensions.BinaryenMemory
