module

public import Silmaril.Wasm.Text.Extensions.SharedMemory.Types
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.SharedMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

def memoryTypeSyntax? (m : MemoryType) : Option (List SExp) := do
  let xs ← Wat.memoryTypeSyntax? m.core
  if m.shared then
    if m.core.limits.max.isSome then pure (xs ++ [K "shared"]) else none
  else pure xs

def memorySyntax? (m : MemoryType) : Option SExp := do
  pure (L (K "memory" :: (← memoryTypeSyntax? m)))

end Silmaril.Wasm.Text.Extensions.SharedMemory
