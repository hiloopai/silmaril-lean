module

public import Silmaril.Wasm.Extensions.SharedMemory
public import Silmaril.Wasm.Text.Core.Types

/-! # Shared-memory text types

Memory types retain the threads proposal's trailing `shared` keyword. Both the
ordinary and shared cases reuse Core's independent address and limits grammar.
A shared memory in this supported slice must have an explicit maximum.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.SharedMemory

open Silmaril Silmaril.Formats.SExpEncoding
abbrev MemoryType := Wasm.Extensions.SharedMemory.MemoryType

inductive MemTypeT : List SExp → MemoryType → Prop where
  | unshared {xs : List SExp} {m : Wasm.MemoryType} (h : Core.MemTypeT xs m) :
      MemTypeT xs ⟨m, false⟩
  | shared {xs : List SExp} {m : Wasm.MemoryType} (h : Core.MemTypeT xs m)
      (hmax : m.limits.max.isSome = true) : MemTypeT (xs ++ [K "shared"]) ⟨m, true⟩

end Silmaril.Wasm.Text.Extensions.SharedMemory
