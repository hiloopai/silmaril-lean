module

public import Silmaril.Wasm.Logic.Iris.Heap.Defs

/-!
# The Iris logic of Wasm Core 3.0: auxiliary definitions for the rules

`growOk t size n` says that `memory.grow` by `n` pages can succeed on a memory of
type `t` with `size` bytes (silmaril-lean's `MemInst.grow?` returns a memory), and
`growType t size n` is the memory type afterwards; both depend only on the type
and the size, which is what the cell `ILoc.mem` records.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

/-- `memory.grow` by `n` pages can succeed on a memory of type `t` and `size` bytes. -/
abbrev growOk (t : MemoryType) (size n : Nat) : Prop :=
  size / Memory.pageSize + n ≤ 2 ^ (t.address.width - 16) ∧
    ∀ j, t.limits.max = some j → size / Memory.pageSize + n ≤ j.val

/-- The memory type after growing a memory of type `t` and `size` bytes by `n` pages. -/
abbrev growType (t : MemoryType) (size n : Nat) : MemoryType :=
  { t with limits := { t.limits with min := Fin.ofNat _ (size / Memory.pageSize + n) } }

end Silmaril.Wasm.Logic.IrisWasm
