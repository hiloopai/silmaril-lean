module

public import Silmaril.Wasm.Component.Reference.Runtime.Table.Defs

/-!
# Component Model handle tables

An executable transcription of the Canonical ABI `Table` class
(`design/mvp/canonical-abi/definitions.py`, class `Table`, at component-model
revision `a25fc0b`; prose in `CanonicalABI.md`, section "Table State"), generic
in the stored element type so that the same table can later hold resource
handles, waitables, waitable sets, error contexts, subtasks, and threads.

The reference state is a Python list `array` whose slot `0` is a permanent
`None`, plus a list `free` used as a stack (`free.append` / `free.pop()`):

* `get(i)` traps when `i >= len(array)` or `array[i] is None`;
* `add(e)` pops the most recently freed index if there is one (and asserts
  that its slot is empty), and otherwise appends at `i = len(array)` after
  `trap_if(i > Table.MAX_LENGTH)` with `MAX_LENGTH = 2**28 - 1`;
* `remove(i)` is `get(i)` followed by clearing the slot and pushing `i`.

Here `Table.get?`, `Table.add?`, and `Table.remove?` return `none` exactly
when the reference traps. The stack `free` is stored with its top at the head
of the Lean list, so `Table.pythonFree` (the reversal) is the reference list.
The reference `assert(self.array[i] is None)` in `add` is not re-checked:
`Table.WellFormed` (proved invariant in `Table/Properties.lean`) implies it.
The reference `__iter__` is `Table.elements`. Indices are natural numbers;
conversion from the `i32` operands of canonical built-ins is the caller's job.

Note that the largest index the reference can return is `MAX_LENGTH` itself
(the append branch traps only when `i > MAX_LENGTH`), so valid handles are
exactly `1 ≤ i ≤ 2^28 - 1`.

## Relational allocation specification

The Python free-list policy is one deterministic choice. `Table.AddSpec`
admits *any* fresh nonzero index `≤ MAX_LENGTH`, stated over the abstract view
`Nat → Option α` of a table (`Table.View`), and `Table.RemoveSpec` specifies
removal. `Table.Full` is the only state in which the reference allocator
traps, and the only state in which any allocator is *required* to trap;
`AddSpec` constrains only successful allocations, so runtimes may additionally
trap on implementation resource limits (e.g. wasmtime's fallible `TryVec` push
on host OOM). A trap specification, if wanted, should read `Full v → trap`,
not `trap → Full v`.
`Table/Properties.lean` proves that `add?`/`remove?` are instances.

## Wasmtime

Wasmtime (`crates/wasmtime/src/runtime/vm/component/handle_table.rs`, rev
`a7b4f29`, `HandleTable::insert`/`remove`/`get_mut`) stores slot `k` as handle
`k + 1` rather than keeping a dead slot `0`, and threads its free list through
the free slots (`Slot::Free { next }`) instead of a separate stack. Its free
list is still LIFO and falls back to appending, and it fails with "cannot
allocate another handle: index overflow" when `next + 1 >= 1 << 28`, so its
handle numbering and its trap conditions coincide with the reference (as its
`misc_testsuite/component-model/resources.wast` "indices should be lifo" test
pins). As in the reference (`ComponentInstance.handles :
Table[ResourceHandle | Waitable | WaitableSet | ErrorContext]`), a single
wasmtime `HandleTable` stores every handle kind (in one tagged slot type) and
traps on kind mismatches; that typing belongs to the users of this generic
table. The host-side table in `runtime/component/resources/`
adds generation counters for embedder `Resource<T>` values; this is embedder
API, not specification semantics, and is not modelled. Successful allocations
of both allocators satisfy `AddSpec` (wasmtime can additionally fail on host
allocation failure in `slots.push`); only the Python policy is formalized
here.

Not modelled: stores, instances, trapping side effects (`store.lock_down`),
or the typed dispatch performed by canonical built-ins on table entries.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

universe u

namespace Table

variable {α : Type u}

/-! ## Representation-independent specification -/

/-! ## Operations and histories -/

end Table

end Silmaril.Wasm.Component.Runtime
