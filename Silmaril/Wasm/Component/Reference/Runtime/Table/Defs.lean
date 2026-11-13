module

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

/-- A Component Model handle table (`definitions.py`, class `Table`). `array[0]`
is reserved; `free` is the free-index stack with its top at the head. -/
structure Table (α : Type u) where
  array : Array (Option α)
  free : List Nat
  deriving Repr, DecidableEq

namespace Table

variable {α : Type u}

/-- `Table.MAX_LENGTH = 2**28 - 1`, the largest index `add` can return. -/
def maxLength : Nat := 2 ^ 28 - 1

/-- `Table.__init__`: `array = [None]`, `free = []`. -/
def empty : Table α := ⟨#[none], []⟩

instance : EmptyCollection (Table α) := ⟨empty⟩

instance : Inhabited (Table α) := ⟨empty⟩

/-- `Table.get`; `none` means trap. -/
def get? (t : Table α) (i : Nat) : Option α := t.array[i]?.join

/-- `Table.add`: reuse the most recently freed index, otherwise append.
Returns the new index and table; `none` means trap (`i > MAX_LENGTH`). -/
def add? (t : Table α) (e : α) : Option (Nat × Table α) :=
  match t.free with
  | i :: free => some (i, ⟨t.array.setIfInBounds i (some e), free⟩)
  | [] =>
    if t.array.size ≤ maxLength then
      some (t.array.size, ⟨t.array.push (some e), []⟩)
    else none

/-- `Table.remove`: `get` then clear the slot and push the index on the free
stack. Returns the removed element; `none` means trap. -/
def remove? (t : Table α) (i : Nat) : Option (α × Table α) :=
  (t.get? i).map fun e => (e, ⟨t.array.setIfInBounds i none, i :: t.free⟩)

/-- `Table.__iter__`: the live elements in index order. -/
def elements (t : Table α) : List α := t.array.toList.filterMap id

/-- The reference's `free` list (bottom of the stack first). -/
def pythonFree (t : Table α) : List Nat := t.free.reverse

/-- Representation invariant. Every reachable table satisfies it
(`Table.WellFormed.empty`, `.add?`, `.remove?` in `Table/Properties.lean`). -/
structure WellFormed (t : Table α) : Prop where
  /-- Slot `0` exists and is empty. -/
  zero : t.array[0]? = some none
  /-- Free-stack entries are exactly the empty nonzero slots. -/
  free_iff : ∀ i, i ∈ t.free ↔ 0 < i ∧ t.array[i]? = some none
  /-- The free stack has no duplicates. -/
  nodup : t.free.Nodup
  /-- At most `MAX_LENGTH + 1` slots, i.e. indices are `≤ MAX_LENGTH`. -/
  bounded : t.array.size ≤ maxLength + 1

/-! ## Representation-independent specification -/

/-- The abstract content of a table: which handle indices are valid, and what
they hold. -/
abbrev View (α : Type u) := Nat → Option α

/-- The abstract view of a concrete table. -/
def view (t : Table α) : View α := t.get?

/-- Allocation specification: `add` of `e` may return any fresh nonzero index
`i ≤ MAX_LENGTH`, after which `i` holds `e` and every other index is
unchanged. Admits both the reference and the wasmtime allocators. -/
structure AddSpec (before : View α) (e : α) (i : Nat) (after : View α) : Prop where
  pos : 0 < i
  bounded : i ≤ maxLength
  fresh : before i = none
  added : after i = some e
  frame : ∀ j, j ≠ i → after j = before j

/-- Every admissible index is in use. This is the only state in which the
reference `add` traps (`add?_eq_none_iff_full`) and the only state in which an
allocator is required to trap; real runtimes may also trap on implementation
resource limits (e.g. host OOM), which `AddSpec` does not constrain. -/
def Full (v : View α) : Prop := ∀ j, 0 < j → j ≤ maxLength → (v j).isSome

/-- Removal specification: `i` held `e`, and now only `i` is invalidated. -/
structure RemoveSpec (before : View α) (i : Nat) (e : α) (after : View α) : Prop where
  found : before i = some e
  removed : after i = none
  frame : ∀ j, j ≠ i → after j = before j

/-! ## Operations and histories -/

/-- A table operation, as issued by a canonical built-in. -/
inductive Op (α : Type u) where
  | add (e : α)
  | get (i : Nat)
  | remove (i : Nat)
  deriving Repr, DecidableEq

/-- A successful (non-trapping) operation together with its result. -/
inductive Event (α : Type u) where
  /-- `add e` returned `i`. -/
  | added (i : Nat) (e : α)
  /-- `get i` returned `e`. -/
  | got (i : Nat) (e : α)
  /-- `remove i` returned `e`. -/
  | removed (i : Nat) (e : α)
  deriving Repr, DecidableEq

/-- The operation that produced an event. -/
def Event.op : Event α → Op α
  | .added _ e => .add e
  | .got i _ => .get i
  | .removed i _ => .remove i

/-- Whether an event changes the entry at index `j` (`add`/`remove` of `j`). -/
def Event.Touches : Event α → Nat → Prop
  | .added i _, j => i = j
  | .got _ _, _ => False
  | .removed i _, j => i = j

instance (ev : Event α) (j : Nat) : Decidable (ev.Touches j) := by
  cases ev <;> unfold Event.Touches <;> infer_instance

/-- The effect of an event on the abstract view. -/
def Event.apply : Event α → View α → View α
  | .added i e, v => fun j => if j = i then some e else v j
  | .got _ _, v => v
  | .removed i _, v => fun j => if j = i then none else v j

/-- Replay a history, oldest event first, on a view. -/
def replay (v : View α) : List (Event α) → View α
  | [] => v
  | ev :: evs => replay (ev.apply v) evs

/-- Run one operation; `none` means trap. -/
def step? (t : Table α) : Op α → Option (Event α × Table α)
  | .add e => (t.add? e).map fun p => (.added p.1 e, p.2)
  | .get i => (t.get? i).map fun e => (.got i e, t)
  | .remove i => (t.remove? i).map fun p => (.removed i p.1, p.2)

/-- Run operations in order, stopping at the first trap. Returns the events
of the successful prefix and the final table, or `none` if a trap occurred. -/
def run (t : Table α) : List (Op α) → List (Event α) × Option (Table α)
  | [] => ([], some t)
  | op :: ops =>
    match t.step? op with
    | none => ([], none)
    | some (ev, t') =>
      let r := t'.run ops
      (ev :: r.1, r.2)

/-- `Steps t evs t'`: the successful history `evs` leads from `t` to `t'`. -/
inductive Steps : Table α → List (Event α) → Table α → Prop where
  | nil (t : Table α) : Steps t [] t
  | cons {t t' t'' : Table α} {ev : Event α} {evs : List (Event α)} :
      t.step? ev.op = some (ev, t') → Steps t' evs t'' → Steps t (ev :: evs) t''

end Table

end Silmaril.Wasm.Component.Runtime
