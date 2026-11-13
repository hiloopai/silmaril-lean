module

public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Wasm.Types
public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

/-!
# The memory view of a Wasm semantics

Every WebAssembly semantics in this development (V1, Lime1, 2.0, Core 3.0, the mock engine)
stores its linear memories the same way: the store holds a list of memory instances, each of
which wraps a `Silmaril.Wasm.Execution.Memory.Bytes` buffer together with bookkeeping (a
maximum, an address type). The byte-level accessors the component runtime needs
(`memAddrType?`, `memSize?`, `memRead?`, `memWrite?`) are then the *same four expressions* in
every engine, and so are their laws -- which are currently proved four times over
(`Engine/Lime1/Properties.lean`, `Engine/V2/Properties.lean`, `Engine/Core3/Store.lean`,
`Engine/Mock.lean`).

A `MemoryView Store` factors that repetition. It is the minimal data a semantics must supply:

* a memory address type and a memory-instance type;
* a partial lookup `inst?` of an instance in a store, and an update `setInst`;
* the byte buffer `data` of an instance, a functional update `withData`, and the instance's
  address type.

The four accessors are *derived* (`addrType?`, `size?`, `read?`, `write?`), and
`MemoryView.Lawful` asks only for four pointwise coherence facts -- read-back and frame for
`setInst`, and read-back and address-type preservation for `withData`. From those,
`Silmaril/Wasm/Semantics/Defs.lean` derives eight of the twenty-three
`Component.Engine.CoreEngine.Lawful` fields.

Deliberately not here: store extension, which mentions function types and thread status and so
cannot be stated at this level (see `WasmSemantics.Lawful.memWrite_frame`), and memory growth,
which the component runtime never performs.
-/

@[expose] public section

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Execution

/-- The linear-memory sublanguage of a Wasm semantics: how to find, read and replace the byte
buffer of a memory instance inside a store. See the module docstring. -/
structure MemoryView (Store : Type → Type) where
  /-- Memory addresses. -/
  MemAddr : Type
  [decEqMemAddr : DecidableEq MemAddr]
  /-- Memory instances: a byte buffer plus engine-specific bookkeeping. -/
  MemInst : Type
  /-- The memory instance at an address, if the address is allocated. -/
  inst? : {H : Type} → Store H → MemAddr → Option MemInst
  /-- Replace the memory instance at an address. Unspecified at unallocated addresses. -/
  setInst : {H : Type} → Store H → MemAddr → MemInst → Store H
  /-- The byte buffer of a memory instance. -/
  data : MemInst → Memory.Bytes
  /-- Replace the byte buffer of a memory instance. -/
  withData : MemInst → Memory.Bytes → MemInst
  /-- The address type of a memory instance (`.i32` for every engine but 64-bit memories). -/
  addrType : MemInst → AddrType

attribute [instance] MemoryView.decEqMemAddr

namespace MemoryView

variable {Store : Type → Type} (V : MemoryView Store)

/-- The address type of a memory, if it is allocated. -/
def addrType? {H : Type} (s : Store H) (m : V.MemAddr) : Option AddrType :=
  (V.inst? s m).map V.addrType

/-- The size of a memory **in bytes**, if it is allocated. -/
def size? {H : Type} (s : Store H) (m : V.MemAddr) : Option Nat :=
  (V.inst? s m).map fun mi => (V.data mi).size

/-- Read `len` bytes from a memory at `start`; `none` if unallocated or out of bounds. -/
def read? {H : Type} (s : Store H) (m : V.MemAddr) (start len : Nat) : Option Memory.Bytes :=
  (V.inst? s m).bind fun mi => Memory.readBytes (V.data mi) start len

/-- Write `bytes` into a memory at `start`; `none` if unallocated or out of bounds. -/
def write? {H : Type} (s : Store H) (m : V.MemAddr) (start : Nat) (bytes : Memory.Bytes) :
    Option (Store H) :=
  (V.inst? s m).bind fun mi =>
    (Memory.writeBytes (V.data mi) start bytes).map fun d => V.setInst s m (V.withData mi d)

/-- Coherence of a memory view: `setInst` reads back at allocated addresses and changes no
other address; `withData` replaces the buffer and keeps the address type. Everything the
component runtime needs of linear memory follows (`MemoryView.Lawful` section below). -/
class Lawful (V : MemoryView Store) : Prop where
  /-- Read-back: replacing the instance at an allocated address is observed there. -/
  inst?_setInst_self : ∀ {H : Type} {s : Store H} {m mi₀ mi},
    V.inst? s m = some mi₀ → V.inst? (V.setInst s m mi) m = some mi
  /-- Frame: replacing the instance at `m` changes no other memory. -/
  inst?_setInst_ne : ∀ {H : Type} {s : Store H} {m mi m'},
    m' ≠ m → V.inst? (V.setInst s m mi) m' = V.inst? s m'
  /-- `withData` installs the given buffer. -/
  data_withData : ∀ mi d, V.data (V.withData mi d) = d
  /-- `withData` keeps the address type. -/
  addrType_withData : ∀ mi d, V.addrType (V.withData mi d) = V.addrType mi

variable {V}

section Lawful

variable [L : V.Lawful]

end Lawful

end MemoryView

end Silmaril.Wasm.Semantics

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Execution

namespace MemoryView

variable {Store : Type → Type} (V : MemoryView Store)
variable {V}

/-- Address-typedness and allocatedness agree. -/
theorem addrType?_isSome_iff {H : Type} {s : Store H} {m} :
    (V.addrType? s m).isSome ↔ (V.size? s m).isSome := by
  simp [addrType?, size?]

/-- The shape of a successful write: the written memory was allocated, `writeBytes` succeeded,
and the resulting store is the instance update. -/
theorem write?_eq_some {H : Type} {s s' : Store H} {m start bs}
    (h : V.write? s m start bs = some s') :
    ∃ mi d, V.inst? s m = some mi ∧ Memory.writeBytes (V.data mi) start bs = some d ∧
      s' = V.setInst s m (V.withData mi d) := by
  simp only [write?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mi, hi, d, hd, rfl⟩ := h
  exact ⟨mi, d, hi, hd, rfl⟩

/-- A read succeeds exactly when the memory is allocated and the range is in bounds. -/
theorem read?_isSome_iff {H : Type} {s : Store H} {m start len} :
    (V.read? s m start len).isSome ↔ ∃ n, V.size? s m = some n ∧ start + len ≤ n := by
  cases h : V.inst? s m with
  | none => simp [read?, size?, h]
  | some mi =>
    simp only [read?, size?, h, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left', Memory.readBytes]
    split <;> simp_all

/-- A read returns exactly the requested number of bytes. -/
theorem read?_size {H : Type} {s : Store H} {m start len bs}
    (h : V.read? s m start len = some bs) : bs.size = len := by
  simp only [read?, Option.bind_eq_some_iff] at h
  obtain ⟨mi, -, hr⟩ := h
  exact Memory.readBytes_size _ _ _ _ hr

/-- A write succeeds exactly when the memory is allocated and the range is in bounds. -/
theorem write?_isSome_iff {H : Type} {s : Store H} {m start bs} :
    (V.write? s m start bs).isSome ↔ ∃ n, V.size? s m = some n ∧ start + bs.size ≤ n := by
  cases h : V.inst? s m with
  | none => simp [write?, size?, h]
  | some mi =>
    simp only [write?, size?, h, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left', Option.isSome_map, Memory.writeBytes]
    split <;> simp_all

section Lawful

variable [L : V.Lawful]

/-- A write preserves every memory size. -/
theorem size?_write? {H : Type} {s s' : Store H} {m start bs}
    (h : V.write? s m start bs = some s') (m' : V.MemAddr) : V.size? s' m' = V.size? s m' := by
  obtain ⟨mi, d, hi, hd, rfl⟩ := write?_eq_some h
  by_cases e : m' = m
  · subst e
    simp only [size?, L.inst?_setInst_self hi, hi, Option.map_some, L.data_withData,
      Memory.writeBytes_size _ _ _ _ hd]
  · rw [size?, size?, L.inst?_setInst_ne e]

/-- A write preserves every memory address type. -/
theorem addrType?_write? {H : Type} {s s' : Store H} {m start bs}
    (h : V.write? s m start bs = some s') (m' : V.MemAddr) :
    V.addrType? s' m' = V.addrType? s m' := by
  obtain ⟨mi, d, hi, hd, rfl⟩ := write?_eq_some h
  by_cases e : m' = m
  · subst e
    simp only [addrType?, L.inst?_setInst_self hi, hi, Option.map_some, L.addrType_withData]
  · rw [addrType?, addrType?, L.inst?_setInst_ne e]

/-- Read after write. -/
theorem read?_write? {H : Type} {s s' : Store H} {m start bs}
    (h : V.write? s m start bs = some s') : V.read? s' m start bs.size = some bs := by
  obtain ⟨mi, d, hi, hd, rfl⟩ := write?_eq_some h
  rw [read?, L.inst?_setInst_self hi, Option.bind_some, L.data_withData]
  exact Memory.readBytes_writeBytes _ _ _ _ hd

/-- Frame law: a read of another memory, or of a range disjoint from the written one, is
unchanged by a write. -/
theorem read?_write?_other {H : Type} {s s' : Store H} {m start bs} {m' start' len}
    (h : V.write? s m start bs = some s')
    (hd : m' ≠ m ∨ start' + len ≤ start ∨ start + bs.size ≤ start') :
    V.read? s' m' start' len = V.read? s m' start' len := by
  obtain ⟨mi, d, hi, hw, rfl⟩ := write?_eq_some h
  by_cases e : m' = m
  · subst e
    rw [read?, read?, L.inst?_setInst_self hi, hi, Option.bind_some, Option.bind_some,
      L.data_withData]
    exact Memory.readBytes_writeBytes_disjoint _ _ _ _ _ _ hw (hd.resolve_left (fun hne => hne rfl))
  · rw [read?, read?, L.inst?_setInst_ne e]

end Lawful

end MemoryView

end Silmaril.Wasm.Semantics
