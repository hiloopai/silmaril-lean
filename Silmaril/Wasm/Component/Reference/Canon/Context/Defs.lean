module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs

/-!
# `LiftLowerContext` helpers as specification programs

The memory-facing helpers of REF `LiftLowerContext` and `MemInst`
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>),
written in `P E σ` over the core memory of the engine store `CStore.core`:

| Lean | REF |
| --- | --- |
| `ptrTypeIn s cx`, `ptrType cx` | `cx.opts.memory.ptr_type()` (`MemInst.ptr_type`, L588) |
| `ptrSizeOf`, `ptrSize cx` | `ptr_size` (L567), `MemInst.ptr_size` (L591) |
| `utf16Tag cx` | the UTF-16 tag bit `ABI.utf16Tag` (bit 31 or 63) of the pointer width |
| `memLen cx` | `len(cx.opts.memory)` |
| `memBytes? s cx ptr len` | `cx.opts.memory[ptr : ptr+len]` (pure, no trap) |
| `readMem cx ptr len` | the same, trapping `outOfBounds` |
| `writeMem cx ptr bytes` | `cx.opts.memory[ptr : ptr+len] = bytes`, trapping `outOfBounds` |
| `checkAligned ptr align` | `trap_if(ptr != align_to(ptr, alignment))` |
| `checkInBounds cx ptr size` | `trap_if(ptr + size > len(cx.opts.memory))` |
| `storeU32 cx ptr v` | `store(cx, v, U32Type(), ptr)` (L1461, `store_int` L1488), D-d traps |
| `unpackEvent cx ptr e` | `unpack_event` (L2349-2354) with the D-d traps |
| `reallocate cx old oldLen align newLen` | `LiftLowerContext.reallocate` (L625-641), late-bound |
| `allocate cx align size` | `LiftLowerContext.allocate` (L643-644) |

`reallocate` is the late-bound call `Call.reallocate`; its handler (`Canon.reallocProg` of
`Canon/Lift.lean`, dispatched by `Canon.dispatch`) performs REF `reallocate`: `store.lift` of the
realloc as a sync task with `may_leave = False` around the `store.invoke`.

## Deviations and non-claims

* D-g: without a `memory` option the pointer type is `.i32` (REF would raise; validation makes
  this unreachable wherever a pointer is used). A memory address unknown to the core store
  (dangling; unreachable for instantiated components) also defaults to `.i32` in `ptrTypeIn`.
* Memory access with no `memory` option traps `noMemory` (REF would raise on `None`;
  unreachable for valid components); a failed engine read/write traps `outOfBounds`.
* D-d: `storeU32` (hence `unpackEvent`) traps on a misaligned (`unalignedPointer`) or
  out-of-bounds (`outOfBounds`) pointer, like wasmtime; REF `store` only asserts. `unpackEvent`
  checks the whole 8-byte pointer-pair slot (alignment 4, size 8) before writing anything, as
  wasmtime's `validate_inbounds_dynamic(&CanonicalAbiInfo::POINTER_PAIR, ..)`
  (`crates/wasmtime/src/runtime/component/concurrent.rs`, `waitable_set_wait`/`poll`), so a
  trapping `unpackEvent` leaves memory unchanged; it then writes `p1` at `ptr` and `p2` at
  `ptr + 4`, as REF's two stores.
* The exact `trap_if` orders of the REF functions using these helpers are the callers'
  responsibility; `readMem`/`writeMem` perform no alignment check.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type} {α : Type}

/-! ## Pointer width -/

/-- The pointer type of `cx` in store `s` (D-g: `.i32` without a memory). -/
def ptrTypeIn (s : CStore E) (cx : LiftLowerContext E) : AddrType :=
  cx.opts.ptrType (fun m => (E.memAddrType? s.core m).getD .i32)

/-- REF `ptr_size` (L567): 4 for `i32`, 8 for `i64`. -/
def ptrSizeOf : AddrType → Nat
  | .i32 => 4
  | .i64 => 8

/-- REF `cx.opts.memory.ptr_type()` (D-g: `.i32` without a memory). -/
def ptrType (cx : LiftLowerContext E) : P E σ AddrType := gets (ptrTypeIn · cx)

/-- REF `cx.opts.memory.ptr_size()`. -/
def ptrSize (cx : LiftLowerContext E) : P E σ Nat := do return ptrSizeOf (← ptrType cx)

/-- The UTF-16 tag bit of `cx`'s pointer width (bit 31 or 63). -/
def utf16Tag (cx : LiftLowerContext E) : P E σ Nat := do return ABI.utf16Tag (← ptrType cx)

/-! ## Memory access -/

/-- The memory of `cx`, trapping `noMemory` when the option is absent. -/
def memAddr (cx : LiftLowerContext E) : P E σ E.MemAddr :=
  orTrap .noMemory cx.opts.memory

/-- `cx.opts.memory[ptr : ptr+len]` in store `s`, if in bounds (pure). -/
def memBytes? (s : CStore E) (cx : LiftLowerContext E) (ptr len : Nat) : Option ByteArray :=
  cx.opts.memory.bind fun m => E.memRead? s.core m ptr len

/-- REF `len(cx.opts.memory)` in bytes. -/
def memLen (cx : LiftLowerContext E) : P E σ Nat := do
  let m ← memAddr cx
  orTrap (.internal "dangling memory address") (E.memSize? (← getStore).core m)

/-- Read `len` bytes at `ptr`, trapping `outOfBounds`. -/
def readMem (cx : LiftLowerContext E) (ptr len : Nat) : P E σ ByteArray := do
  let m ← memAddr cx
  orTrap .outOfBounds (E.memRead? (← getStore).core m ptr len)

/-- The store update of `writeMem` (unchanged if the engine write fails). -/
def writeMemSt (m : E.MemAddr) (ptr : Nat) (bytes : ByteArray) (s : CStore E) : CStore E :=
  match E.memWrite? s.core m ptr bytes with
  | some c => { s with core := c }
  | none => s

/-- Write `bytes` at `ptr`, trapping `outOfBounds`. -/
def writeMem (cx : LiftLowerContext E) (ptr : Nat) (bytes : ByteArray) : P E σ Unit := do
  let m ← memAddr cx
  match E.memWrite? (← getStore).core m ptr bytes with
  | none => trap .outOfBounds
  | some _ => modifyStore (writeMemSt m ptr bytes)

/-- REF `trap_if(ptr != align_to(ptr, alignment))`. -/
def checkAligned (ptr align : Nat) : P E σ Unit :=
  trapIf (ptr % align != 0) .unalignedPointer

/-- REF `trap_if(ptr + size > len(cx.opts.memory))`. -/
def checkInBounds (cx : LiftLowerContext E) (ptr size : Nat) : P E σ Unit := do
  trapIf (decide (ptr + size > (← memLen cx))) .outOfBounds

/-- The 4 little-endian bytes of `v mod 2^32`. -/
def u32Bytes (v : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat v, UInt8.ofNat (v / 2 ^ 8), UInt8.ofNat (v / 2 ^ 16),
    UInt8.ofNat (v / 2 ^ 24)]⟩

/-- REF `store(cx, v, U32Type(), ptr)` with the D-d alignment and bounds traps. -/
def storeU32 (cx : LiftLowerContext E) (ptr v : Nat) : P E σ Unit := do
  checkAligned ptr 4
  checkInBounds cx ptr 4
  writeMem cx ptr (u32Bytes v)

/-- REF `unpack_event(mem, inst, ptr, e)` (L2349-2354) with the D-d traps: check alignment 4
and bounds of the whole 8-byte slot first (like wasmtime's `POINTER_PAIR` check, so a trap
writes nothing), then store the index and payload as `u32`s at `ptr` and `ptr + 4`; returns
the event code. -/
def unpackEvent (cx : LiftLowerContext E) (ptr : Nat) (e : AsyncRef.EventTuple) : P E σ Nat := do
  checkAligned ptr 4
  checkInBounds cx ptr 8
  writeMem cx ptr (u32Bytes e.index)
  writeMem cx (ptr + 4) (u32Bytes e.payload)
  return e.code.toNat

/-! ## Allocation -/

/-- REF `LiftLowerContext.reallocate` (L625-641), as the late-bound `Call.reallocate`. -/
def reallocate (cx : LiftLowerContext E) (old oldLen align newLen : Nat) : P E σ Nat :=
  callNat (.reallocate cx old oldLen align newLen)

/-- REF `LiftLowerContext.allocate` (L643-644). -/
def allocate (cx : LiftLowerContext E) (align size : Nat) : P E σ Nat :=
  reallocate cx 0 0 align size

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon
