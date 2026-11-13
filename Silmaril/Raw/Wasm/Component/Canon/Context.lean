module

public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Effects

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

/-! ## Memory access -/

example : (u32Bytes 0x01020304).data = #[4, 3, 2, 1] := by decide

/-! ## Allocation -/

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem utf16Tag (cx : LiftLowerContext E) : P.Inv I (Canon.utf16Tag cx : P E σ _) :=
  bind (ptrType cx) fun _ => pure _

theorem storeU32 (cx : LiftLowerContext E) (ptr v : Nat)
    (h : ∀ m s, I s → I (writeMemSt m ptr (u32Bytes v) s)) :
    P.Inv I (Canon.storeU32 cx ptr v : P E σ Unit) :=
  bind (checkAligned _ _) fun _ => bind (checkInBounds _ _ _) fun _ => writeMem _ _ _ h

end P.Inv

/-- A memory write changes only the core store: every component-level arena and `Store`
field is unchanged. -/
theorem writeMemSt_frame (m : E.MemAddr) (ptr : Nat) (bytes : ByteArray) (s : CStore E) :
    ∃ c, writeMemSt m ptr bytes s = { s with core := c } := by
  unfold writeMemSt
  split
  · exact ⟨_, rfl⟩
  · exact ⟨s.core, rfl⟩

/-- Corollary of `writeMemSt_frame` for the most used fields. -/
theorem writeMemSt_fields (m : E.MemAddr) (ptr : Nat) (bytes : ByteArray) (s : CStore E) :
    let s' := writeMemSt m ptr bytes s
    s'.insts = s.insts ∧ s'.tasks = s.tasks ∧ s'.threads = s.threads ∧
      s'.waiting = s.waiting ∧ s'.lockdown = s.lockdown := by
  obtain ⟨c, hc⟩ := writeMemSt_frame m ptr bytes s
  rw [hc]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Examples -/

section Examples

/-- A small program: allocate 8 bytes aligned to 4 and store an event there. -/
example (cx : LiftLowerContext E) : P E σ Nat := do
  let ptr ← allocate cx 4 8
  unpackEvent cx ptr ⟨.subtask, 1, 2⟩

/-- Without a memory the pointer width is `i32` (D-g). -/
example (s : CStore E) (inst : InstId) :
    ptrTypeIn s ({ opts := {}, inst := inst } : LiftLowerContext E) = .i32 := rfl

end Examples

end Silmaril.Wasm.Component.Canon
