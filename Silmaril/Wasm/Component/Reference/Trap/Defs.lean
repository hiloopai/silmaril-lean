module

/-!
# Component Model trap reasons

`TrapReason` has one constructor per distinct trap site of the Canonical ABI reference
`definitions.py` at component-model `a25fc0b` (every `trap_if`, plus core traps,
uncaught exceptions and host traps), and `TrapReason.wasmtimeMessage` gives the wasmtime
`a7b4f29` trap message (`crates/environ/src/trap_encoding.rs`, and `bail!` strings in
`crates/wasmtime/src/runtime/component`) that the `.wast` tests match as a substring.

**The specification compares traps only as "some trap".** The reason is informative:
it documents which check fired and lets differential tests compare messages. Where
wasmtime has no dedicated message, `wasmtimeMessage` returns a descriptive string that
is not claimed to match wasmtime. The constructors whose strings are such descriptive
fallbacks (no wasmtime `a7b4f29` or `.wast` counterpart) are exactly: `setNotEmpty`,
`backpressureUnderflow`, `contextIndex`, `reentrantHostCall` and `internal`
(`hostTrap msg` returns the host's own message). All other strings occur in wasmtime
sources or in `.wast` `assert_trap` expectations.

Special constructors:
* `cannotLeave` is REF `trap_if(not task.inst.may_leave)` at every builtin entry,
  including `thread.index` and `thread.resume-later`;
* `reentrantHostCall` is reserved for embeddings and is not produced by the
  specification;
* `internal msg` marks a state unreachable in validated runs (a Python assert that the model must
  still handle); its unreachability is not proved here;
* `exhausted` is fuel exhaustion of the executable machine, not a REF trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

/-- Reasons a Component Model execution traps. -/
inductive TrapReason where
  /-- A trap inside core wasm code. -/
  | coreTrap
  /-- An exception escaped a component (`call_and_trap_on_throw`). -/
  | uncaughtException
  /-- `trap_if(not task.inst.may_leave)` (also `thread.index`, `thread.resume-later`). -/
  | cannotLeave
  /-- The store is locked down after an earlier trap. -/
  | lockedDown
  /-- A handle-table index is not in use. -/
  | unknownHandle (index : Nat)
  /-- A handle-table entry has the wrong kind (resource vs waitable vs ...). -/
  | wrongHandleType
  /-- `trap_if(h.rt is not t.rt)` (wasmtime runtime: "handle index N used with the wrong
  type", `vm/component/resources.rs`). -/
  | resourceTypeMismatch
  /-- An own handle with outstanding lends is dropped or lifted. -/
  | ownLent
  /-- `lift_own`/`resource.drop` of a borrow where an own is required. -/
  | notOwnHandle
  /-- `trap_if(self.num_borrows > 0)` at task exit. -/
  | borrowsRemain
  /-- `convert_i32_to_char` rejects a non-scalar value. -/
  | invalidChar
  /-- A variant/option/result/enum discriminant is out of range. -/
  | invalidDiscriminant
  /-- Invalid UTF-8 in a lifted string. -/
  | invalidUtf8
  /-- Invalid UTF-16 in a lifted string. -/
  | invalidUtf16
  /-- `MAX_STRING_BYTE_LENGTH` exceeded. -/
  | stringTooLong
  /-- `MAX_LIST_BYTE_LENGTH` exceeded. -/
  | listTooLong
  /-- A pointer is not aligned to the element alignment. -/
  | unalignedPointer
  /-- A pointer/length range is outside linear memory. -/
  | outOfBounds
  /-- A handle/thread table reached `Table.MAX_LENGTH`. -/
  | tableFull
  /-- A callback returned an unknown `CallbackCode`. -/
  | unsupportedCallbackCode
  /-- A synchronous task attempted to block before returning. -/
  | cannotBlockSync
  /-- No thread can make progress. -/
  | deadlock
  /-- `task.return`/`task.cancel` called after the task already resolved. -/
  | taskReturnTwice
  /-- `task.return` with a signature or options not matching the task. -/
  | taskReturnInvalid
  /-- `task.return`/`task.cancel` in a sync-lifted task. -/
  | taskNotAsync
  /-- `task.cancel` without a delivered cancellation. -/
  | taskCancelNotCancelled
  /-- An async-lifted export finished without producing a result. -/
  | taskNotResolved
  /-- `subtask.drop` of a subtask that has not resolved (or not been delivered). -/
  | subtaskNotResolved
  /-- `subtask.cancel` after a cancellation was already requested / terminal status. -/
  | subtaskCancelTwice
  /-- A waitable in a waitable set was used synchronously (sync and async). Also used for
  `trap_if(w.has_sync_waiter)` in `waitable.join` (REF L2383) and for
  `trap_if(end.has_sync_waiter)` in `stream/future.cancel-{read,write}` (REF L2501), which
  the `.wast` tests expect with this message (`trap-if-sync-and-waitable-set.wast`). -/
  | subtaskInSet
  /-- `waitable-set.drop` while a thread is waiting on it. -/
  | setHasWaiters
  /-- `waitable-set.drop` of a set that still has members. -/
  | setNotEmpty
  /-- `backpressure.inc` reached the counter bound. -/
  | backpressureOverflow
  /-- `backpressure.dec` at zero. -/
  | backpressureUnderflow
  /-- A stream/future operation while another is active on the same end. -/
  | concurrentStreamOp
  /-- A stream/future end used after it reached the done state (REF
  `trap_if(end.state != End.State.IDLE)` in `copy`, L2466, when the state is `DONE`;
  the `COPYING` case is `concurrentStreamOp`).
  `future` distinguishes futures from streams, `write` the writable from the readable end,
  because wasmtime's messages differ. -/
  | streamDone (future write : Bool)
  /-- Dropping a stream/future end with an operation in flight. `future` distinguishes
  futures from streams, `readable` the readable end (wasmtime "cannot remove busy ...")
  from the writable end ("cannot drop busy ..."), `vm/component/handle_table.rs`. -/
  | dropBusy (future readable : Bool)
  /-- Dropping a future's writable end before writing a value. -/
  | futureNotWritten
  /-- An intra-instance copy with a non-numeric payload. -/
  | sameInstanceCopy
  /-- A buffer longer than `Buffer.MAX_LENGTH`. -/
  | bufferTooLong
  /-- Lifting a stream/future end that is busy or done. -/
  | liftBusyEnd
  /-- REF `stream.forward`/`future.forward` on a readable or writable end that is not
  idle (`trap_if(readable_end.state != IDLE)` L2553, `trap_if(writable_end.state != IDLE)`
  L2558). `future` distinguishes futures from streams. -/
  | forwardBusy (future : Bool)
  /-- Lifting or forwarding a stream/future end that is in a waitable set. -/
  | endInSet
  /-- Resuming a thread that is not suspended. Also used for `trap_if(i == thread.index)`
  in `thread.suspend-then-promote` / `thread.yield-then-promote` (REF L2646, L2656), which
  the `.wast` tests expect with this message (`self-switch-traps.wast`). -/
  | cannotResumeThread
  /-- `thread.new-indirect` table entry has the wrong type. -/
  | threadNewIndirectType
  /-- `thread.new-indirect` table entry is null (or out of bounds). -/
  | threadNewIndirectNull
  /-- `realloc` returned a misaligned pointer. -/
  | reallocMisaligned
  /-- `realloc` returned a range outside linear memory. -/
  | reallocOutOfBounds
  /-- `context.get/set` index out of range. -/
  | contextIndex
  /-- A trap raised by host code. -/
  | hostTrap (message : String)
  /-- Fuel exhaustion of the executable machine (not a REF trap). -/
  | exhausted
  /-- Reserved for embeddings that forbid re-entrant host calls; unused by the spec. -/
  | reentrantHostCall
  /-- A memory-requiring operation without a `memory` option. -/
  | noMemory
  /-- An internal inconsistency, unreachable in validated runs. -/
  | internal (msg : String)
  deriving Repr, DecidableEq, BEq

namespace TrapReason

/-- The wasmtime `a7b4f29` trap message (a substring matched by `.wast` tests) where
one exists; otherwise a descriptive string that is not claimed to match wasmtime. -/
def wasmtimeMessage : TrapReason → String
  | coreTrap => "wasm trap"
  | uncaughtException => "uncaught exception propagated out of component"
  | cannotLeave => "cannot leave component instance"
  | lockedDown => "cannot enter component instance"
  | unknownHandle i => s!"unknown handle index {i}"
  | wrongHandleType => "used with the wrong type"
  | resourceTypeMismatch => "used with the wrong type"
  | ownLent => "cannot remove owned resource while borrowed"
  | notOwnHandle => "own resource"
  | borrowsRemain => "borrow handles still remain at the end of the call"
  | invalidChar => "invalid `char` bit pattern"
  | invalidDiscriminant => "discriminant"
  | invalidUtf8 => "invalid utf-8"
  | invalidUtf16 => "invalid utf16"
  | stringTooLong => "string content out-of-bounds"
  | listTooLong => "list content out-of-bounds"
  | unalignedPointer => "unaligned pointer"
  | outOfBounds => "out of bounds"
  | tableFull => "cannot allocate another handle"
  | unsupportedCallbackCode => "unsupported callback code"
  | cannotBlockSync => "cannot block a synchronous task before returning"
  | deadlock => "deadlock detected"
  | taskReturnTwice =>
      "`task.return` or `task.cancel` called more than once for current task"
  | taskReturnInvalid => "invalid `task.return` signature and/or options for current task"
  | taskNotAsync => "invalid `task.return` signature and/or options for current task"
  | taskCancelNotCancelled => "called by task which has not been cancelled"
  | taskNotResolved => "async-lifted export failed to produce a result"
  | subtaskNotResolved => "cannot drop a subtask which has not yet resolved"
  | subtaskCancelTwice => "`subtask.cancel` called after terminal status delivered"
  | subtaskInSet => "waitable cannot be used synchronously while added to a waitable set"
  | setHasWaiters => "cannot drop waitable set with waiters"
  | setNotEmpty => "cannot drop waitable set with members"
  | backpressureOverflow => "backpressure counter overflow"
  | backpressureUnderflow => "backpressure counter underflow"
  | concurrentStreamOp => "cannot have concurrent operations active on a future/stream"
  | streamDone true true => "cannot write to future after previous write succeeded"
  | streamDone true false => "cannot read from future after previous read succeeded"
  | streamDone false true => "cannot write to stream after being notified"
  | streamDone false false => "cannot read from stream after being notified"
  | dropBusy future readable =>
      (if readable then "cannot remove busy " else "cannot drop busy ") ++
        (if future then "future" else "stream")
  | futureNotWritten => "cannot drop future write end without first writing a value"
  | sameInstanceCopy => "cannot read from and write to intra-component future"
  | bufferTooLong => "stream read/write count too large"
  | liftBusyEnd => "cannot lift"
  | forwardBusy future => if future then "cannot forward busy future"
      else "cannot forward busy stream"
  | endInSet => "while it's in a waitable set"
  | cannotResumeThread => "cannot resume thread which is not suspended"
  | threadNewIndirectType => "start function does not match expected type"
  | threadNewIndirectNull => "the start function index points to an uninitialized function"
  | reallocMisaligned => "realloc return: result not aligned"
  | reallocOutOfBounds => "realloc return: beyond end of memory"
  | contextIndex => "context index out of bounds"
  | hostTrap msg => msg
  | exhausted => "all fuel consumed"
  | reentrantHostCall => "reentrant host call"
  | noMemory => "canonical option `memory` is required"
  | internal msg => s!"internal error: {msg}"

end TrapReason

end Silmaril.Wasm.Component
