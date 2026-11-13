module

public import Silmaril.Wasm.Component.Async.Cabi.Defs

@[expose] public section

/-!
# `run_tests.py` as an oracle for the transcribed async Canonical ABI

Seven async tests of `design/mvp/canonical-abi/run_tests.py` at component-model `d095e2f`,
transcribed as scripts of `Silmaril.Wasm.Component.Async.Cabi` with the test's own assertions as
checks (`Chk`). Each script replays the test's calls in the order the Python test makes them;
the expected values are those the Python test asserts. `Silmaril.Wasm.Component.Async.CabiOracle`'s
`Thms` checks every script in the kernel (`decide`), and `#guard` checks them with the compiled
evaluator.

| Script | `run_tests.py` | What it exercises |
|---|---|---|
| `dropBothEndsWhileIdle` | `test_stream_drop_both_ends_while_idle` (L2385) | drops notify the idle peer once; index reuse; poll/wait |
| `futureDropReadableWithPendingWrite` | `test_future_drop_readable_with_pending_write` (L2349) | a blocked future write gets `DROPPED` |
| `futures` | `test_futures` (L2264) | host futures, async lower, `thread.yield`, sync `future.cancel-read` |
| `hostPartialReadsWrites` | `test_host_partial_reads_writes` (L1849) | partial copies, parked buffers that stay parked, `DROPPED` to host |
| `cancelCopy` | `test_cancel_copy` (L2165) | `stream.cancel-{read,write}`, sync and async |
| `asyncCallback` | `test_async_callback` (L794) | callback ABI: `WAIT`, `YIELD`, `EXIT`, `context.{get,set}`, subtask events |
| `asyncBackpressure` | `test_async_backpressure` (L1195) | `backpressure.{inc,dec}`, a callee waiting to enter (`STARTING`) |

**How the Python control flow is replayed.** The host helpers of `run_tests.py`
(`HostWriter`, `HostReader`, `mk_host_func`) are unrolled into host steps. Their `pump`
runs right after the other end's `copy`/`drop`; in every place used here the pump only touches
the host's own end, so the script runs it after the guest's operation. A `wait_until` blocks
and is resumed by a `tick` (the deterministic profile); the script ticks the thread that
Python's `Store.tick` may pick (every assertion of these tests holds for every choice). The
`expect_fail` calls become `Chk.trap`, which keeps the state before the operation (Python keeps
the effects before the trap; the only such effect here is the removal of a handle in a final
`future.drop-writable`, after which the test ends).

The other 17 of the 24 async test functions (`test_async_to_async` onwards) are in
`CabiOracle2` (guest-to-guest calls, sync function types, threads), `CabiOracle3` (streams with
the re-entrant host pumps) and `CabiOracle4` (`test_cancel_subtask`, `test_sync_threads`).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

open Silmaril.Wasm.Component.Async.Cabi

/-- A check of a script. -/
inductive Chk where
  | step (s : Step Nat)
  /-- The operation traps; the state is kept. -/
  | trap (o : Op Nat)
  /-- The last output of thread `th`. -/
  | out (th : Nat) (vs : List Nat)
  /-- Guest memory of instance `i` from `ptr`. -/
  | mem (i ptr : Nat) (vs : List Nat)
  /-- What host buffers of end `e` received. -/
  | recv (e : Nat) (vs : List Nat)
  /-- The payload of the last event taken by host code. -/
  | hostEv (payload : Nat)
  /-- The results stored by a subtask. -/
  | stored (s : Nat) (vs : List Nat)
  /-- The result the embedder's `on_resolve` received. -/
  | hostResult (task : Nat) (r : Option (List AVal))
  /-- The thread exited. -/
  | exited (th : Nat)
  /-- The arguments `on_start` gave the host thread `th`. -/
  | hostArgs (th : Nat) (vs : List AVal)
  /-- The `HostReader` pump `p` has received `vs` (not yet taken) and is `dropped` or not. -/
  | reader (p : Nat) (vs : List Nat) (dropped : Bool)

/-- Shorthand for an operation of the running thread. -/
abbrev op (o : Op Nat) : Chk := .step (.op o)

/-- Shorthand for a tick. -/
abbrev tick (th : Nat) : Chk := .step (.tick th)

/-- Does a check hold now (for the observations), and the next state. `none`: it fails. -/
def Chk.exec (st : Store Nat) : Chk → Option (Store Nat)
  | .step s => match st.runStep s with
    | .ok st' => some st'
    | .error _ => none
  | .trap o => match st.runOp o with
    | .error (.trap _) => some st
    | _ => none
  | .out th vs => match st.threads th with
    | some t => if t.out = vs then some st else none
    | none => none
  | .mem i ptr vs => match st.insts i with
    | some ins => if (List.range vs.length).map (fun k => ins.mem (ptr + k)) = vs then some st else none
    | none => none
  | .recv e vs => if st.hostRecv e = vs then some st else none
  | .hostEv p => match st.hostEvents with
    | (_, _, q) :: _ => if p = q then some st else none
    | [] => none
  | .stored s vs => match st.subs s with
    | some x => if x.stored = vs then some st else none
    | none => none
  | .hostResult t r => match st.tasks t with
    | some x => if x.hostResult = some r then some st else none
    | none => none
  | .exited th => match st.threads th with
    | some t => if t.status = .exited then some st else none
    | none => none
  | .hostArgs th vs => match st.threads th with
    | some t => if t.hostArgs = vs then some st else none
    | none => none
  | .reader p vs d => match st.pumps p with
    | some (.reader r) => if r.received = vs ∧ r.dropped = d then some st else none
    | _ => none

/-- Run the checks; `none` when all hold, `some k` for the first failing check `k`. -/
def runChecks (st : Store Nat) : Nat → List Chk → Option Nat
  | _, [] => none
  | k, c :: cs => match c.exec st with
    | some st' => runChecks st' (k + 1) cs
    | none => some k

/-- The element type `u8`. -/
def u8 : Ty := { id := 0, kind := .number }

/-- `opts.async_ = True`, no callback, `ft.async_ = True`: an async stackful export. -/
def asyncLift (i : Nat) : Callee := .guest i true true false 0

/-- `mk_opts()`: sync options, `ft.async_ = True`. -/
def syncOptsLift (i : Nat) : Callee := .guest i true false false 0

/-- `r | w << 32`. -/
def ends (r w : Nat) : List Nat := [r + w * 2 ^ 32]

/-! ## `test_stream_drop_both_ends_while_idle` (L2385–2437) -/

/-- The script. -/
def dropBothEndsWhileIdle : List Chk := [
  .step (.invoke (asyncLift 0) []),
  op (.taskReturn 0 []),
  op (.streamNew u8), .out 0 (ends 1 2),
  op (.dropEnd .streamW u8 2),
  op (.dropEnd .streamR u8 1),
  op .wsNew, .out 0 [1],
  op (.streamNew u8), .out 0 (ends 2 3),
  op (.join 2 1),
  op (.dropEnd .streamW u8 3),
  op (.wsPoll 1), .out 0 [EventCode.streamRead.toNat, 2, CopyResult.dropped.toNat],
  op (.wsPoll 1), .out 0 [EventCode.none.toNat, 0, 0],
  .trap (.copy .streamR u8 true 2 0 4),
  op (.join 2 0),
  op (.dropEnd .streamR u8 2),
  op (.futureNew u8), .out 0 (ends 2 3),
  op (.join 3 1),
  op (.dropEnd .futureR u8 2),
  op (.wsWait 1), tick 0, .out 0 [EventCode.futureWrite.toNat, 3, CopyResult.dropped.toNat],
  op (.join 3 0),
  op (.dropEnd .futureW u8 3),
  op (.wsDrop 1),
  op .coreExit, .exited 0, .hostResult 0 (some [])]

/-! ## `test_future_drop_readable_with_pending_write` (L2349–2382) -/

/-- The script. -/
def futureDropReadableWithPendingWrite : List Chk := [
  .step (.invoke (asyncLift 0) []),
  op (.taskReturn 0 []),
  op (.futureNew u8), .out 0 (ends 1 2),
  op (.memSet 0 [42]),
  op (.copy .futureW u8 true 2 0 1), .out 0 [BLOCKED],
  op (.dropEnd .futureR u8 1),
  op .wsNew, .out 0 [1],
  op (.join 2 1),
  op (.wsWait 1), tick 0, .out 0 [EventCode.futureWrite.toNat, 2, CopyResult.dropped.toNat],
  op (.join 2 0),
  op (.wsDrop 1),
  op (.dropEnd .futureW u8 2),
  op .coreExit, .exited 0]

/-! ## `test_futures` (L2264–2346) -/

/-- One call of `host_func` (L2272–2281) for incoming end `inc` and outgoing ends `r`, `w`:
`on_start`, `new_future`, `on_resolve`, `copy` into a one-element buffer, `wait_until`. -/
def hostFutureCall : Nat → List Chk
  | inc => [op .hostStart, .step (.hostNew false u8),
            op (.hostResolve [.end_ (inc + 2)]),
            .step (.hostRead inc 1), op (.hostWaitPending inc)]

/-- The script. -/
def futures : List Chk := [
  .step (.invoke (syncOptsLift 0) []),
  op (.futureNew u8), .out 0 (ends 1 2)] ++
  -- `store.lower(host_func_inst, …)([rfi, retp])`: the host thread is thread 1, ends 2, 3
  [op (.lower .host true [.readable false u8 1])] ++ hostFutureCall 0 ++
  [.out 0 [SubState.returned.toNat], .stored 0 [1],
  op (.copy .futureR u8 true 1 0 1), .out 0 [BLOCKED],
  op (.memSet 8 [42]),
  op (.copy .futureW u8 true 2 8 1), .out 0 [CopyResult.completed.toNat],
  op .wsNew, .out 0 [3],
  op (.join 1 3),
  op (.wsWait 3),
  -- the host thread is ready: `assert(buffer.received == [42])`, then it writes 43
  tick 1, .recv 0 [42], .step (.hostWrite 3 [43]), op .hostExit,
  tick 0, .out 0 [EventCode.futureRead.toNat, 1, CopyResult.completed.toNat], .mem 0 0 [43],
  op (.dropEnd .futureW u8 2),
  op (.dropEnd .futureR u8 1),
  op (.wsDrop 3),
  op (.futureNew u8), .out 0 (ends 3 1),
  op (.lower .host true [.readable false u8 3])] ++ hostFutureCall 4 ++
  [.out 0 [SubState.returned.toNat], .stored 1 [3],
  op (.copy .futureR u8 true 3 0 1), .out 0 [BLOCKED],
  op (.memSet 8 [42]),
  op (.copy .futureW u8 true 1 8 1), .out 0 [CopyResult.completed.toNat],
  -- `while not …has_pending_event(): canon_thread_yield()`
  op .threadYield,
  tick 2, .recv 4 [42], .step (.hostWrite 7 [43]), op .hostExit,
  tick 0, .out 0 [0],
  op (.cancelCopy .futureR u8 false 3 false), .out 0 [CopyResult.completed.toNat], .mem 0 0 [43],
  op (.dropEnd .futureW u8 1),
  op (.dropEnd .futureR u8 3),
  op (.futureNew u8), .out 0 (ends 3 1),
  .trap (.dropEnd .futureW u8 1),
  op (.coreReturn []), .exited 0, .hostResult 0 (some [])]

/-! ## `test_host_partial_reads_writes` (L1849–1930) -/

/-- The script. `HostWriter([1,2])` owns ends 0 (readable) and 1; the sink's stream is ends
2 and 3. -/
def hostPartialReadsWrites : List Chk := [
  -- `HostWriter(U8Type(), [1,2], drop_when_empty = False)`: its pump writes [1,2]
  .step (.hostNew true u8), .step (.hostWrite 1 [1, 2]),
  .step (.invoke (syncOptsLift 0) []),
  op (.lower .host true []), op .hostStart, op (.hostResolve [.end_ 0]), op .hostExit,
  .out 0 [SubState.returned.toNat], .stored 0 [1],
  op (.copy .streamR u8 true 1 0 4), .out 0 [CopyResult.completed.toNat + 16 * 2],
  .mem 0 0 [1, 2], .step (.hostTake 1),
  .step (.hostWrite 1 [3, 4]),
  op (.copy .streamR u8 true 1 0 4), .out 0 [CopyResult.completed.toNat + 16 * 2],
  .mem 0 0 [3, 4], .step (.hostTake 1),
  op (.copy .streamR u8 true 1 0 4), .out 0 [BLOCKED],
  .step (.hostWrite 1 [5, 6]), .step (.hostTake 1),
  op .wsNew, .out 0 [2],
  op (.join 1 2),
  op (.wsWait 2), tick 0,
  .out 0 [EventCode.streamRead.toNat, 1, CopyResult.completed.toNat + 16 * 2],
  op (.dropEnd .streamR u8 1),
  op (.streamNew u8), .out 0 (ends 1 3),
  -- the sink: `HostReader(readable_end, remain=2)` parks a two-element buffer
  op (.lower .host true [.readable true u8 1]), op .hostStart, .step (.hostRead 2 2),
  op (.hostResolve []), op .hostExit, .out 0 [SubState.returned.toNat],
  op (.memSet 0 [1, 2, 3, 4, 5, 6]),
  op (.copy .streamW u8 true 3 0 6), .out 0 [CopyResult.completed.toNat + 16 * 2],
  .step (.hostTake 2),
  op (.copy .streamW u8 true 3 2 4), .out 0 [BLOCKED],
  -- `host_reader.set_remain(4)`
  .step (.hostRead 2 4), .step (.hostTake 2),
  op (.join 3 2),
  op (.wsWait 2), tick 0,
  .out 0 [EventCode.streamWrite.toNat, 3, CopyResult.completed.toNat + 16 * 4],
  .recv 2 [1, 2, 3, 4, 5, 6],
  op (.dropEnd .streamW u8 3),
  op (.wsDrop 2),
  -- `host_reader.set_remain(100)`: the copy finds the peer gone and gets `DROPPED`
  .step (.hostRead 2 100), .step (.hostTake 2), .hostEv CopyResult.dropped.toNat,
  op (.coreReturn []), .exited 0]

/-! ## `test_cancel_copy` (L2165–2261) -/

/-- `host_func1`: `on_start`, `HostReader(remain = 0)`, `on_resolve([])`. -/
def hostSink : List Chk := [op .hostStart, op (.hostResolve []), op .hostExit]

/-- `host_func2` with its `HostWriter` on ends `r`, `r + 1`. -/
def hostSource (r : Nat) : List Chk :=
  [op .hostStart, .step (.hostNew true u8), op (.hostResolve [.end_ r]), op .hostExit]

/-- Cancel a write after the host read two of four elements. `async` is the cancel's flag. -/
def cancelWrite (rsi wsi hostR : Nat) (vs : List Nat) (async : Bool) : List Chk := [
  op (.lower .host true [.readable true u8 rsi])] ++ hostSink ++
  [.out 0 [SubState.returned.toNat],
  op (.memSet 0 vs),
  op (.copy .streamW u8 true wsi 0 4), .out 0 [BLOCKED],
  .step (.hostRead hostR 2), .step (.hostTake hostR), .recv hostR (vs.take 2),
  op (.cancelCopy .streamW u8 async wsi false), .out 0 [CopyResult.cancelled.toNat + 16 * 2],
  op (.dropEnd .streamW u8 wsi),
  .step (.hostRead hostR 100), .step (.hostTake hostR), .hostEv CopyResult.dropped.toNat]

/-- The script. -/
def cancelCopy : List Chk := [
  .step (.invoke (syncOptsLift 0) []),
  op (.streamNew u8), .out 0 (ends 1 2)] ++
  cancelWrite 1 2 0 [10, 11, 12, 13] false ++
  [op (.streamNew u8), .out 0 (ends 2 1)] ++
  cancelWrite 2 1 2 [1, 2, 3, 4] true ++
  [op (.lower .host true [])] ++ hostSource 4 ++
  [.out 0 [SubState.returned.toNat], .stored 2 [1],
  op (.copy .streamR u8 true 1 0 4), .out 0 [BLOCKED],
  op (.cancelCopy .streamR u8 false 1 false), .out 0 [CopyResult.cancelled.toNat],
  op (.dropEnd .streamR u8 1),
  op (.lower .host true [])] ++ hostSource 6 ++
  [.out 0 [SubState.returned.toNat], .stored 3 [1],
  op (.copy .streamR u8 true 1 0 4), .out 0 [BLOCKED],
  op (.cancelCopy .streamR u8 true 1 false), .out 0 [CopyResult.cancelled.toNat],
  op (.dropEnd .streamR u8 1),
  op (.lower .host true [])] ++ hostSource 8 ++
  [.out 0 [SubState.returned.toNat], .stored 4 [1],
  op (.copy .streamR u8 true 1 0 4), .out 0 [BLOCKED],
  -- `host_writer.write([7,8])`
  .step (.hostWrite 9 [7, 8]), .step (.hostTake 9),
  op (.cancelCopy .streamR u8 true 1 false), .out 0 [CopyResult.cancelled.toNat + 16 * 2],
  .mem 0 0 [7, 8],
  op (.dropEnd .streamR u8 1),
  op (.coreReturn []), .exited 0]

/-! ## `test_async_callback` (L794–882) -/

/-- The script. Instance 0 is the producer, instance 1 the consumer (callback ABI, result
type `u32` = tag 1). Threads: 0 consumer, 1 and 2 producers. -/
def asyncCallback : List Chk := [
  .step (.invoke (.guest 1 true true true 1) []),
  op (.lower (asyncLift 0) true []), op (.waitFlag 1),
  .out 0 [SubState.started.toNat + 16 * 1],
  op (.lower (asyncLift 0) true []), op (.waitFlag 2),
  .out 0 [SubState.started.toNat + 16 * 2],
  op .wsNew, .out 0 [3],
  op (.join 1 3), op (.join 2 3),
  op (.setFlag 1),
  op (.contextSet 0 42),
  op (.cbReturn (2 + 16 * 3)),
  -- producer 1 runs
  tick 1, op (.taskReturn 0 []), op .coreExit, .exited 1,
  tick 0, .out 0 [EventCode.subtask.toNat, 1, SubState.returned.toNat],
  op (.contextGet 0), .out 0 [42],
  op (.subtaskDrop 1),
  op (.contextSet 0 52),
  op (.cbReturn 1),
  tick 0, .out 0 [EventCode.none.toNat, 0, 0],
  op (.contextGet 0), .out 0 [52],
  op (.setFlag 2),
  op (.contextSet 0 62),
  op (.cbReturn (2 + 16 * 3)),
  tick 2, op (.taskReturn 0 []), op .coreExit, .exited 2,
  tick 0, .out 0 [EventCode.subtask.toNat, 2, SubState.returned.toNat],
  op (.contextGet 0), .out 0 [62],
  op (.subtaskDrop 2),
  op (.taskReturn 1 [.num 83]),
  op (.cbReturn 0), .exited 0,
  .hostResult 0 (some [.num 83])]

/-! ## `test_async_backpressure` (L1195–1275) -/

/-- The script. Instance 0 is the producer, instance 1 the consumer (result type `u8` = tag
1). Thread 1 is producer 1 (which raises backpressure until the flag is set), thread 2
producer 2 (which waits to enter). -/
def asyncBackpressure : List Chk := [
  .step (.invoke (.guest 1 true true false 1) []),
  op (.lower (asyncLift 0) true []), op .backpressureInc, op (.waitFlag 0),
  .out 0 [SubState.started.toNat + 16 * 1],
  -- producer 2 cannot enter: its subtask is `STARTING`
  op (.lower (asyncLift 0) true []), .out 0 [SubState.starting.toNat + 16 * 2],
  op .wsNew, .out 0 [3],
  op (.join 1 3), op (.join 2 3),
  op (.setFlag 0),
  op (.wsWait 3),
  tick 1, op .backpressureDec, op (.taskReturn 0 []), op .coreExit, .exited 1,
  tick 0, .out 0 [EventCode.subtask.toNat, 1, SubState.returned.toNat],
  op (.subtaskDrop 1),
  op (.wsWait 3),
  -- producer 2 enters now that backpressure is off
  tick 2, op (.taskReturn 0 []), op .coreExit, .exited 2,
  tick 0, .out 0 [EventCode.subtask.toNat, 2, SubState.returned.toNat],
  op (.subtaskDrop 2),
  op (.wsDrop 3),
  op (.taskReturn 1 [.num 84]), op .coreExit, .exited 0,
  .hostResult 0 (some [.num 84])]

/-- All scripts, with their initial number of instances. -/
def all : List (String × Nat × List Chk) := [
  ("test_stream_drop_both_ends_while_idle", 1, dropBothEndsWhileIdle),
  ("test_future_drop_readable_with_pending_write", 1, futureDropReadableWithPendingWrite),
  ("test_futures", 1, futures),
  ("test_host_partial_reads_writes", 1, hostPartialReadsWrites),
  ("test_cancel_copy", 1, cancelCopy),
  ("test_async_callback", 2, asyncCallback),
  ("test_async_backpressure", 2, asyncBackpressure)]

/-- Run one script from `Store.init n`. -/
def runScript (n : Nat) (cs : List Chk) : Option Nat := runChecks (Store.init n) 0 cs

end Silmaril.Wasm.Component.Async.Cabi.Oracle
