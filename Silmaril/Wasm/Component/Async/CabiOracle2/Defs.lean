module

public import Silmaril.Wasm.Component.Async.CabiOracle.Defs

@[expose] public section

/-!
# More `run_tests.py` async tests as scripts (guest-to-guest calls, sync lifts, threads)

Further async tests of `design/mvp/canonical-abi/run_tests.py` at component-model `d095e2f`,
transcribed as scripts of `Silmaril.Wasm.Component.Async.Cabi` with the test's own assertions as
checks (`Oracle.Chk`), in the style of `Silmaril.Wasm.Component.Async.CabiOracle`. Each script
replays the Python test's calls in order; where Python's `Store.tick` or the `canon lift` loop
may pick among several ready threads, the script ticks one of them (the assertions of these
tests hold for every choice).

| Script | `run_tests.py` | What it exercises |
|---|---|---|
| `asyncToAsync` | `test_async_to_async` (L682) | async lowers of async callees, backpressure, `STARTING` → `STARTED` → `RETURNED` events, arguments |
| `syncUsingWait` | `test_sync_using_wait` (L1278) | a sync-lifted caller using `waitable-set.wait` |
| `asyncToSync` | `test_async_to_sync` (L1111) | callees with sync options wait for the exclusive thread |
| `callbackInterleaving` | `test_callback_interleaving` (L885) | callback ABI, `subtask.cancel` before start, futures passed to a callee, host backpressure |
| `syncIgnoresBackpressure` | `test_sync_ignores_backpressure` (L1054) | a sync function type enters while the exclusive thread is taken; the `canon lift` loop |
| `forward` | `test_forward` (L1719) | `stream.forward`, `future.forward`: drops, splices, re-issued copies |
| `receiveOwnStream` | `test_receive_own_stream` (L1810) | a readable end passed to the host and back |
| `selfCopy` | `test_self_copy(None/U8/F64)` (L2780) | copies within one instance, zero-length copies, cancellation of completed copies |
| `wasmToWasmStream` | `test_wasm_to_wasm_stream` (L1933) | a stream returned from one instance to another, partial and zero-length copies |
| `wasmToWasmStreamEmpty` | `test_wasm_to_wasm_stream_empty` (L2066) | the same with element type `None` |
| `asyncFlatParams` | `test_async_flat_params` (L2860) | host callees get the arguments in order (values; the spilling of flat parameters to memory is not modelled) |
| `threads` | `test_threads` (L2909) | `thread.{index,new-indirect,yield-then-resume,suspend-then-resume,resume-later,suspend,yield}` |

Element types are tags: `u8 = {id 0, number}`, `none = {id 1, none}`, `f64 = {id 2, number}`;
result types are tags (`0`: none, `1`: `u8`, `2`: `u32`, `3`: `stream<u8>`, `4`: `stream`).
Thread, task, subtask and end ids are global allocation counters; handles are per instance.
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

open Silmaril.Wasm.Component.Async.Cabi

/-- The element type `None` (`FutureType(None)`, `StreamType(None)`). -/
def tnone : Ty := { id := 1, kind := .none }

/-- The element type `f64`. -/
def f64 : Ty := { id := 2, kind := .number }

/-- `Subtask.State` codes. -/
abbrev sStarting : Nat := SubState.starting.toNat
/-- `Subtask.State` codes. -/
abbrev sStarted : Nat := SubState.started.toNat
/-- `Subtask.State` codes. -/
abbrev sReturned : Nat := SubState.returned.toNat

/-- A subtask event `(SUBTASK, i, state)`. -/
def subEv (i state : Nat) : List Nat := [EventCode.subtask.toNat, i, state]

/-- A packed stream copy result `result | n << 4`. -/
def packed (r : CopyResult) (n : Nat) : Nat := r.toNat + 16 * n

/-! ## `test_async_to_async` (L682–791) -/

/-- The script. Instance 0 is the producer, 1 the consumer. Threads: 0 consumer, 1 eager,
2 toggle, 3 blocking producer. Flags 1–5 are `fut1_1`, `fut1_2`, `fut2`, `fut3`, `fut4`. -/
def asyncToAsync : List Chk := [
  .step (.invoke (.guest 1 true true false 1) [.num 1]),
  op .wsNew, .out 0 [1],
  -- the eager producer returns at once
  op (.lower (.guest 0 true true false 1) true []),
  op (.taskReturn 1 [.num 43]), op .coreExit, .exited 1,
  .out 0 [sReturned], .stored 0 [43],
  -- the toggle raises backpressure and waits
  op (.lower (.guest 0 true true false 0) true []),
  op .backpressureInc, op (.waitFlag 1),
  .out 0 [sStarted + 16 * 2],
  op (.join 2 1),
  -- the blocking producer cannot enter
  op (.lower (.guest 0 true true false 1) true [.num 83]),
  .out 0 [sStarting + 16 * 3], .stored 2 [],
  op (.join 3 1),
  op (.setFlag 1),
  op (.wsWait 1),
  tick 2, op (.taskReturn 0 []), op (.waitFlag 2),
  tick 0, .out 0 (subEv 2 sReturned),
  op (.subtaskDrop 2),
  op (.setFlag 2),
  op (.wsWait 1),
  tick 2, op .backpressureDec, op .coreExit, .exited 2,
  tick 3, .out 3 [83], op (.waitFlag 3),
  tick 0, .out 0 (subEv 3 sStarted), .stored 2 [],
  op (.setFlag 3),
  op (.wsWait 1),
  tick 3, op (.taskReturn 1 [.num 44]), op (.waitFlag 4),
  tick 0, .out 0 (subEv 3 sReturned), .stored 2 [44],
  op (.subtaskDrop 3),
  op (.setFlag 4),
  op (.waitFlag 5),
  tick 3, op (.setFlag 5), op .coreExit, .exited 3,
  tick 0,
  op (.taskReturn 1 [.num 42]), op .coreExit, .exited 0,
  .hostResult 0 (some [.num 42])]

/-! ## `test_sync_using_wait` (L1278–1338) -/

/-- The script. Instance 0: the producers (threads 1, 2); instance 1: the consumer, lifted
with sync options (`mk_opts()`). -/
def syncUsingWait : List Chk := [
  .step (.invoke (.guest 1 true false false 0) []),
  op (.lower (.guest 0 true true false 0) true []), op (.waitFlag 1),
  .out 0 [sStarted + 16 * 1],
  op (.lower (.guest 0 true true false 0) true []), op (.waitFlag 2),
  .out 0 [sStarted + 16 * 2],
  op .wsNew, .out 0 [3],
  op (.join 1 3), op (.join 2 3),
  op (.setFlag 1),
  op (.wsWait 3),
  tick 1, op (.taskReturn 0 []), op .coreExit, .exited 1,
  tick 0, .out 0 (subEv 1 sReturned),
  op (.setFlag 2),
  op (.wsWait 3),
  tick 2, op (.taskReturn 0 []), op .coreExit, .exited 2,
  tick 0, .out 0 (subEv 2 sReturned),
  op (.subtaskDrop 1), op (.subtaskDrop 2), op (.wsDrop 3),
  op (.coreReturn []), .exited 0, .hostResult 0 (some [])]

/-! ## `test_async_to_sync` (L1111–1192) -/

/-- The script. The producers have sync options (`CanonicalOptions()`), so producer 2
(thread 2) waits for producer 1 (thread 1) to release the exclusive thread. -/
def asyncToSync : List Chk := [
  .step (.invoke (.guest 1 true true false 1) []),
  op (.lower (.guest 0 true false false 0) true []), op (.waitFlag 1),
  .out 0 [sStarted + 16 * 1],
  op (.lower (.guest 0 true false false 0) true []),
  .out 0 [sStarting + 16 * 2],
  op .wsNew, .out 0 [3],
  op (.join 1 3), op (.join 2 3),
  op (.setFlag 1),
  -- `while remain: canon_thread_yield(); poll`
  op .threadYield,
  tick 1, op (.coreReturn []), .exited 1,
  tick 0, .out 0 [0],
  op (.wsPoll 3), .out 0 (subEv 1 sReturned),
  op (.subtaskDrop 1),
  op .threadYield,
  tick 2, op (.coreReturn []), .exited 2,
  tick 0, .out 0 [0],
  op (.wsPoll 3), .out 0 (subEv 2 sReturned),
  op (.subtaskDrop 2),
  op (.wsDrop 3),
  op (.taskReturn 1 [.num 83]), op .coreExit, .exited 0,
  .hostResult 0 (some [.num 83])]

/-! ## `test_callback_interleaving` (L885–1051) -/

/-- The producer (callback ABI, result `u32`). -/
def producerCb : Callee := .guest 0 true true true 2

/-- The producer's `core_producer` (L890–907) on the handles `fut1 fut2 fut3` of instance 0,
after `context.set`: a sync `future.read` of `fut1` that blocks. -/
def producerStart (i fut1 : Nat) : List Chk :=
  [op (.contextSet 0 i), op (.copy .futureR tnone false fut1 0xdeadbeef 1)]

/-- The script. Instance 0 is the producer, 1 the consumer (lifted with sync options).
Threads: 0 consumer; 1, 3 the cancelled producers; 2, 4 the producers; 5 the sync callee.
Futures (element type `None`): consumer handles `1..12` are `rfut11, wfut11, rfut12, …,
wfut23` (ends `0..11`). -/
def callbackInterleaving : List Chk := [
  .step (.invoke (.guest 1 true false false 0) []),
  op (.futureNew tnone), .out 0 (ends 1 2),
  op (.futureNew tnone), .out 0 (ends 3 4),
  op (.futureNew tnone), .out 0 (ends 5 6),
  op (.futureNew tnone), .out 0 (ends 7 8),
  op (.futureNew tnone), .out 0 (ends 9 10),
  op (.futureNew tnone), .out 0 (ends 11 12),
  .step (.setBackpressure 0 1),
  op (.lower producerCb true [.num 0, .readable false tnone 1, .readable false tnone 3,
    .readable false tnone 5]),
  .out 0 [sStarting + 16 * 13],
  op (.subtaskCancel false 13), .out 0 [SubState.cancelledBeforeStarted.toNat], .exited 1,
  .step (.setBackpressure 0 0),
  -- producer 0 (thread 2) enters; its futures get handles 1, 2, 3 of instance 0
  op (.lower producerCb true [.num 0, .readable false tnone 1, .readable false tnone 3,
    .readable false tnone 5]),
  .out 2 [0, 1, 2, 3]] ++ producerStart 0 1 ++ [
  .out 0 [sStarted + 16 * 5],
  -- producer 1 (thread 3) must wait for the exclusive thread; cancelled
  op (.lower producerCb true [.num 1, .readable false tnone 7, .readable false tnone 9,
    .readable false tnone 11]),
  .out 0 [sStarting + 16 * 3],
  op (.subtaskCancel false 3), .out 0 [SubState.cancelledBeforeStarted.toNat],
  op (.lower producerCb true [.num 1, .readable false tnone 7, .readable false tnone 9,
    .readable false tnone 11]),
  .out 0 [sStarting + 16 * 1],
  op .wsNew, .out 0 [14],
  op (.join 5 14), op (.join 1 14),
  op (.copy .futureW tnone true 2 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat],
  op (.wsWait 14),
  -- producer 0 reads `fut1`, waits on `fut2`
  tick 2, .out 2 [CopyResult.completed.toNat],
  op .wsNew, .out 2 [4],
  op (.copy .futureR tnone true 2 0xdeadbeef 1), .out 2 [BLOCKED],
  op (.join 2 4), op (.cbReturn (2 + 16 * 4)),
  -- producer 1 (thread 4) enters; its futures get handles 5, 6, 7
  tick 4, .out 4 [1, 5, 6, 7]] ++ producerStart 1 5 ++ [
  tick 0, .out 0 (subEv 1 sStarted),
  op (.copy .futureW tnone true 4 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat]] ++
  -- ten rounds of `canon_thread_yield(); poll` with nothing to report
  (List.replicate 10 [op .threadYield, tick 0, .out 0 [0], op (.wsPoll 14), .out 0 [0, 0, 0]]).flatten ++ [
  op (.copy .futureW tnone true 8 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat],
  op (.wsWait 14),
  tick 4, .out 4 [CopyResult.completed.toNat],
  op .wsNew, .out 4 [8],
  op (.copy .futureR tnone true 6 0xdeadbeef 1), .out 4 [BLOCKED],
  op (.join 6 8), op (.cbReturn (2 + 16 * 8)),
  -- producer 0's callback: `FUTURE_READ`, then `task.return(42)` and a sync read of `fut3`
  tick 2, .out 2 [EventCode.futureRead.toNat, 2, CopyResult.completed.toNat],
  op (.contextGet 0), .out 2 [0],
  op (.taskReturn 2 [.num 42]),
  op (.copy .futureR tnone false 3 0xdeadbeef 1),
  tick 0, .out 0 (subEv 5 sReturned), .stored 1 [42],
  op (.subtaskDrop 5),
  op (.copy .futureW tnone true 10 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat]] ++
  (List.replicate 10 [op .threadYield, tick 0, .out 0 [0], op (.wsPoll 14), .out 0 [0, 0, 0]]).flatten ++ [
  op (.copy .futureW tnone true 6 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat],
  op (.wsWait 14),
  tick 2, .out 2 [CopyResult.completed.toNat], op (.cbReturn 0), .exited 2,
  tick 4, .out 4 [EventCode.futureRead.toNat, 6, CopyResult.completed.toNat],
  op (.contextGet 0), .out 4 [1],
  op (.taskReturn 2 [.num 43]),
  op (.copy .futureR tnone false 7 0xdeadbeef 1),
  tick 0, .out 0 (subEv 1 sReturned), .stored 3 [43],
  op (.subtaskDrop 1),
  -- the sync callee (sync options) waits for the exclusive thread
  op (.lower (.guest 0 true false false 2) true []),
  .out 0 [sStarting + 16 * 1],
  op (.join 1 14),
  op (.copy .futureW tnone true 12 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat],
  op (.wsWait 14),
  tick 4, .out 4 [CopyResult.completed.toNat], op (.cbReturn 0), .exited 4,
  tick 5, op (.coreReturn [100]), .exited 5,
  tick 0, .out 0 (subEv 1 sReturned), .stored 4 [100],
  op (.coreReturn []), .exited 0]

/-! ## `test_sync_ignores_backpressure` (L1054–1108) -/

/-- The script. Instance 0: the async-typed callee with sync options (thread 1, which takes
the exclusive thread) and the sync-typed callee (thread 2, which enters anyway); instance 1:
the caller. -/
def syncIgnoresBackpressure : List Chk := [
  .step (.invoke (.guest 1 true false false 0) []),
  op (.futureNew tnone), .out 0 (ends 1 2),
  op (.lower (.guest 0 true false false 2) true [.num 1, .readable false tnone 1]),
  .out 1 [1, 1],
  op (.copy .futureR tnone false 1 0xdeadbeef 1),
  .out 0 [sStarted + 16 * 1],
  -- a sync function type: no backpressure check; the `canon lift` loop is not needed
  op (.lower (.guest 0 false false false 2) true [.num 2]),
  .out 2 [2], op (.coreReturn [86]), .exited 2,
  .out 0 [sReturned], .stored 1 [86],
  op (.copy .futureW tnone false 2 0xdeadbeef 1), .out 0 [CopyResult.completed.toNat],
  op .wsNew, .out 0 [3],
  op (.join 1 3),
  op (.wsWait 3),
  tick 1, .out 1 [CopyResult.completed.toNat], op (.coreReturn [43]), .exited 1,
  tick 0, .out 0 (subEv 1 sReturned),
  op (.subtaskDrop 1),
  op (.coreReturn []), .exited 0]

/-! ## `test_forward` (L1719–1807) -/

/-- The script. One instance, lifted with sync options; handles are reused last freed first. -/
def forward : List Chk := [
  .step (.invoke (.guest 0 true false false 0) []),
  -- `forward` of the two ends of one stream drops both
  op (.streamNew u8), .out 0 (ends 1 2),
  op (.forward true u8 1 2),
  -- forwarding into a writable end whose reader is gone: the source writer sees `DROPPED`
  op (.streamNew u8), .out 0 (ends 2 1),
  op (.streamNew u8), .out 0 (ends 3 4),
  op (.dropEnd .streamR u8 3),
  op (.forward true u8 2 4),
  op (.copy .streamW u8 true 1 0 4), .out 0 [packed .dropped 0],
  op (.dropEnd .streamW u8 1),
  -- a splice; the write parks, the read on the other stream takes it
  op (.streamNew u8), .out 0 (ends 1 4),
  op (.streamNew u8), .out 0 (ends 2 3),
  op (.forward true u8 1 3),
  op (.memSet 0 [1, 2, 3, 4]),
  op (.copy .streamW u8 true 4 0 4), .out 0 [BLOCKED],
  op (.copy .streamR u8 true 2 8 4), .out 0 [packed .completed 4],
  .mem 0 8 [1, 2, 3, 4],
  -- a parked read, then a splice, then the write
  op (.streamNew u8), .out 0 (ends 3 1),
  op (.streamNew u8), .out 0 (ends 5 6),
  op (.copy .streamR u8 true 5 8 4), .out 0 [BLOCKED],
  op (.forward true u8 3 6),
  op (.memSet 0 [5, 6, 7, 8]),
  op (.copy .streamW u8 true 1 0 4), .out 0 [packed .completed 4],
  .mem 0 8 [5, 6, 7, 8],
  op .wsNew, .out 0 [6],
  op (.join 5 6),
  op (.wsWait 6), tick 0,
  .out 0 [EventCode.streamRead.toNat, 5, packed .completed 4],
  -- futures: a parked read, a splice, a write
  op (.futureNew u8), .out 0 (ends 3 7),
  op (.futureNew u8), .out 0 (ends 8 9),
  op (.copy .futureR u8 true 8 8 1), .out 0 [BLOCKED],
  op (.forward false u8 3 9),
  op (.memSet 0 [42]),
  op (.copy .futureW u8 true 7 0 1), .out 0 [CopyResult.completed.toNat],
  .mem 0 8 [42],
  -- both parked, then a splice re-issues the copy
  op (.futureNew u8), .out 0 (ends 9 3),
  op (.futureNew u8), .out 0 (ends 10 11),
  op (.memSet 0 [43]),
  op (.copy .futureW u8 true 3 0 1), .out 0 [BLOCKED],
  op (.copy .futureR u8 true 10 8 1), .out 0 [BLOCKED],
  op (.forward false u8 9 11),
  .mem 0 8 [43],
  -- forwarding into a future whose reader is gone
  op (.futureNew u8), .out 0 (ends 11 9),
  op (.futureNew u8), .out 0 (ends 12 13),
  op (.dropEnd .futureR u8 12),
  op (.forward false u8 11 13),
  op (.copy .futureW u8 true 9 0 1), .out 0 [CopyResult.dropped.toNat],
  op (.dropEnd .futureW u8 9),
  op (.coreReturn []), .exited 0]

/-! ## `test_receive_own_stream` (L1810–1846) -/

/-- The script. The readable end goes to the host and comes back with the same index. -/
def receiveOwnStream : List Chk := [
  .step (.invoke (.guest 0 true false false 0) []),
  op (.streamNew u8), .out 0 (ends 1 2),
  op (.copy .streamW u8 true 2 0 4), .out 0 [BLOCKED],
  op (.lower .host true [.readable true u8 1]),
  op .hostStart, .hostArgs 1 [.end_ 0],
  op (.hostResolve [.end_ 0]), op .hostExit,
  .out 0 [sReturned], .stored 0 [1],
  op (.cancelCopy .streamW u8 false 2 false), .out 0 [packed .cancelled 0],
  op (.dropEnd .streamW u8 2),
  op (.coreReturn []), .exited 0, .hostResult 0 (some [])]

/-! ## `test_self_copy` (L2780–2857) -/

/-- The script for the element type `t` (`None`, `U8` and `F64` in `run_tests.py`). -/
def selfCopy (t : Ty) : List Chk := [
  .step (.invoke (.guest 0 true false false 0) []),
  op .wsNew, .out 0 [1],
  op (.futureNew t), .out 0 (ends 2 3),
  op (.copy .futureW t true 3 0 1), .out 0 [BLOCKED],
  op (.copy .futureR t true 2 0 1), .out 0 [CopyResult.completed.toNat],
  op (.dropEnd .futureR t 2),
  op (.join 3 1),
  op (.wsWait 1), tick 0,
  .out 0 [EventCode.futureWrite.toNat, 3, CopyResult.completed.toNat],
  op (.dropEnd .futureW t 3),
  op (.streamNew t), .out 0 (ends 3 2),
  op (.copy .streamW t true 2 0 3), .out 0 [BLOCKED],
  op (.copy .streamR t true 3 0 1), .out 0 [packed .completed 1],
  op (.copy .streamR t true 3 0 4), .out 0 [packed .completed 2],
  op (.dropEnd .streamR t 3),
  op (.join 2 1),
  op (.wsWait 1), tick 0,
  .out 0 [EventCode.streamWrite.toNat, 2, packed .dropped 3],
  op (.dropEnd .streamW t 2),
  -- a completed zero-length read is not a pending one
  op (.streamNew t), .out 0 (ends 2 3),
  op (.copy .streamR t true 2 0 0), .out 0 [BLOCKED],
  op (.copy .streamW t true 3 0 1), .out 0 [BLOCKED],
  op (.cancelCopy .streamW t true 3 false), .out 0 [packed .cancelled 0],
  op (.copy .streamW t true 3 0 0), .out 0 [BLOCKED],
  op (.cancelCopy .streamR t true 2 false), .out 0 [packed .cancelled 0],
  op (.cancelCopy .streamW t true 3 false), .out 0 [packed .cancelled 0],
  op (.dropEnd .streamR t 2),
  op (.dropEnd .streamW t 3),
  op (.wsDrop 1),
  op (.coreReturn []), .exited 0]

/-! ## `test_wasm_to_wasm_stream` (L1933–2063) -/

/-- The script. Instance 0 runs `core_func1` (thread 1; a sync function type returning a
stream, async options), instance 1 `core_func2` (thread 0; a sync function type invoked by
the embedder, so `Store.invoke` runs the `canon lift` loop until it calls `task.return`).
Flags 1–4 are `fut1`–`fut4`. -/
def wasmToWasmStream : List Chk := [
  .step (.invoke (.guest 1 false true false 0) []),
  op (.taskReturn 0 []), .hostResult 0 (some []),
  op (.lower (.guest 0 false true false 3) true []),
  op (.streamNew u8), .out 1 (ends 1 2),
  op (.taskReturnL 3 [.readable true u8 1]),
  op (.waitFlag 1),
  .out 0 [sReturned], .stored 0 [1],
  op (.copy .streamR u8 true 1 0 8), .out 0 [BLOCKED],
  op (.setFlag 1),
  op .wsNew, .out 0 [2],
  op (.join 1 2),
  op (.wsWait 2),
  tick 1,
  op (.memSet 0 [1, 2, 3, 4]),
  op (.copy .streamW u8 true 2 0 4), .out 1 [packed .completed 4],
  op (.copy .streamW u8 true 2 0 4), .out 1 [packed .completed 4],
  op (.copy .streamW u8 true 2 0 0), .out 1 [BLOCKED],
  op (.cancelCopy .streamW u8 true 2 false), .out 1 [packed .cancelled 0],
  op (.waitFlag 2),
  tick 0, .out 0 [EventCode.streamRead.toNat, 1, packed .completed 8],
  .mem 1 0 [1, 2, 3, 4, 1, 2, 3, 4],
  op (.setFlag 2),
  op (.waitFlag 3),
  tick 1,
  op (.memSet 0 [5, 6, 7, 8, 9, 10, 11, 12]),
  op (.copy .streamW u8 true 2 0 8), .out 1 [BLOCKED],
  op (.setFlag 3),
  op .wsNew, .out 1 [1],
  op (.join 2 1),
  op (.wsWait 1),
  tick 0,
  op (.copy .streamR u8 true 1 12345 0), .out 0 [packed .completed 0],
  op (.memSet 0 [0, 0, 0, 0, 0, 0, 0, 0]),
  op (.copy .streamR u8 true 1 0 2), .out 0 [packed .completed 2],
  .mem 1 0 [5, 6, 0, 0, 0, 0],
  op (.copy .streamR u8 true 1 2 2), .out 0 [packed .completed 2],
  .mem 1 0 [5, 6, 7, 8, 0, 0],
  op (.waitFlag 4),
  tick 1, .out 1 [EventCode.streamWrite.toNat, 2, packed .completed 4],
  op (.copy .streamW u8 true 2 12345 0), .out 1 [BLOCKED],
  op (.setFlag 4),
  op (.wsWait 1),
  tick 0,
  op (.copy .streamR u8 true 1 12345 0), .out 0 [BLOCKED],
  op (.wsWait 2),
  tick 1, .out 1 [EventCode.streamWrite.toNat, 2, 0],
  op (.copy .streamW u8 true 2 12345 0), .out 1 [0],
  op (.errNew 0), .out 1 [3],
  op (.dropEnd .streamW u8 2),
  op (.wsDrop 1),
  op (.errDrop 3),
  op .coreExit, .exited 1,
  tick 0, .out 0 [EventCode.streamRead.toNat, 1, packed .dropped 0],
  op (.dropEnd .streamR u8 1),
  op (.wsDrop 2),
  op .coreExit, .exited 0]

/-! ## `test_wasm_to_wasm_stream_empty` (L2066–2162) -/

/-- The script: `test_wasm_to_wasm_stream` with element type `None` (no memory is touched). -/
def wasmToWasmStreamEmpty : List Chk := [
  .step (.invoke (.guest 1 false true false 0) []),
  op (.taskReturn 0 []),
  op (.lower (.guest 0 false true false 4) true []),
  op (.streamNew tnone), .out 1 (ends 1 2),
  op (.taskReturnL 4 [.readable true tnone 1]),
  op (.waitFlag 1),
  .out 0 [sReturned], .stored 0 [1],
  op (.copy .streamR tnone true 1 0 8), .out 0 [BLOCKED],
  op (.setFlag 1),
  op .wsNew, .out 0 [2],
  op (.join 1 2),
  op (.wsWait 2),
  tick 1,
  op (.copy .streamW tnone true 2 10000 2), .out 1 [packed .completed 2],
  op (.copy .streamW tnone true 2 10000 2), .out 1 [packed .completed 2],
  op (.waitFlag 2),
  tick 0, .out 0 [EventCode.streamRead.toNat, 1, packed .completed 4],
  op (.setFlag 2),
  op (.waitFlag 3),
  tick 1,
  op (.copy .streamW tnone true 2 0 8), .out 1 [BLOCKED],
  op (.setFlag 3),
  op .wsNew, .out 1 [1],
  op (.join 2 1),
  op (.wsWait 1),
  tick 0,
  op (.copy .streamR tnone true 1 1000000 2), .out 0 [packed .completed 2],
  op (.copy .streamR tnone true 1 1000000 2), .out 0 [packed .completed 2],
  op (.waitFlag 4),
  tick 1, .out 1 [EventCode.streamWrite.toNat, 2, packed .completed 4],
  op (.setFlag 4),
  op (.errNew 0), .out 1 [3],
  op (.dropEnd .streamW tnone 2),
  op (.errDrop 3),
  op .coreExit, .exited 1,
  tick 0,
  op (.copy .streamR tnone true 1 1000000 2), .out 0 [packed .dropped 0],
  op (.dropEnd .streamR tnone 1),
  op .coreExit, .exited 0]

/-! ## `test_async_flat_params` (L2860–2906) -/

/-- The script. The host callees receive their arguments in order; `1.1` and `2.2` are
represented by the tags `11` and `22` (values are opaque here), and the third call's
arguments, which Python passes through memory (more than `MAX_FLAT_ASYNC_PARAMS`), are
given as values. -/
def asyncFlatParams : List Chk := [
  .step (.invoke (.guest 0 false true false 0) []),
  op (.lower .host true [.num 11, .num 22, .num 3, .num 4]),
  op .hostStart, .hostArgs 1 [.num 11, .num 22, .num 3, .num 4],
  op (.hostResolve []), op .hostExit, .out 0 [sReturned],
  op (.lower .host true [.num 1, .num 2, .num 3, .num 4]),
  op .hostStart, .hostArgs 2 [.num 1, .num 2, .num 3, .num 4],
  op (.hostResolve []), op .hostExit, .out 0 [sReturned],
  op (.lower .host true [.num 1, .num 2, .num 3, .num 4, .num 5]),
  op .hostStart, .hostArgs 3 [.num 1, .num 2, .num 3, .num 4, .num 5],
  op (.hostResolve []), op .hostExit, .out 0 [sReturned],
  op (.taskReturn 0 []), op .coreExit, .exited 0, .hostResult 0 (some [])]

/-! ## `test_threads` (L2909–2975) -/

/-- The script. Thread 0 is the main thread (index 1 in the instance's thread table); threads
1–3 run `thread_func1`–`thread_func3`, threads 4–8 `thread_func4` on the cell `4`. -/
def threads : List Chk := [
  .step (.invoke (.guest 0 true false false 1) []),
  op .threadIndex, .out 0 [1],
  op (.threadNewIndirect 13), .out 0 [2],
  op (.threadYieldThenResume 2), .out 1 [13], op .threadExit, .exited 1,
  tick 0, .out 0 [0],
  op (.threadNewIndirect 1), .out 0 [2],
  op (.threadSuspendThenResume 2), .out 2 [1],
  op (.threadYieldThenResume 1), .out 0 [0],
  op (.threadNewIndirect 1), .out 0 [3],
  op (.threadResumeLater 3),
  op .threadSuspend,
  tick 3, .out 3 [1], op (.threadResumeLater 1), op .threadExit, .exited 3,
  tick 2, .out 2 [0], op .threadExit, .exited 2,
  tick 0, .out 0 [0],
  op (.memSet 4 [0]),
  op (.threadNewIndirect 4), .out 0 [2], op (.threadResumeLater 2),
  op (.threadNewIndirect 4), .out 0 [3], op (.threadResumeLater 3),
  op (.threadNewIndirect 4), .out 0 [4], op (.threadResumeLater 4),
  op (.threadNewIndirect 4), .out 0 [5], op (.threadResumeLater 5),
  op (.threadNewIndirect 4), .out 0 [6], op (.threadResumeLater 6),
  -- `while mem[ptr] != 10: canon_thread_yield()`
  .mem 0 4 [0], op .threadYield,
  tick 4, .out 4 [4], op .threadYield,
  tick 5, .out 5 [4], op .threadYield,
  tick 6, .out 6 [4], op .threadYield,
  tick 7, .out 7 [4], op .threadYield,
  tick 8, .out 8 [4], op .threadYield,
  tick 4, op (.memSet 4 [1]), op .threadYield,
  tick 5, op (.memSet 4 [2]), op .threadYield,
  tick 6, op (.memSet 4 [3]), op .threadYield,
  tick 7, op (.memSet 4 [4]), op .threadYield,
  tick 8, op (.memSet 4 [5]), op .threadYield,
  tick 4, op (.memSet 4 [6]), op .threadExit,
  tick 5, op (.memSet 4 [7]), op .threadExit,
  tick 6, op (.memSet 4 [8]), op .threadExit,
  tick 7, op (.memSet 4 [9]), op .threadExit,
  tick 8, op (.memSet 4 [10]), op .threadExit,
  tick 0, .out 0 [0], .mem 0 4 [10],
  op (.coreReturn [42]), .exited 0, .hostResult 0 (some [.num 42])]

/-- All scripts of this module, with their initial number of instances. -/
def all2 : List (String × Nat × List Chk) := [
  ("test_async_to_async", 2, asyncToAsync),
  ("test_sync_using_wait", 2, syncUsingWait),
  ("test_async_to_sync", 2, asyncToSync),
  ("test_callback_interleaving", 2, callbackInterleaving),
  ("test_sync_ignores_backpressure", 2, syncIgnoresBackpressure),
  ("test_forward", 1, forward),
  ("test_receive_own_stream", 1, receiveOwnStream),
  ("test_self_copy(None)", 1, selfCopy tnone),
  ("test_self_copy(U8Type())", 1, selfCopy u8),
  ("test_self_copy(F64Type())", 1, selfCopy f64),
  ("test_wasm_to_wasm_stream", 2, wasmToWasmStream),
  ("test_wasm_to_wasm_stream_empty", 2, wasmToWasmStreamEmpty),
  ("test_async_flat_params", 1, asyncFlatParams),
  ("test_threads", 1, threads)]

end Silmaril.Wasm.Component.Async.Cabi.Oracle
