module

public import Silmaril.Wasm.Component.Async.CabiOracle2.Defs

@[expose] public section

/-!
# `run_tests.py`'s `test_cancel_subtask` and `test_sync_threads` as scripts

`test_cancel_subtask` (L2440–2777) of `design/mvp/canonical-abi/run_tests.py` at
component-model `d095e2f`: `subtask.cancel` of tasks waiting to enter, waiting in the callback
event loop, after `YIELD`, while another task holds the exclusive thread, while blocked in a
sync import call, and of a stackful task that ignores the request. The memory cells the
Python test inspects (`caller_heap.memory[0]`, `[4]`) are the results the subtasks store
(`Oracle.Chk.stored`).

Instance 0 is the callee instance, 1 the caller (`caller_opts` async, stackful); all callees
have the function type `[u8] -> [u8]` (result tag `1`). Callback callees (`callee_wait`,
`callee_yield`, `callee_lock_hog`, `callee_sync_import`) are `cbCallee`; the stackful ones
(`callee_never_started`, `callee_ignores_cancel`) `stackful`. Thread `k + 1` is the implicit
thread of task `k + 1`, the callee of subtask `k` (the host functions take a task and a
thread too).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

open Silmaril.Wasm.Component.Async.Cabi

/-- A callee with the callback ABI. -/
def cbCallee : Callee := .guest 0 true true true 1

/-- A stackful async callee. -/
def stackful : Callee := .guest 0 true true false 1

/-- `TASK_CANCELLED`. -/
def evCancelled : List Nat := [EventCode.taskCancelled.toNat, 0, 0]

/-- `core_wait` with argument `x` and its new waitable set `si` (instance 0's handle):
`context.set(x)`, `waitable-set.new`, `WAIT`. -/
def coreWait (th x si : Nat) : List Chk :=
  [.out th [x], op (.contextSet 0 x), op .wsNew, .out th [si], op (.cbReturn (2 + 16 * si))]

/-- `core_yield` with argument `x`: `context.set(x)`, `YIELD`. -/
def coreYield (th x : Nat) : List Chk := [.out th [x], op (.contextSet 0 x), op (.cbReturn 1)]

/-- The script. -/
def cancelSubtask : List Chk := [
  .step (.invoke (.guest 1 true true false 1) [.num 1]), .out 0 [1],
  op .wsNew, .out 0 [1],
  -- tasks blocked on backpressure are cancelled without running
  .step (.setBackpressure 0 1),
  op (.lower stackful true [.num 13]), .out 0 [sStarting + 16 * 2],
  op (.lower stackful true [.num 13]), .out 0 [sStarting + 16 * 3],
  op (.subtaskCancel false 3), .out 0 [SubState.cancelledBeforeStarted.toNat], .exited 2,
  op (.subtaskCancel true 2), .out 0 [SubState.cancelledBeforeStarted.toNat], .exited 1,
  .step (.setBackpressure 0 0),
  -- six `callee_wait` tasks (threads 3–8, sets 1–6 of instance 0, handles 4–9)
  op (.lower cbCallee true [.num 1])] ++ coreWait 3 1 1 ++ [.out 0 [sStarted + 16 * 4],
  op (.lower cbCallee true [.num 2])] ++ coreWait 4 2 2 ++ [.out 0 [sStarted + 16 * 5],
  op (.lower cbCallee true [.num 3])] ++ coreWait 5 3 3 ++ [.out 0 [sStarted + 16 * 6],
  op (.lower cbCallee true [.num 3])] ++ coreWait 6 3 4 ++ [.out 0 [sStarted + 16 * 7],
  op (.lower cbCallee true [.num 4])] ++ coreWait 7 4 5 ++ [.out 0 [sStarted + 16 * 8],
  op (.lower cbCallee true [.num 4])] ++ coreWait 8 4 6 ++ [.out 0 [sStarted + 16 * 9],
  -- x = 1: resumed with `TASK_CANCELLED`, returns 42
  op (.subtaskCancel false 4), .out 3 evCancelled,
  op (.contextGet 0), .out 3 [1], op (.taskReturn 1 [.num 42]), op (.cbReturn 0), .exited 3,
  .out 0 [sReturned], .stored 2 [42],
  op (.subtaskDrop 4),
  -- x = 2: `task.cancel`
  op (.subtaskCancel true 5), .out 4 evCancelled,
  op (.contextGet 0), .out 4 [2], op .taskCancel, op (.cbReturn 0), .exited 4,
  .out 0 [SubState.cancelledBeforeReturned.toNat], .stored 3 [],
  op (.subtaskDrop 5),
  -- x = 3, async cancel: `YIELD`, then returns 43
  op (.subtaskCancel true 6), .out 5 evCancelled,
  op (.contextGet 0), .out 5 [3], op (.cbReturn 1),
  .out 0 [BLOCKED], .stored 4 [],
  op (.join 6 1),
  op (.wsWait 1),
  tick 5, .out 5 [0, 0, 0], op (.contextGet 0), op (.taskReturn 1 [.num 43]), op (.cbReturn 0),
  .exited 5,
  tick 0, .out 0 (subEv 6 sReturned), .stored 4 [43],
  op (.subtaskDrop 6),
  -- x = 3, sync cancel: the caller waits for the subtask
  op (.subtaskCancel false 7), .out 6 evCancelled,
  op (.contextGet 0), .out 6 [3], op (.cbReturn 1),
  tick 6, .out 6 [0, 0, 0], op (.contextGet 0), op (.taskReturn 1 [.num 43]), op (.cbReturn 0),
  .exited 6,
  tick 0, .out 0 [sReturned], .stored 5 [43],
  op (.subtaskDrop 7),
  -- x = 4, async cancel: `YIELD`, then `task.cancel`
  op (.subtaskCancel true 8), .out 7 evCancelled,
  op (.contextGet 0), .out 7 [4], op (.cbReturn 1),
  .out 0 [BLOCKED],
  op (.join 8 1),
  op (.wsWait 1),
  tick 7, .out 7 [0, 0, 0], op (.contextGet 0), op .taskCancel, op (.cbReturn 0), .exited 7,
  tick 0, .out 0 (subEv 8 SubState.cancelledBeforeReturned.toNat), .stored 6 [],
  op (.subtaskDrop 8),
  -- x = 4, sync cancel
  op (.subtaskCancel false 9), .out 8 evCancelled,
  op (.contextGet 0), .out 8 [4], op (.cbReturn 1),
  tick 8, .out 8 [0, 0, 0], op (.contextGet 0), op .taskCancel, op (.cbReturn 0), .exited 8,
  tick 0, .out 0 [SubState.cancelledBeforeReturned.toNat], .stored 7 [],
  op (.subtaskDrop 9),
  -- cancelling a subtask that already returned reports `RETURNED` (thread 9)
  op (.lower cbCallee true [.num 83])] ++ coreYield 9 83 ++ [.out 0 [sStarted + 16 * 9],
  op .threadYield,
  tick 9, .out 9 [0, 0, 0], op (.contextGet 0), op (.taskReturn 1 [.num 83]), op (.cbReturn 0),
  .exited 9,
  tick 0, .out 0 [0],
  op (.subtaskCancel true 9), .out 0 [sReturned], .stored 8 [83],
  op (.subtaskDrop 9),
  -- a task that returned `YIELD` is cancellable at once (thread 10)
  op (.lower cbCallee true [.num 83])] ++ coreYield 10 83 ++ [.out 0 [sStarted + 16 * 9],
  op (.subtaskCancel true 9), .out 10 evCancelled,
  op (.contextGet 0), op .taskCancel, op (.cbReturn 0), .exited 10,
  .out 0 [SubState.cancelledBeforeReturned.toNat], .stored 9 [],
  op (.subtaskDrop 9),
  -- the lock hog (thread 12) delays the cancellation of `callee_wait` (thread 11)
  op (.lower cbCallee true [.num 1])] ++ coreWait 11 1 7 ++ [.out 0 [sStarted + 16 * 9],
  op (.lower cbCallee true [.num 45]), .out 12 [45], op .threadYield,
  .out 0 [sStarted + 16 * 8],
  op (.subtaskCancel true 9), .out 0 [BLOCKED], .stored 10 [],
  op (.join 9 1),
  op (.wsWait 1),
  tick 12, .out 12 [0], op (.taskReturn 1 [.num 45]), op (.cbReturn 0), .exited 12,
  tick 11, .out 11 evCancelled, op (.contextGet 0), .out 11 [1],
  op (.taskReturn 1 [.num 42]), op (.cbReturn 0), .exited 11,
  tick 0, .out 0 (subEv 9 sReturned), .stored 10 [42], .stored 11 [45],
  op (.subtaskDrop 9),
  op (.join 8 1),
  op (.wsWait 1),
  tick 0, .out 0 (subEv 8 sReturned),
  op (.subtaskDrop 8),
  -- the same for `callee_yield` (thread 13) and a second lock hog (thread 14)
  op (.lower cbCallee true [.num 1])] ++ coreYield 13 1 ++ [.out 0 [sStarted + 16 * 8],
  op (.lower cbCallee true [.num 45]), .out 14 [45], op .threadYield,
  .out 0 [sStarted + 16 * 9],
  op (.subtaskCancel true 8), .out 0 [BLOCKED], .stored 12 [],
  op (.join 8 1),
  op (.wsWait 1),
  tick 14, .out 14 [0], op (.taskReturn 1 [.num 45]), op (.cbReturn 0), .exited 14,
  tick 13, .out 13 evCancelled, op (.contextGet 0), .out 13 [1],
  op .taskCancel, op (.cbReturn 0), .exited 13,
  tick 0, .out 0 (subEv 8 SubState.cancelledBeforeReturned.toNat), .stored 12 [],
  .stored 13 [45],
  op (.subtaskDrop 8),
  op (.join 9 1),
  op (.wsWait 1),
  tick 0, .out 0 (subEv 9 sReturned),
  op (.subtaskDrop 9),
  -- blocked in a sync import call (thread 15; the host function is thread 16, flag 1)
  op (.lower cbCallee true [.num 0]), .out 15 [0],
  op (.lower .host false [.num 42]), op .hostStart, .hostArgs 16 [.num 42], op (.waitFlag 1),
  .out 0 [sStarted + 16 * 9],
  op (.subtaskCancel true 9), .out 0 [BLOCKED], .stored 14 [],
  op (.setFlag 1),
  op (.join 9 1),
  op (.wsWait 1),
  tick 16, op (.hostResolve [.num 43]), op .hostExit, .exited 16,
  tick 15, .out 15 [43],
  .trap .taskCancel,
  op .wsNew, .out 15 [8],
  op (.contextSet 0 8),
  op (.cbReturn (2 + 16 * 8)), .out 15 evCancelled,
  op (.contextGet 0), .out 15 [8],
  op (.wsPoll 8), .out 15 [0, 0, 0],
  op .taskCancel, op (.cbReturn 0), .exited 15,
  tick 0, .out 0 (subEv 9 SubState.cancelledBeforeReturned.toNat), .stored 14 [],
  op (.subtaskDrop 9),
  -- a stackful task ignores the request (thread 17; the host function is thread 18, flag 2)
  op (.lower stackful true [.num 13]), .out 17 [13],
  op (.lower .host true [.num 42]), op .hostStart, .hostArgs 18 [.num 42], op (.waitFlag 2),
  .out 17 [sStarted + 16 * 9],
  op (.subtaskCancel false 9),
  .out 0 [sStarted + 16 * 9],
  op (.subtaskCancel true 9), .out 0 [BLOCKED], .stored 16 [],
  op (.setFlag 2),
  op (.join 9 1),
  op (.wsWait 1),
  tick 18, op (.waitFlag 2),
  tick 18, op (.hostResolve [.num 43]), op .hostExit, .exited 18,
  tick 17, .out 17 [sReturned],
  op (.subtaskDrop 9),
  op (.taskReturn 1 [.num 44]), op .coreExit, .exited 17,
  tick 0, .out 0 (subEv 9 sReturned), .stored 16 [44],
  op (.subtaskDrop 9),
  op (.wsDrop 1),
  op (.taskReturn 1 [.num 42]), op .coreExit, .exited 0,
  .hostResult 0 (some [.num 42])]

/-! ## `test_sync_threads` (L2978–3123) -/

/-- The script. Thread 0 runs `async_task_thread` (sync options, waiting for `ready_bit`,
flag 1); thread 1 runs `core_func` of the sync-typed export, so the embedder's `canon lift`
loop resumes ready threads of the instance until `thread_func5_1` calls `task.return`. Its
choices are `loopPicks`. Threads 2–9 run `thread_func1_1`, `1_2`, `2`, `3`, `4_1`, `4_2`,
`5_1`, `5_2` (thread-table indices 3–10). -/
def syncThreads : List Chk := [
  .step (.invoke (.guest 0 true false false 2) []),
  op (.waitFlag 1),
  op (.setFlag 1),
  .step (.loopPicks [0, 2, 3, 2, 3, 2, 3, 2, 3, 4, 5, 6, 5, 7, 6, 8, 8, 8, 8]),
  .step (.invoke (.guest 0 false true false 1) []),
  op (.threadNewIndirect 131), .out 1 [3],
  op (.threadNewIndirect 132), .out 1 [4],
  op (.threadNewIndirect 14), .out 1 [5],
  op (.threadNewIndirect 15), .out 1 [6],
  op (.threadNewIndirect 161), .out 1 [7],
  op (.threadNewIndirect 162), .out 1 [8],
  op (.threadNewIndirect 171), .out 1 [9],
  op (.threadNewIndirect 172), .out 1 [10],
  op (.threadResumeLater 3), op (.threadResumeLater 4),
  op .coreExit, .exited 1,
  -- the loop resumes `async_task_thread`, which returns 43
  .out 0 [], op (.coreReturn [43]), .exited 0, .hostResult 0 (some [.num 43]),
  -- ping and pong
  .out 2 [131], op .threadYield,
  .out 3 [132], op .threadYield,
  .out 2 [0], op .threadYield,
  .out 3 [0], op .threadYield,
  .out 2 [0], op .threadYield,
  .out 3 [0], op .threadYield,
  .out 2 [0], op (.threadResumeLater 5), op .threadExit, .exited 2,
  .out 3 [0], op .threadExit, .exited 3,
  .out 4 [14], op (.threadResumeLater 6), op .threadExit, .exited 4,
  .out 5 [15], op (.threadResumeLater 7), op .threadSuspend,
  .out 6 [161], op (.threadResumeLater 6), op (.threadResumeLater 8),
  op .wsNew, .out 6 [1], op (.wsWait 1),
  .out 5 [0], op .threadExit, .exited 5,
  .out 7 [162], op (.futureNew tnone), .out 7 (ends 2 3),
  op (.copy .futureR tnone true 2 0xdeadbeef 1), .out 7 [BLOCKED],
  op (.join 2 1),
  op (.copy .futureW tnone true 3 0xdeadbeef 1), .out 7 [CopyResult.completed.toNat],
  op .threadExit, .exited 7,
  .out 6 [EventCode.futureRead.toNat, 2, CopyResult.completed.toNat],
  op (.threadResumeLater 9), op .threadExit, .exited 6,
  -- `thread_func5_1` and `thread_func5_2`: promotions
  .out 8 [171], op (.threadYieldThenPromote 10),
  .out 8 [0], op (.threadResumeLater 10), op (.threadYieldThenPromote 10),
  .out 9 [172], op (.threadSuspendThenPromote 9),
  .out 8 [0], op (.threadYieldThenPromote 10),
  .out 8 [0], op (.threadResumeLater 10), op (.threadYieldThenPromote 10),
  .out 9 [0], op (.threadSuspendThenPromote 9),
  .out 8 [0], op (.threadYieldThenPromote 10),
  .out 8 [0], op (.threadResumeLater 10), op (.threadYieldThenPromote 10),
  .out 9 [0], op (.threadSuspendThenPromote 9),
  .out 8 [0],
  op (.taskReturn 1 [.num 42]), .hostResult 1 (some [.num 42]),
  op (.threadResumeLater 10), op .threadExit, .exited 8,
  -- the top-level tick resumes `thread_func5_2`, which exits
  tick 9, .out 9 [0], op .threadExit, .exited 9]

/-- The scripts of this module, with their initial number of instances. -/
def all4 : List (String × Nat × List Chk) := [
  ("test_cancel_subtask", 2, cancelSubtask),
  ("test_sync_threads", 1, syncThreads)]

end Silmaril.Wasm.Component.Async.Cabi.Oracle
