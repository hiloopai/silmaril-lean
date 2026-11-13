module

public import Silmaril.Wasm.Component.Async.CabiOracle2.Defs

@[expose] public section

/-!
# `run_tests.py` stream tests with host pumps, as scripts

The tests of `design/mvp/canonical-abi/run_tests.py` (component-model `d095e2f`) whose host
side uses the re-entrant `HostWriter`/`HostReader` helpers: their `pump` runs inside the
guest's `stream.read`/`stream.write`/`drop` (between `End.copy` and the canon built-in's own
`has_pending_event` check), which the transcription models with pumps hooked to ends
(`Cabi.Pump`, `Cabi.Store.copyH`/`dropH`). The host code of a test (`HostWriter(...)`,
`set_remain`, `write`, `end_when_empty`, `on_resolve`) is a step of the script at the place
where Python runs it.

| Script | `run_tests.py` | What it exercises |
|---|---|---|
| `transferReadableEnd` | `test_transfer_readable_end` (L1687) | a readable end lowered into and lifted out of a sync-typed export, also after its writer dropped |
| `eagerStreamCompletion` | `test_eager_stream_completion` (L1490) | pumps completing copies inside the guest's copy (sync and async), `add10` forwarding |
| `asyncStreamOps` | `test_async_stream_ops` (L1572) | async copies, a host thread waiting for its reader, `DROPPED` after the last chunk |

Pumps are numbered in creation order; `HostWriter` creates a stream (readable end first).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

open Silmaril.Wasm.Component.Async.Cabi

/-- `add10` of `test_eager_stream_completion` and `test_async_stream_ops`. -/
def add10 : Nat → Nat := (· + 10)

/-! ## `test_transfer_readable_end` (L1687–1716) -/

/-- The script. Pump 0 is the first `HostWriter` (ends 0, 1), pump 1 the second (ends 2, 3;
it drops its writable end at once), pump 2 the final `HostReader`. -/
def transferReadableEnd : List Chk := [
  .step (.writerNew u8 [1, 2, 3, 4] 4 true),
  .step (.invoke (.guest 0 false false false 3) [.end_ 0]),
  .out 0 [1], op (.coreReturnL [.readable true u8 1]), .exited 0,
  .hostResult 0 (some [.end_ 0]),
  .step (.writerNew u8 [] MAX_LENGTH true),
  .step (.invoke (.guest 0 false false false 3) [.end_ 2]),
  .out 1 [1], op (.coreReturnL [.readable true u8 1]), .exited 1,
  .hostResult 1 (some [.end_ 2]),
  .step (.readerNew 2 MAX_LENGTH none),
  .reader 2 [] true]

/-! ## `test_eager_stream_completion` (L1490–1569) -/

/-- The script. Pump 0: the embedder's `HostWriter([1..8], chunk = 4)` (ends 0, 1); pump 1:
the embedder's `HostReader` of the returned stream (ends 2, 3); host thread 1 runs
`host_func` with its `HostWriter` (pump 2, ends 6, 7) and its `HostReader` of the incoming
stream (pump 3, ends 4, 5) with `on_data = add10`. -/
def eagerStreamCompletion : List Chk := [
  .step (.writerNew u8 [1, 2, 3, 4, 5, 6, 7, 8] 4 true),
  .step (.invoke (.guest 0 false true false 3) [.end_ 0]),
  .out 0 [1],
  op (.streamNew u8), .out 0 (ends 2 3),
  op (.taskReturnL 3 [.readable true u8 2]), .hostResult 0 (some [.end_ 2]),
  .step (.readerNew 2 MAX_LENGTH none),
  op (.copy .streamR u8 true 1 0 4), .out 0 [packed .completed 4], .mem 0 0 [1, 2, 3, 4],
  op (.streamNew u8), .out 0 (ends 2 4),
  op (.lower .host true [.readable true u8 2]),
  op .hostStart, .hostArgs 1 [.end_ 4],
  .step (.writerNew u8 [] 4 false),
  .step (.readerNew 4 MAX_LENGTH (some (2, add10))),
  op (.hostResolve [.end_ 6]), op .hostExit,
  .out 0 [sReturned], .stored 0 [2],
  op (.copy .streamW u8 true 4 0 4), .out 0 [packed .completed 4],
  op (.copy .streamR u8 false 2 0 4), .out 0 [packed .completed 4],
  .mem 0 0 [11, 12, 13, 14],
  op (.copy .streamW u8 true 3 0 4), .out 0 [packed .completed 4],
  op (.copy .streamR u8 true 1 0 4), .out 0 [packed .dropped 4], .mem 0 0 [5, 6, 7, 8],
  op (.copy .streamW u8 false 4 0 4), .out 0 [packed .completed 4],
  op (.copy .streamR u8 false 2 0 4), .out 0 [packed .completed 4],
  op (.copy .streamW u8 false 3 0 4), .out 0 [packed .completed 4],
  op (.dropEnd .streamR u8 1), op (.dropEnd .streamR u8 2),
  op (.dropEnd .streamW u8 3), op (.dropEnd .streamW u8 4),
  op .coreExit, .exited 0,
  .reader 1 [11, 12, 13, 14, 15, 16, 17, 18] true]

/-! ## `test_async_stream_ops` (L1572–1684) -/

/-- The script. Pump 0: `host_writer2` (ends 0, 1); pump 1: `host_reader2` of the returned
stream (ends 2, 3); host thread 1 runs `host_func` with `host_reader` (pump 2, ends 4, 5) and
`host_writer` (pump 3, ends 6, 7), and loops `wait_until(received or dropped)`, `take`,
`write(add10)`. -/
def asyncStreamOps : List Chk := [
  .step (.writerNew u8 [] 4 false),
  .step (.invoke (.guest 0 true true false 3) [.end_ 0]),
  .out 0 [1],
  op (.streamNew u8), .out 0 (ends 2 3),
  op (.taskReturnL 3 [.readable true u8 2]), .hostResult 0 (some [.end_ 2]),
  .step (.readerNew 2 0 none),
  op (.copy .streamR u8 true 1 0 4), .out 0 [BLOCKED],
  .step (.writerWrite 0 [1, 2, 3, 4]),
  op .wsNew, .out 0 [2],
  op (.join 1 2),
  op (.wsWait 2), tick 0,
  .out 0 [EventCode.streamRead.toNat, 1, packed .completed 4], .mem 0 0 [1, 2, 3, 4],
  op (.streamNew u8), .out 0 (ends 4 5),
  op (.lower .host true [.readable true u8 4]),
  op .hostStart, .hostArgs 1 [.end_ 4],
  .step (.readerNew 4 0 none),
  .step (.writerNew u8 [] 4 false),
  op (.hostResolve [.end_ 6]),
  op (.hostWaitReader 2),
  .out 0 [sReturned], .stored 0 [4],
  op (.copy .streamW u8 true 5 0 4), .out 0 [BLOCKED],
  .step (.readerSetRemain 2 100),
  op (.join 5 2),
  op (.wsWait 2),
  tick 1, .step (.readerTakeTo 2 3 add10), op (.hostWaitReader 2),
  tick 0, .out 0 [EventCode.streamWrite.toNat, 5, packed .completed 4],
  op (.copy .streamR u8 false 4 0 4), .out 0 [packed .completed 4],
  op (.copy .streamW u8 true 3 0 4), .out 0 [BLOCKED],
  .step (.readerSetRemain 1 100),
  op (.join 3 2),
  op (.wsWait 2), tick 0,
  .out 0 [EventCode.streamWrite.toNat, 3, packed .completed 4],
  .step (.writerWrite 0 [5, 6, 7, 8]),
  .step (.writerEndWhenEmpty 0),
  op (.copy .streamR u8 true 1 0 4), .out 0 [packed .dropped 4], .mem 0 0 [5, 6, 7, 8],
  op (.dropEnd .streamR u8 1),
  op (.copy .streamW u8 true 5 0 4), .out 0 [packed .completed 4],
  op (.dropEnd .streamW u8 5),
  op (.copy .streamR u8 true 4 0 4), .out 0 [BLOCKED],
  op (.join 4 2),
  op (.wsWait 2),
  tick 1, .step (.readerTakeTo 2 3 add10), op (.hostWaitReader 2),
  tick 0, .out 0 [EventCode.streamRead.toNat, 4, packed .completed 4],
  op (.join 4 0),
  .step (.writerEndWhenEmpty 3),
  op (.copy .streamR u8 false 4 0 4), .out 0 [packed .dropped 0],
  op (.dropEnd .streamR u8 4),
  op (.copy .streamW u8 true 3 0 4), .out 0 [packed .completed 4],
  op (.dropEnd .streamW u8 3),
  op (.wsDrop 2),
  op .coreExit, .exited 0,
  -- the host thread finds the reader dropped and returns
  tick 1, .step (.readerTakeTo 2 3 add10), op .hostExit, .exited 1,
  .reader 1 [11, 12, 13, 14, 15, 16, 17, 18] true]

/-- All scripts of this module, with their initial number of instances. -/
def all3 : List (String × Nat × List Chk) := [
  ("test_transfer_readable_end", 1, transferReadableEnd),
  ("test_eager_stream_completion", 1, eagerStreamCompletion),
  ("test_async_stream_ops", 1, asyncStreamOps)]

end Silmaril.Wasm.Component.Async.Cabi.Oracle
