module

public import Silmaril.Wasm.Component.Reference.Async.Codes.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Calling

/-!
# Canonical ABI async codes and bit packings

This module transcribes every numeric code, sentinel and bit packing of the
Component Model concurrency ABI (the 🔀/🧵 parts of the Canonical ABI). It does
not depend on any runtime or scheduler design: everything here is a plain
enumeration, a constant, or a total function on `Nat`.

Source: `design/mvp/canonical-abi/definitions.py` at component-model revision
`a25fc0b` (line numbers below refer to that file), with prose in
`design/mvp/CanonicalABI.md` and `design/mvp/Explainer.md` at the same revision.

| Lean | `definitions.py` |
| --- | --- |
| `tableMaxLength` | `Table.MAX_LENGTH` (L654), index 0 reserved (`Table.__init__`, L656–658) |
| `bufferMaxLength` | `Buffer.MAX_LENGTH` (L877), trap in `GuestBuffer.__init__` (L895) |
| `EventCode`, `EventTuple` | `EventCode`, `EventTuple` (L713–722) |
| `SubtaskState` | `Subtask.State` (L817–822), `Subtask.resolved` (L838) |
| `TaskState` | `Task.State` (L393–398) |
| `EndState` | `End.State` (L932–936), `End.copying_or_cancelling` (L1018) |
| `CopyResult` | `CopyResult` (L1021–1024) |
| `packStreamCopyResult` | `StreamEnd.notify.stream_event` (L1028–1044) |
| `futureCopyPayload` | `FutureEnd.notify.future_event` (L1050–1066) |
| `EndKind.eventCode` | `new_stream`, `new_future` (L1085–1097) |
| `CallbackCode`, `unpackCallbackResult` | `CallbackCode`, `unpack_callback_result` (L2147–2159) |
| `AsyncLowerResult` | `canon_lower`, async branch (L2217–2233) |
| `contextSlotCount`, `contextValueBound` | `Thread.storage` (L292), `canon_context_*` (L2275–2291) |
| `backpressureInc?`, `backpressureDec?` | `canon_backpressure_{inc,dec}` (L2295–2307) |
| `EventTuple.callbackArgs` | callback call in `canon_lift` (L2131–2132) |
| `EventTuple.Storable` | `unpack_event` (L2349–2354) |
| `noWaitableSet` | `canon_waitable_join` (L2384) |
| `blocked` | `BLOCKED` (L2394) |
| `subtaskCancelResult`, `SubtaskCancelResultWF`, `subtaskCancelResult?` | `canon_subtask_cancel` (L2396–2416) |
| `packEnds`, `unpackEnds` | `canon_{stream,future}_new` (L2430–2444); test helper `unpack_new_ends` |
| `threadSwitchResult` | `canon_thread_{suspend,yield,…}` return `[0]` (L2605–2659) |
| `ABI.maxFlat*` (from `ABI.Calling`) | `MAX_FLAT_{PARAMS,ASYNC_PARAMS,RESULTS}` (L1765–1767) |

`CallbackCode` at `a25fc0b` has exactly `EXIT`, `YIELD` and `WAIT` (with
`MAX = 2`); there is no `POLL` code, and codes `3..15` trap in
`unpack_callback_result`. There is no function named `pack_copy_result` at this
revision; the packing is inlined in `stream_event` (wasmtime's
`ReturnCode::encode` comment still uses that older name).

Python models core values as unbounded integers and relies on assertions for
their ranges. Here packings are total functions on `Nat`; the range facts that
Python asserts are theorems in `Async/Codes/Properties.lean`. `TaskState` and
`EndState` are Python `Enum`s (not `IntEnum`s), so their numeric values are
never observable through the ABI; they are recorded only for transcription
fidelity.

Cross-check with wasmtime (`a7b4f29`,
`crates/wasmtime/src/runtime/component/concurrent.rs`,
`concurrent/futures_and_streams.rs`, `crates/environ/src/component.rs`,
`crates/environ/src/vmoffsets.rs`): event codes (`Event::parts`), callback codes
(`callback_code`, `unpack_callback_code`), subtask states (`Status`, whose
cancelled cases are named `StartCancelled`/`ReturnCancelled`), copy results and
`BLOCKED` (`ReturnCode::encode`), `ItemCount::MAX = 1 << 28` (strict bound,
agreeing with `Buffer.MAX_LENGTH = 2^28 - 1`), `MAX_FLAT_*`,
`NUM_COMPONENT_CONTEXT_SLOTS = 2` and the `u16` backpressure counter all agree.
Differences: wasmtime keeps context slots as `u32` only (Python also allows the
🐘 `i64` form); wasmtime's `PREPARE_ASYNC_*` and `START_FLAG_ASYNC_CALLEE` are
implementation-internal adapter constants with no spec counterpart. A spec-level
inconsistency: `Explainer.md` says the `stream.{read,write}` result is a
`memory.addrtype` whose all-ones value means blocked, but `definitions.py`
returns `BLOCKED = 0xffff_ffff` for both address types; `blocked` follows
`definitions.py`.

Nothing here models tasks, threads, waitables, scheduling or memory; this is
not a conformance claim for any runtime behaviour.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Async

/-! ## Shared bounds and sentinels -/

/-! ## Low-nibble packing

`lo | (hi << 4)` is shared by callback results (`unpack_callback_result`),
async-lower results (`canon_lower`) and stream copy results (`stream_event`). -/

/-! ## Event codes -/

/-! ## Callback codes -/

/-! ## Subtask and task states -/

/-! ## Stream and future ends -/

/-! ## Thread-local context and backpressure -/

end Silmaril.Wasm.Component.Async
