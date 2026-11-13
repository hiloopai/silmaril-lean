module

public import Silmaril.Wasm.Component.Streams.AStore.Defs
public import Silmaril.Proofs.Wasm.Component.Streams.AStore

/-!
# The store with asynchronous cancellation and futures: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.AStore`.

* **Conservativity** (`astep_ofD`, `astep_ofD_cancelRead`, `astep_ofD_cancelWrite`,
  `atakeEv_ofD`, `await_ofD`): on a `Drop` store with no flags and no futures, every stream
  built-in, cancel and wait of `ACancel` is `Cancel.cstep`'s and `Drop`'s. With
  `Cancel.cstep_eq` and `Cancel.reach_good`, the theorems about networks (`Net`, `Pipes`,
  `Live`) and generated modules (`KDrop`, `KNet`, `KGame`) are theorems about runs in this model
  too: their stores never have a cancelling end, a host-owned end or a future.
* **`BLOCKED` at the store** (`astep_cancelRead_blocked`): only from a host-owned writer, by the
  host's choice; the end is then `CANCELLING_COPY`.
* **Store-level futures** (`fut_*`, checked by `rfl`): `future.new`, `future.write` before the
  read (`BLOCKED`), `future.read` (`COMPLETED` with the value), the writer's event,
  `future.drop-*`; dropping the writable end before the value is written traps
  (`futures-must-write`); a `future.cancel-read` with a component-owned writer is `CANCELLED` at
  once; with a host-owned writer it may be `BLOCKED`, and the host's later write then completes
  the read (`COMPLETED`, the value delivered by `waitable-set.wait`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.ACancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Cancel

/-- **The stream built-ins of `Drop` are answered as `Cancel` answers them.** -/
theorem astep_ofD {st : DStore} (hNF : NoFut st) (o : DOp) :
    astep (ofD st) (liftD o) = (cstep st (.op o)).map fun p => (ofD p.1, p.2) :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.astep_ofD hNF o

/-- With no host-owned end, `stream.cancel-read` is `Cancel`'s (never `BLOCKED`). -/
theorem astep_ofD_cancelRead (st : DStore) (r : Nat) (now : Bool) :
    astep (ofD st) (.cancelRead r now) = (cstep st (.cancelRead r)).map fun p => (ofD p.1, p.2) :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.astep_ofD_cancelRead st r now

theorem astep_ofD_cancelWrite (st : DStore) (w : Nat) (now : Bool) :
    astep (ofD st) (.cancelWrite w now) = (cstep st (.cancelWrite w)).map fun p => (ofD p.1, p.2) :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.astep_ofD_cancelWrite st w now

/-- Event delivery is `Drop`'s. -/
theorem atakeEv_ofD (st : DStore) (h : Nat) :
    atakeEv (ofD st) h = (takeEv st h).map fun p => (ofD p.1, p.2) :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.atakeEv_ofD st h

/-- **`waitable-set.wait` is `Drop`'s.** -/
theorem await_ofD {st : DStore} {s h : Nat} {st' : AStore} {e : Event} :
    AWait (ofD st) s h st' e ↔ ∃ st'', DWait st s h st'' e ∧ st' = ofD st'' :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.await_ofD

/-- **A `BLOCKED` cancel comes from a host-owned writer** and leaves the end cancelling. -/
theorem astep_cancelRead_blocked {st st' : AStore} {r : Nat} {now : Bool}
    (h : astep st (.cancelRead r now) = some (st', .nat blocked)) :
    ∃ s, st.d.tbl r = some (.streamR s) ∧ (st.sf s).hostW = true ∧ now = false ∧
      (st'.chan s).rstate = .cancelling :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.astep_cancelRead_blocked h

/-! ## Store-level futures -/

/-- Run built-ins in order, collecting their results (`none`: a trap). -/
def runOps : AStore → List AOp → Option (AStore × List Res)
  | st, [] => some (st, [])
  | st, o :: os => do
    let (st₁, r) ← astep st o
    let (st₂, rs) ← runOps st₁ os
    pure (st₂, r :: rs)

/-- The results only. -/
def results (st : AStore) (os : List AOp) : Option (List Res) := (runOps st os).map (·.2)

/-- `future.new` (handles 1, 2), a write before the read (`BLOCKED`), the read (`COMPLETED` with
the value), `future.drop-readable`; the writer's event is `COMPLETED`, then
`future.drop-writable`. -/
theorem fut_write_read :
    (do let (st, rs) ← runOps {} [.futureNew, .futureWrite 2 (b8 7), .futureRead 1, .futureDropR 1]
        let (st, e) ← atakeEv st 2
        let (_, r) ← astep st (.futureDropW 2)
        pure (rs, e.code, e.payload, r)) =
      some ([.ends 1 2, .nat blocked, .read 0 [b8 7], .unit], .futureWrite, 0, .unit) := rfl

/-- A read before the write (`BLOCKED`); the write completes it at once; the reader's event
delivers the value. -/
theorem fut_read_write :
    (do let (st, rs) ← runOps {} [.futureNew, .futureRead 1, .futureWrite 2 (b8 9)]
        let (_, e) ← atakeEv st 1
        pure (rs, e.code, e.payload, e.items)) =
      some ([.ends 1 2, .nat blocked, .nat 0], .futureRead, 0, [b8 9]) := rfl

/-- **`futures-must-write`**: dropping the writable end before the value is written traps. -/
theorem fut_drop_unwritten : results {} [.futureNew, .futureDropW 2] = none := rfl

/-- After the reader has gone, a write reports `DROPPED`, and the writable end may be dropped. -/
theorem fut_write_dropped :
    results {} [.futureNew, .futureDropR 1, .futureWrite 2 (b8 1), .futureDropW 2] =
      some [.ends 1 2, .unit, .nat 1, .unit] := rfl

/-- A cancelled read with a component-owned writer: `CANCELLED` at once. -/
theorem fut_cancel_now :
    results {} [.futureNew, .futureRead 1, .futureCancelRead 1 false] =
      some [.ends 1 2, .nat blocked, .read 2 []] := rfl

/-- **Asynchronous cancellation**: the host owns the writer (`give 2`), the read is cancelled
and the host chooses to notify later: `BLOCKED`, the end is cancelling, a second cancel and a drop
trap; the host's write then completes the read, whose event is `COMPLETED` with the value. -/
theorem fut_host_cancel_blocked :
    (do let (st, rs) ← runOps {} [.futureNew, .futureRead 1, .give 2, .futureCancelRead 1 false]
        let (a, _) ← (st.futs 1).write (b8 5)
        let st := st.setFut 1 a
        let (_, e) ← atakeEv st 1
        pure (rs, e.code, e.payload, e.items)) =
      some ([.ends 1 2, .nat blocked, .unit, .nat blocked], .futureRead, 0, [b8 5]) := rfl

theorem fut_cancelling_traps :
    results {} [.futureNew, .futureRead 1, .give 2, .futureCancelRead 1 false,
      .futureCancelRead 1 true] = none ∧
    results {} [.futureNew, .futureRead 1, .give 2, .futureCancelRead 1 false, .futureDropR 1] = none :=
  ⟨rfl, rfl⟩

/-- The host may also notify at once (`now = true`): then the cancel is `CANCELLED`. -/
theorem fut_host_cancel_now :
    results {} [.futureNew, .futureRead 1, .give 2, .futureCancelRead 1 true] =
      some [.ends 1 2, .nat blocked, .unit, .read 2 []] := rfl

/-- **Streams, asynchronously**: a read of 4 with the writer given to the host, cancelled
(`BLOCKED`); the host writes 2 items into the still-open buffer; the event is `CANCELLED` with
progress 2 and those items (`0x22`). -/
theorem stream_host_cancel_blocked :
    (do let (st, rs) ← runOps {} [.streamNew, .streamRead 1 4, .give 2, .cancelRead 1 false]
        let (a, _) ← (st.chan 1).write [b8 1, b8 2]
        let st := st.setChan 1 a
        let (_, e) ← atakeEv st 1
        pure (rs, e.code, e.payload, e.items)) =
      some ([.ends 1 2, .nat blocked, .unit, .nat blocked], .streamRead, 0x22, [b8 1, b8 2]) := rfl

/-- **What wasmtime 50 does with a host-owned stdin** (`tools/wasm-streams/tests/host-cancel.sh`):
a read of 16 with the writer owned by the host, cancelled (`BLOCKED`); the host gives up the copy
without items (`AChan.ackR`, a host step: wasmtime's producer returns `Cancelled`); the event is
`CANCELLED` with progress 0 (`0x02`). -/
theorem stream_host_cancel_zero :
    (do let (st, rs) ← runOps {} [.streamNew, .streamRead 1 16, .give 2, .cancelRead 1 false]
        let a ← (st.chan 1).ackR
        let st := st.setChan 1 a
        let (_, e) ← atakeEv st 1
        pure (rs, e.code, e.payload, e.items)) =
      some ([.ends 1 2, .nat blocked, .unit, .nat blocked], .streamRead, 0x02, []) := rfl

/-- After a `BLOCKED` cancel the end is cancelling: a second read on it traps (wasmtime 50: "cannot
have concurrent operations active on a future/stream"). -/
theorem stream_cancelling_read_traps :
    results {} [.streamNew, .streamRead 1 16, .give 2, .cancelRead 1 false, .streamRead 1 16] =
      none := rfl

end Silmaril.Wasm.Component.Streams.ACancel
