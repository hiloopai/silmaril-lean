module

public import Silmaril.Wasm.Component.ABI.Defs

@[expose] public section

/-!
# Component Model async built-ins: streams, futures, waitable sets, tasks

A small-step model of the concurrency built-ins of the Component Model (the 🔀 part of the
Canonical ABI), at the level of one handle table shared by a component and the runtime. It is a
**new** semantic layer next to the component IR (`Silmaril.Wasm.Component`), whose import calls are
synchronous. WASI 0.3 (`Silmaril.Wasi.Versions.P3`) uses it as the runtime part of its hosts.

Numeric codes follow `design/mvp/canonical-abi/definitions.py` at component-model revision
`a25fc0b`, the revision of the copied reference machine (`Silmaril.Wasm.Component.Reference`):
event codes `EventCode` (L713–720), copy results `CopyResult` (L1021–1024) packed as
`result | count << 4` (`stream_event`, L1028–1044), `BLOCKED = 0xffff_ffff` (L2394) and the
subtask state `STARTED = 1`, `RETURNED = 2` (L817–822). The codes are restated here (they are
checked against the reference's `Async.Codes` only by reading; no import of the reference's
`Raw` modules is made).

## The store

* `Obj`: what a handle denotes: the readable or writable end of a stream or a future (by the
  channel id), a subtask, or a waitable set. Handles are `Nat`s from `1`; `0` is never
  allocated (`Table.__init__`).
* `Chan`: the shared state of a stream or future: at most one **pending** copy (`Pend`: a
  reader waiting for up to `n` items, or a writer offering items), drop flags of the two ends,
  `done` (a future's value has been delivered) and the ghost `sent`, the items transferred so
  far.
* `Task`: a callee task: started, or returned with its results (`task.return`).
* `Store`: the handle table, channels, tasks, waitable-set membership (`joined`) and the one
  pending event of each waitable (`ev`).

## The built-ins (`step`)

`step st op` is `none` for a trap, `some (st', r)` otherwise. Copies are **rendezvous**, as in
the Component Model: a `stream.write` meets a pending `stream.read` (or vice versa) and copies
`min n |xs|` items at once; the pending side receives a `stream-read`/`stream-write` event;
otherwise the operation becomes pending and returns `BLOCKED`. A copy towards a dropped peer
returns `DROPPED`. A future is written at most once. `waitable-set.wait` returns the pending
event of a member (the one with the least handle in this deterministic `step`; the relational
`Waits` allows any member) and **suspends** (`Res.blocked`) when there is none;
`waitable-set.poll` returns the event `none` instead. `task.return` resolves a subtask once and
posts its `subtask` event.

## Sync lowering of async imports

`canon lower` *without* `async` of an async callee (`definitions.py`, `canon_lower`, sync
branch): the caller starts the callee task and its thread is suspended until the subtask is
resolved, then reads the results. No subtask handle reaches the caller's table. `SyncPc` and
`syncStep` are that caller; `Silmaril.Wasm.Component.Async.Thms` proves that, interleaved with
arbitrary steps of the other parties, it resumes exactly with the values of the callee's
`task.return`.

## Simplifications (stated, not hidden)

* One handle table: the ends a component passes to the host (e.g. to `write-via-stream`) keep
  their number. The reference machine moves ends between per-instance tables.
* Items are component values `Val`; the guest memory copy is not modelled.
* Zero-length copies are not given their special meaning (a zero-length `stream.write` meeting
  a pending read completes with `0`).
* `stream.cancel-*`, `future.cancel-*`, `subtask.cancel`, `error-context`, backpressure,
  threads and the callback ABI of async exports are not modelled here.
* After a rendezvous the pending side's operation completes (a partial copy completes it with
  the copied count, as `COMPLETED`).

A Silmaril addition; the line-by-line correspondence with the reference machine is open
(`docs/projects/wasm-components.md`).
-/

namespace Silmaril.Wasm.Component.Async

open Silmaril.Wasm.Component (Val)

/-! ## Codes -/

/-- `EventCode` (`definitions.py` L713–720). -/
inductive EventCode where
  | none
  | subtask
  | streamRead
  | streamWrite
  | futureRead
  | futureWrite
  | taskCancelled
  deriving DecidableEq, Repr

/-- The numeric event code. -/
def EventCode.toNat : EventCode → Nat
  | .none => 0
  | .subtask => 1
  | .streamRead => 2
  | .streamWrite => 3
  | .futureRead => 4
  | .futureWrite => 5
  | .taskCancelled => 6

/-- `CopyResult` (L1021–1024). -/
inductive CopyResult where
  | completed
  | dropped
  | cancelled
  deriving DecidableEq, Repr

/-- The numeric copy result. -/
def CopyResult.toNat : CopyResult → Nat
  | .completed => 0
  | .dropped => 1
  | .cancelled => 2

/-- The packed result of a copy: `result | count << 4` (`stream_event`). -/
def packCopy (r : CopyResult) (k : Nat) : Nat := r.toNat + 16 * k

/-- `BLOCKED = 0xffff_ffff` (L2394). -/
def blocked : Nat := 0xffff_ffff

/-- `Subtask.State.STARTED` (L817–822). -/
def subStarted : Nat := 1

/-- `Subtask.State.RETURNED`. -/
def subReturned : Nat := 2

/-! ## The store -/

/-- What a handle denotes. -/
inductive Obj where
  /-- The readable end of the stream `s`. -/
  | streamR (s : Nat)
  /-- The writable end of the stream `s`. -/
  | streamW (s : Nat)
  /-- The readable end of the future `s`. -/
  | futureR (s : Nat)
  /-- The writable end of the future `s`. -/
  | futureW (s : Nat)
  /-- A subtask (its task id). -/
  | subtask (t : Nat)
  /-- A waitable set. -/
  | wset
  deriving DecidableEq, Repr

/-- A handle denotes a waitable (anything but a waitable set). -/
def Obj.isWaitable : Obj → Bool
  | .wset => false
  | _ => true

/-- The pending copy of a channel. -/
inductive Pend where
  /-- No copy is pending. -/
  | idle
  /-- The reader `h` waits for up to `n` items. -/
  | read (h n : Nat)
  /-- The writer `h` offers the items `xs`. -/
  | write (h : Nat) (xs : List Val)

/-- An event delivered to a waitable: code, waitable index, payload, and the items it delivers
(a completed read). -/
structure Event where
  code : EventCode
  index : Nat
  payload : Nat
  items : List Val := []

/-- The state of a stream or future. -/
structure Chan where
  pend : Pend := .idle
  rDropped : Bool := false
  wDropped : Bool := false
  /-- A future's value has been delivered (or its reader dropped). -/
  done : Bool := false
  /-- Ghost: the items transferred so far, in order. -/
  sent : List Val := []

/-- A callee task. -/
structure Task where
  /-- The results of `task.return`, once it has been called. -/
  result : Option (List Val) := none

/-- The store of the async built-ins. -/
structure Store where
  /-- The next fresh handle (handles start at `1`). -/
  next : Nat := 1
  tbl : Nat → Option Obj := fun _ => none
  chans : Nat → Chan := fun _ => {}
  tasks : Nat → Task := fun _ => {}
  /-- The waitable set a waitable has joined. -/
  joined : Nat → Option Nat := fun _ => none
  /-- The pending event of a waitable. -/
  ev : Nat → Option Event := fun _ => none

/-- Point update of a function on handles. -/
def upd {β : Type} (f : Nat → β) (k : Nat) (v : β) : Nat → β := fun j => if j = k then v else f j

/-- The empty store. -/
def Store.empty : Store := {}

namespace Store

/-- Set the channel `s`. -/
def setChan (st : Store) (s : Nat) (c : Chan) : Store := { st with chans := upd st.chans s c }

/-- Post the event `e` on the waitable `h`. -/
def post (st : Store) (h : Nat) (e : Event) : Store := { st with ev := upd st.ev h (some e) }

/-- Remove the handle `h` (and its set membership and event). -/
def remove (st : Store) (h : Nat) : Store :=
  { st with tbl := upd st.tbl h none, joined := upd st.joined h none, ev := upd st.ev h none }

/-- Allocate two fresh handles denoting `a` and `b`. -/
def alloc2 (st : Store) (a b : Nat → Obj) : Store × Nat × Nat :=
  let r := st.next
  ({ st with next := r + 2, tbl := upd (upd st.tbl r (some (a r))) (r + 1) (some (b r)) },
   r, r + 1)

end Store

/-! ## Operations and results -/

/-- The built-ins, and the callee's `task.return`. -/
inductive Op where
  | streamNew
  | streamWrite (w : Nat) (xs : List Val)
  | streamRead (r n : Nat)
  | streamDropR (r : Nat)
  | streamDropW (w : Nat)
  | futureNew
  | futureWrite (w : Nat) (v : Val)
  | futureRead (r : Nat)
  | futureDropR (r : Nat)
  | futureDropW (w : Nat)
  | wsNew
  /-- `waitable.join h s` (`s = 0`: leave any set). -/
  | join (h s : Nat)
  | wait (s : Nat)
  | poll (s : Nat)
  | wsDrop (s : Nat)
  /-- An `async`-lowered import call: a new subtask handle. -/
  | callAsync
  | subtaskDrop (t : Nat)
  /-- The callee of the task `t` calls `task.return` with `vs`. -/
  | taskReturn (t : Nat) (vs : List Val)

/-- The results of the built-ins. -/
inductive Res where
  | unit
  /-- A code, packed result or handle. -/
  | nat (n : Nat)
  /-- The two ends of a new stream or future. -/
  | ends (r w : Nat)
  /-- A read: the packed result and the items delivered. -/
  | read (code : Nat) (xs : List Val)
  /-- An event of `waitable-set.wait`/`poll`. -/
  | event (e : Event)
  /-- The calling thread is suspended (`waitable-set.wait` with no event). -/
  | blocked

/-! ## The step function -/

/-- The first waitable joined to the set `s` with a pending event, among the handles `< n`. -/
def firstReady (st : Store) (s : Nat) : List Nat → Option Nat
  | [] => none
  | h :: hs => if st.joined h = some s ∧ (st.ev h).isSome then some h else firstReady st s hs

/-- Some waitable joined to `s` among `hs` has a pending event. -/
def anyReady (st : Store) (s : Nat) (hs : List Nat) : Bool :=
  hs.any fun h => decide (st.joined h = some s) && (st.ev h).isSome

/-- Take the pending event of `h`. -/
def take (st : Store) (h : Nat) : Option (Store × Event) :=
  (st.ev h).map fun e => ({ st with ev := upd st.ev h none }, e)

/-- `stream.write w xs`. -/
def streamWrite (st : Store) (w : Nat) (xs : List Val) : Option (Store × Res) :=
  match st.tbl w with
  | some (.streamW s) =>
    let c := st.chans s
    match c.pend with
    | .write .. => none
    | .read hr n =>
      let k := min n xs.length
      some ((st.setChan s { c with pend := .idle, sent := c.sent ++ xs.take k }).post hr
          ⟨.streamRead, hr, packCopy .completed k, xs.take k⟩, .nat (packCopy .completed k))
    | .idle =>
      if c.rDropped then some (st, .nat (packCopy .dropped 0))
      else some (st.setChan s { c with pend := .write w xs }, .nat blocked)
  | _ => none

/-- `stream.read r n`. -/
def streamRead (st : Store) (r n : Nat) : Option (Store × Res) :=
  match st.tbl r with
  | some (.streamR s) =>
    let c := st.chans s
    match c.pend with
    | .read .. => none
    | .write hw xs =>
      let k := min n xs.length
      some ((st.setChan s { c with pend := .idle, sent := c.sent ++ xs.take k }).post hw
          ⟨.streamWrite, hw, packCopy .completed k, []⟩, .read (packCopy .completed k) (xs.take k))
    | .idle =>
      if c.wDropped then some (st, .read (packCopy .dropped 0) [])
      else some (st.setChan s { c with pend := .read r n }, .nat blocked)
  | _ => none

/-- `stream.drop-readable r`: a pending write gets `DROPPED`; a pending read of `r` traps. -/
def streamDropR (st : Store) (r : Nat) : Option (Store × Res) :=
  match st.tbl r with
  | some (.streamR s) =>
    let c := st.chans s
    match c.pend with
    | .read .. => none
    | .write hw _ =>
      some (((st.setChan s { c with pend := .idle, rDropped := true }).post hw
          ⟨.streamWrite, hw, packCopy .dropped 0, []⟩).remove r, .unit)
    | .idle => some ((st.setChan s { c with rDropped := true }).remove r, .unit)
  | _ => none

/-- `stream.drop-writable w`: a pending read gets `DROPPED`; a pending write of `w` traps. -/
def streamDropW (st : Store) (w : Nat) : Option (Store × Res) :=
  match st.tbl w with
  | some (.streamW s) =>
    let c := st.chans s
    match c.pend with
    | .write .. => none
    | .read hr _ =>
      some (((st.setChan s { c with pend := .idle, wDropped := true }).post hr
          ⟨.streamRead, hr, packCopy .dropped 0, []⟩).remove w, .unit)
    | .idle => some ((st.setChan s { c with wDropped := true }).remove w, .unit)
  | _ => none

/-- `future.write w v`: once only. -/
def futureWrite (st : Store) (w : Nat) (v : Val) : Option (Store × Res) :=
  match st.tbl w with
  | some (.futureW s) =>
    let c := st.chans s
    if c.done then none else
    match c.pend with
    | .write .. => none
    | .read hr _ =>
      some ((st.setChan s { c with pend := .idle, done := true, sent := [v] }).post hr
          ⟨.futureRead, hr, CopyResult.completed.toNat, [v]⟩, .nat CopyResult.completed.toNat)
    | .idle =>
      if c.rDropped then some (st.setChan s { c with done := true }, .nat CopyResult.dropped.toNat)
      else some (st.setChan s { c with pend := .write w [v] }, .nat blocked)
  | _ => none

/-- `future.read r`. -/
def futureRead (st : Store) (r : Nat) : Option (Store × Res) :=
  match st.tbl r with
  | some (.futureR s) =>
    let c := st.chans s
    if c.done then none else
    match c.pend with
    | .read .. => none
    | .write hw xs =>
      some ((st.setChan s { c with pend := .idle, done := true, sent := xs }).post hw
          ⟨.futureWrite, hw, CopyResult.completed.toNat, []⟩, .read CopyResult.completed.toNat xs)
    | .idle => some (st.setChan s { c with pend := .read r 1 }, .nat blocked)
  | _ => none

/-- `future.drop-readable r`. -/
def futureDropR (st : Store) (r : Nat) : Option (Store × Res) :=
  match st.tbl r with
  | some (.futureR s) =>
    let c := st.chans s
    match c.pend with
    | .read .. => none
    | .write hw _ =>
      some (((st.setChan s { c with pend := .idle, rDropped := true, done := true }).post hw
          ⟨.futureWrite, hw, CopyResult.dropped.toNat, []⟩).remove r, .unit)
    | .idle => some ((st.setChan s { c with rDropped := true }).remove r, .unit)
  | _ => none

/-- `future.drop-writable w`: only after the value has been written. -/
def futureDropW (st : Store) (w : Nat) : Option (Store × Res) :=
  match st.tbl w with
  | some (.futureW s) =>
    let c := st.chans s
    if c.done then some ((st.setChan s { c with wDropped := true }).remove w, .unit) else none
  | _ => none

/-- **The built-ins.** `none` is a trap. -/
def step (st : Store) : Op → Option (Store × Res)
  | .streamNew =>
    let (st', r, w) := st.alloc2 .streamR .streamW
    some (st', .ends r w)
  | .streamWrite w xs => streamWrite st w xs
  | .streamRead r n => streamRead st r n
  | .streamDropR r => streamDropR st r
  | .streamDropW w => streamDropW st w
  | .futureNew =>
    let (st', r, w) := st.alloc2 .futureR .futureW
    some (st', .ends r w)
  | .futureWrite w v => futureWrite st w v
  | .futureRead r => futureRead st r
  | .futureDropR r => futureDropR st r
  | .futureDropW w => futureDropW st w
  | .wsNew =>
    some ({ st with next := st.next + 1, tbl := upd st.tbl st.next (some .wset) }, .nat st.next)
  | .join h s =>
    match st.tbl h with
    | some o =>
      if o.isWaitable then
        if s = 0 then some ({ st with joined := upd st.joined h none }, .unit)
        else if st.tbl s = some .wset then some ({ st with joined := upd st.joined h (some s) }, .unit)
        else none
      else none
    | none => none
  | .wait s =>
    if st.tbl s = some .wset then
      match firstReady st s (List.range st.next) with
      | some h => (take st h).map fun (st', e) => (st', .event e)
      | none => some (st, .blocked)
    else none
  | .poll s =>
    if st.tbl s = some .wset then
      match firstReady st s (List.range st.next) with
      | some h => (take st h).map fun (st', e) => (st', .event e)
      | none => some (st, .event ⟨.none, 0, 0, []⟩)
    else none
  | .wsDrop s =>
    if st.tbl s = some .wset ∧ ¬ (List.range st.next).any (fun h => decide (st.joined h = some s))
    then some ({ st with tbl := upd st.tbl s none }, .unit) else none
  | .callAsync =>
    let t := st.next
    some ({ st with next := t + 1, tbl := upd st.tbl t (some (.subtask t)),
                    tasks := upd st.tasks t {} }, .nat (subStarted + 16 * t))
  | .subtaskDrop t =>
    if st.tbl t = some (.subtask t) ∧ (st.tasks t).result.isSome then some (st.remove t, .unit)
    else none
  | .taskReturn t vs =>
    if (st.tasks t).result.isSome then none else
    let st' := { st with tasks := upd st.tasks t { result := some vs } }
    if st.tbl t = some (.subtask t) then some (st'.post t ⟨.subtask, t, subReturned, []⟩, .unit)
    else some (st', .unit)

/-! ## Waiting, relationally -/

/-- **`waitable-set.wait s`, relationally**: any member `h` of `s` with a pending event `e` may
be chosen (the reference machine's choice is unspecified). -/
def Waits (st : Store) (s h : Nat) (e : Event) (st' : Store) : Prop :=
  st.tbl s = some .wset ∧ st.joined h = some s ∧ st.ev h = some e ∧
    st' = { st with ev := upd st.ev h none }

/-! ## Sync lowering of an async import -/

/-- The caller of a sync-lowered async import. -/
inductive SyncPc where
  /-- Not yet called. -/
  | start
  /-- Suspended until the task `t` returns. -/
  | waiting (t : Nat)
  /-- Resumed with these results. -/
  | done (vs : List Val)

/-- Start a callee task for a sync-lowered call: a fresh task id, not entered in the caller's
handle table. -/
def startSync (st : Store) : Store × Nat :=
  ({ st with next := st.next + 1, tasks := upd st.tasks st.next {} }, st.next)

/-- **One step of the sync-lowered caller**: start the callee, or resume once it has returned
(`none`: still suspended, or already done). -/
def syncStep (st : Store) : SyncPc → Option (Store × SyncPc)
  | .start => let (st', t) := startSync st; some (st', .waiting t)
  | .waiting t => (st.tasks t).result.map fun vs => (st, .done vs)
  | .done _ => none

/-- A run of the sync-lowered caller interleaved with the environment: every step is either a
caller step or a built-in of another party (not touching the caller's suspended state). -/
inductive SyncRun : Store → SyncPc → Store → SyncPc → Prop where
  | refl (st pc) : SyncRun st pc st pc
  | caller {st pc st' pc' st'' pc''} : syncStep st pc = some (st', pc') →
      SyncRun st' pc' st'' pc'' → SyncRun st pc st'' pc''
  | env {st pc st' r st'' pc''} (op : Op) : step st op = some (st', r) →
      SyncRun st' pc st'' pc'' → SyncRun st pc st'' pc''

end Silmaril.Wasm.Component.Async
