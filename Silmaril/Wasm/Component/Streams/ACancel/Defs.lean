module

public import Silmaril.Wasm.Component.Streams.Cancel.Defs

/-!
# Asynchronous cancellation (`BLOCKED`, `CANCELLING_COPY`) and store-level futures

`Silmaril.Wasm.Component.Streams.Cancel` models `stream.cancel-*` between two component-owned ends,
where `End.cancel` always notifies the end at once and the cancel never returns `BLOCKED`. This
module adds the case it leaves out, following `design/mvp/canonical-abi/definitions.py` at
component-model `d095e2f60ddae1f9a1e9b1e2fb547ec1114da677` (`End.cancel`, `StreamEnd.notify`,
`FutureEnd.notify`, `cancel_copy`, `copy`, `drop`):

```
def cancel(self):
  assert(self.state == End.State.COPYING)
  self.state = End.State.CANCELLING_COPY
  if (not self.has_pending_event()
      and (self.other.owner is not None or DETERMINISTIC_PROFILE or random.randint(0,1))):
    self.notify(progress = 0)
```

When the **peer end is owned by the host** (`other.owner is None`) the notification may be left
to the host: `cancel_copy` (with `async`) then returns **`BLOCKED`**, and the end stays in the
state **`CANCELLING_COPY`** until its event is delivered. While it is cancelling:

* `copy` on it traps (`trap_if(end.state != IDLE)`), `drop` traps (`copying_or_cancelling`), and
  a second cancel traps (`trap_if(end.state != COPYING)`);
* the peer may still copy into or out of its buffer (the buffer is released only when the event is
  delivered), and each such copy replaces the pending event with the new progress;
* the event, when delivered (`stream_event`), is **`CANCELLED`** with the progress of the copy
  (and for a read the items copied), or `DROPPED` if the peer has gone; the end is `IDLE` again
  (`DONE` after `DROPPED`).

## The model

A cancelling end is a `Drop` end in the state `copying` with a flag (`Flags.rc`, `Flags.wc`):
`Drop`'s and `Cancel`'s operations already trap on a copying end exactly where `definitions.py`
traps on a cancelling one, and copies from the peer are unaffected. `Flags.hostR`/`hostW` say
which ends the host owns. So `AChan` is a `DChan` with its `Flags`:

* `atakeR`/`atakeW`: event delivery, `CANCELLED` on a cancelling end;
* `acancelR now`/`acancelW now`: `End.cancel` and `cancel_copy`; `now` is the nondeterministic
  choice (`random.randint(0,1)`), only consulted when the peer is host-owned;
* streams' copies are `Cancel`'s `zread`/`zwrite`, drops are `Drop`'s.

Futures (`AFChan`) are a `Cancel.FChan` with `Flags`; `FChan.ftakeR` already reports `CANCELLED` for
a non-`1` progress while the writer is alive, which only a cancel produces.

**The store** `AStore` adds the future channels, the flags and host ownership to `Drop`'s
`DStore` (whose handle table already has `futureR`/`futureW` objects), and `astep` gives the
built-ins `stream.new`, `stream.read`, `stream.write`, `stream.cancel-read`,
`stream.cancel-write`, `stream.drop-*`, **`future.new`, `future.read`, `future.write`,
`future.cancel-read`, `future.cancel-write`, `future.drop-*`**, `waitable-set.new` and
`waitable.join`; `AWait` is `waitable-set.wait` over stream and future ends. `give h` hands the
end `h` to the host (its handle is removed and the end becomes host-owned); the host's own
operations on its ends are `HStep`.

## Simplifications (stated)

Sync copies and cancels (`async_ = false`), `forward`, the same-instance trap of `End.copy`, and
futures of other than one value are not modelled; items are `Val`s; the host's choice in
`End.cancel` is a parameter of the operation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.ACancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Cancel

/-- The cancellation flags and host ownership of a stream or future. -/
structure Flags where
  /-- The readable end is in `CANCELLING_COPY`. -/
  rc : Bool := false
  /-- The writable end is in `CANCELLING_COPY`. -/
  wc : Bool := false
  /-- The host owns the readable end. -/
  hostR : Bool := false
  /-- The host owns the writable end. -/
  hostW : Bool := false
  deriving DecidableEq

/-! ## Streams -/

/-- A stream with its flags. -/
structure AChan where
  c : DChan := {}
  f : Flags := {}

/-- The state of an end in `definitions.py`'s terms. -/
inductive AState where
  | idle
  | copying
  | cancelling
  | done
  deriving DecidableEq, Repr

/-- The state of the readable end. -/
def AChan.rstate (a : AChan) : AState :=
  match a.c.r.st with
  | .idle => .idle
  | .copying => if a.f.rc then .cancelling else .copying
  | .done => .done

/-- The state of the writable end. -/
def AChan.wstate (a : AChan) : AState :=
  match a.c.w.st with
  | .idle => .idle
  | .copying => if a.f.wc then .cancelling else .copying
  | .done => .done

namespace AChan

/-- `stream.read` of up to `n` items: `Cancel.zread` (traps unless the end is `IDLE`). -/
def read (a : AChan) (n : Nat) : Option (AChan × Res) :=
  (a.c.zread n).map fun p => ({ a with c := p.1 }, p.2)

/-- `stream.write` of `xs`: `Cancel.zwrite`. -/
def write (a : AChan) (xs : List Val) : Option (AChan × Res) :=
  (a.c.zwrite xs).map fun p => ({ a with c := p.1 }, p.2)

/-- Deliver the pending event of the readable end (`stream_event`): `DROPPED` if the writer has
gone, `CANCELLED` if the end is cancelling, else `COMPLETED`; with the progress and the items. -/
def takeR (a : AChan) : Option (AChan × Nat × List Val) :=
  match a.c.r.ev with
  | none => none
  | some p =>
    some ({ c := { a.c with r := { a.c.r with st := if a.c.w.gone then .done else .idle, ev := none },
                            rcap := none, rgot := [] },
            f := { a.f with rc := false } },
      (if a.c.w.gone then packCopy .dropped p
        else if a.f.rc then packCopy .cancelled p else packCopy .completed p), a.c.rgot)

/-- Deliver the pending event of the writable end. -/
def takeW (a : AChan) : Option (AChan × Nat) :=
  match a.c.w.ev with
  | none => none
  | some p =>
    some ({ c := { a.c with w := { a.c.w with st := if a.c.r.gone then .done else .idle, ev := none },
                            wbuf := none },
            f := { a.f with wc := false } },
      if a.c.r.gone then packCopy .dropped p
        else if a.f.wc then packCopy .cancelled p else packCopy .completed p)

/-- `End.cancel` on the readable end: `CANCELLING_COPY`, and a notification with progress `0`
unless an event is pending and unless the host owns the writer and chose (`now = false`) to
notify later. -/
def startCancelR (a : AChan) (now : Bool) : AChan :=
  let ev := if a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true) then some 0 else a.c.r.ev
  { c := { a.c with r := { a.c.r with ev := ev } }, f := { a.f with rc := true } }

/-- `End.cancel` on the writable end. -/
def startCancelW (a : AChan) (now : Bool) : AChan :=
  let ev := if a.c.w.ev = none ∧ (a.f.hostR = false ∨ now = true) then some 0 else a.c.w.ev
  { c := { a.c with w := { a.c.w with ev := ev } }, f := { a.f with wc := true } }

/-- **`stream.cancel-read`** (async): trap unless `COPYING`; then `End.cancel`; deliver the pending
event at once, or return `BLOCKED` (the end stays `CANCELLING_COPY`). -/
def cancelR (a : AChan) (now : Bool) : Option (AChan × Res) :=
  if a.c.r.gone ∨ a.c.r.st ≠ .copying ∨ a.f.rc then none
  else
    let b := a.startCancelR now
    match b.takeR with
    | some (b', p, ys) => some (b', .read p ys)
    | none => some (b, .nat blocked)

/-- **`stream.cancel-write`** (async). -/
def cancelW (a : AChan) (now : Bool) : Option (AChan × Res) :=
  if a.c.w.gone ∨ a.c.w.st ≠ .copying ∨ a.f.wc then none
  else
    let b := a.startCancelW now
    match b.takeW with
    | some (b', p) => some (b', .nat p)
    | none => some (b, .nat blocked)

/-- **The host-owned writer finishes a cancelled read** that it had deferred (`BLOCKED`), without
further items: the read's event is posted with the progress so far (delivered as `CANCELLED`).
This is what wasmtime 50's stdin producer does when the guest cancels (`StreamResult::Cancelled`,
`tools/wasm-streams/tests/host-cancel.sh`). Only while the end is cancelling with no event. -/
def ackR (a : AChan) : Option AChan :=
  if a.f.rc = true ∧ a.c.r.ev = none ∧ a.c.r.st = .copying ∧ a.c.r.gone = false then
    some { a with c := { a.c with r := { a.c.r with ev := some a.c.rgot.length } } }
  else none

/-- The host-owned reader finishes a cancelled write it had deferred. -/
def ackW (a : AChan) : Option AChan :=
  if a.f.wc = true ∧ a.c.w.ev = none ∧ a.c.w.st = .copying ∧ a.c.w.gone = false then
    some { a with c := { a.c with w := { a.c.w with ev := some 0 } } }
  else none

/-- `stream.drop-readable`: `Drop.dropR` (traps while copying or cancelling). -/
def dropR (a : AChan) : Option AChan := a.c.dropR.map fun c => { a with c := c }

/-- `stream.drop-writable`. -/
def dropW (a : AChan) : Option AChan := a.c.dropW.map fun c => { a with c := c }

end AChan

/-! ## Futures -/

/-- A future with its flags. -/
structure AFChan where
  c : FChan := {}
  f : Flags := {}

namespace AFChan

/-- `future.read`. -/
def read (a : AFChan) : Option (AFChan × Res) := a.c.fread.map fun p => ({ a with c := p.1 }, p.2)

/-- `future.write` of `v`. -/
def write (a : AFChan) (v : Val) : Option (AFChan × Res) :=
  a.c.fwrite v |>.map fun p => ({ a with c := p.1 }, p.2)

/-- Deliver the pending event of the readable end (`future_event`). -/
def takeR (a : AFChan) : Option (AFChan × Nat × List Val) :=
  a.c.ftakeR.map fun p => ({ c := p.1, f := { a.f with rc := false } }, p.2)

/-- Deliver the pending event of the writable end. -/
def takeW (a : AFChan) : Option (AFChan × Nat) :=
  a.c.ftakeW.map fun p => ({ c := p.1, f := { a.f with wc := false } }, p.2)

/-- `End.cancel` on the readable end of a future. -/
def startCancelR (a : AFChan) (now : Bool) : AFChan :=
  let ev := if a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true) then some 0 else a.c.r.ev
  { c := { a.c with r := { a.c.r with ev := ev } }, f := { a.f with rc := true } }

/-- `End.cancel` on the writable end of a future. -/
def startCancelW (a : AFChan) (now : Bool) : AFChan :=
  let ev := if a.c.w.ev = none ∧ (a.f.hostR = false ∨ now = true) then some 0 else a.c.w.ev
  { c := { a.c with w := { a.c.w with ev := ev } }, f := { a.f with wc := true } }

/-- **`future.cancel-read`** (async): trap unless `COPYING`; `End.cancel`; the event at once or
`BLOCKED`. -/
def cancelR (a : AFChan) (now : Bool) : Option (AFChan × Res) :=
  if a.c.r.gone ∨ a.c.r.st ≠ .copying ∨ a.f.rc then none
  else
    let b := a.startCancelR now
    match b.takeR with
    | some (b', p, ys) => some (b', .read p ys)
    | none => some (b, .nat blocked)

/-- **`future.cancel-write`** (async). -/
def cancelW (a : AFChan) (now : Bool) : Option (AFChan × Res) :=
  if a.c.w.gone ∨ a.c.w.st ≠ .copying ∨ a.f.wc then none
  else
    let b := a.startCancelW now
    match b.takeW with
    | some (b', p) => some (b', .nat p)
    | none => some (b, .nat blocked)

/-- `future.drop-readable`. -/
def dropR (a : AFChan) : Option AFChan := a.c.fdropR.map fun c => { a with c := c }

/-- `future.drop-writable`: traps unless the writable end is `DONE`. -/
def dropW (a : AFChan) : Option AFChan := a.c.fdropW.map fun c => { a with c := c }

end AFChan

/-! ## The store -/

/-- `Drop`'s store (handle table, streams, waitable-set membership) with the stream flags and the
futures. A stream's id is the handle of its readable end, a future's likewise. -/
structure AStore where
  d : DStore := {}
  sf : Nat → Flags := fun _ => {}
  futs : Nat → AFChan := fun _ => {}

namespace AStore

/-- The stream `s` with its flags. -/
def chan (st : AStore) (s : Nat) : AChan := ⟨st.d.chans s, st.sf s⟩

/-- Set the stream `s`. -/
def setChan (st : AStore) (s : Nat) (a : AChan) : AStore :=
  { st with d := st.d.setChan s a.c, sf := upd st.sf s a.f }

/-- Set the future `s`. -/
def setFut (st : AStore) (s : Nat) (a : AFChan) : AStore := { st with futs := upd st.futs s a }

/-- Remove the handle `h`. -/
def remove (st : AStore) (h : Nat) : AStore := { st with d := st.d.remove h }

end AStore

/-- The built-ins of this variant. `now` is the host's choice in `End.cancel`. -/
inductive AOp where
  | streamNew
  | streamRead (r n : Nat)
  | streamWrite (w : Nat) (xs : List Val)
  | cancelRead (r : Nat) (now : Bool)
  | cancelWrite (w : Nat) (now : Bool)
  | streamDropR (r : Nat)
  | streamDropW (w : Nat)
  | futureNew
  | futureRead (r : Nat)
  | futureWrite (w : Nat) (v : Val)
  | futureCancelRead (r : Nat) (now : Bool)
  | futureCancelWrite (w : Nat) (now : Bool)
  | futureDropR (r : Nat)
  | futureDropW (w : Nat)
  | wsNew
  | join (h s : Nat)
  /-- Hand the end `h` to the host. -/
  | give (h : Nat)

/-- A stream operation on the stream behind the readable handle `r`. -/
def onR (st : AStore) (r : Nat) (f : AChan → Option (AChan × Res)) : Option (AStore × Res) :=
  match st.d.tbl r with
  | some (.streamR s) => (f (st.chan s)).map fun p => (st.setChan s p.1, p.2)
  | _ => none

/-- A stream operation on the stream behind the writable handle `w`. -/
def onW (st : AStore) (w : Nat) (f : AChan → Option (AChan × Res)) : Option (AStore × Res) :=
  match st.d.tbl w with
  | some (.streamW s) => (f (st.chan s)).map fun p => (st.setChan s p.1, p.2)
  | _ => none

/-- A future operation on the future behind the readable handle `r`. -/
def onFR (st : AStore) (r : Nat) (f : AFChan → Option (AFChan × Res)) : Option (AStore × Res) :=
  match st.d.tbl r with
  | some (.futureR s) => (f (st.futs s)).map fun p => (st.setFut s p.1, p.2)
  | _ => none

/-- A future operation on the future behind the writable handle `w`. -/
def onFW (st : AStore) (w : Nat) (f : AFChan → Option (AFChan × Res)) : Option (AStore × Res) :=
  match st.d.tbl w with
  | some (.futureW s) => (f (st.futs s)).map fun p => (st.setFut s p.1, p.2)
  | _ => none

/-- **The built-ins** (`none`: a trap). -/
def astep (st : AStore) : AOp → Option (AStore × Res)
  | .streamNew =>
    let r := st.d.next
    let d : DStore := { next := r + 2,
                        tbl := upd (upd st.d.tbl r (some (.streamR r))) (r + 1) (some (.streamW r)),
                        chans := upd st.d.chans r {},
                        joined := st.d.joined }
    some ({ st with d := d, sf := upd st.sf r {} }, .ends r (r + 1))
  | .streamRead r n => onR st r fun a => a.read n
  | .streamWrite w xs => onW st w fun a => a.write xs
  | .cancelRead r now => onR st r fun a => a.cancelR now
  | .cancelWrite w now => onW st w fun a => a.cancelW now
  | .streamDropR r =>
    (onR st r fun a => a.dropR.map fun a' => (a', .unit)).map fun p => (p.1.remove r, p.2)
  | .streamDropW w =>
    (onW st w fun a => a.dropW.map fun a' => (a', .unit)).map fun p => (p.1.remove w, p.2)
  | .futureNew =>
    let r := st.d.next
    let d : DStore := { st.d with next := r + 2,
                                  tbl := upd (upd st.d.tbl r (some (.futureR r))) (r + 1) (some (.futureW r)) }
    some ({ st with d := d, futs := upd st.futs r {} }, .ends r (r + 1))
  | .futureRead r => onFR st r fun a => a.read
  | .futureWrite w v => onFW st w fun a => a.write v
  | .futureCancelRead r now => onFR st r fun a => a.cancelR now
  | .futureCancelWrite w now => onFW st w fun a => a.cancelW now
  | .futureDropR r =>
    (onFR st r fun a => a.dropR.map fun a' => (a', .unit)).map fun p => (p.1.remove r, p.2)
  | .futureDropW w =>
    (onFW st w fun a => a.dropW.map fun a' => (a', .unit)).map fun p => (p.1.remove w, p.2)
  | .wsNew =>
    let d : DStore := { st.d with next := st.d.next + 1, tbl := upd st.d.tbl st.d.next (some .wset) }
    some ({ st with d := d }, .nat st.d.next)
  | .join h s =>
    match st.d.tbl h with
    | some (.streamR _) | some (.streamW _) | some (.futureR _) | some (.futureW _) =>
      if st.d.tbl s = some .wset then some ({ st with d := { st.d with joined := upd st.d.joined h (some s) } }, .unit)
      else none
    | _ => none
  | .give h =>
    match st.d.tbl h with
    | some (.streamR s) =>
      if (st.chan s).rstate = .idle then
        some (st.remove h |>.setChan s { (st.chan s) with f := { (st.sf s) with hostR := true } }, .unit)
      else none
    | some (.streamW s) =>
      if (st.chan s).wstate = .idle then
        some (st.remove h |>.setChan s { (st.chan s) with f := { (st.sf s) with hostW := true } }, .unit)
      else none
    | some (.futureR s) =>
      if (st.futs s).c.r.st = .idle then
        some (st.remove h |>.setFut s { (st.futs s) with f := { (st.futs s).f with hostR := true } }, .unit)
      else none
    | some (.futureW s) =>
      if (st.futs s).c.w.st = .idle then
        some (st.remove h |>.setFut s { (st.futs s) with f := { (st.futs s).f with hostW := true } }, .unit)
      else none
    | _ => none

/-- Deliver the pending event of the handle `h` (a stream or future end). -/
def atakeEv (st : AStore) (h : Nat) : Option (AStore × Event) :=
  match st.d.tbl h with
  | some (.streamR s) => ((st.chan s).takeR).map fun p =>
      (st.setChan s p.1, ⟨.streamRead, h, p.2.1, p.2.2⟩)
  | some (.streamW s) => ((st.chan s).takeW).map fun p =>
      (st.setChan s p.1, ⟨.streamWrite, h, p.2, []⟩)
  | some (.futureR s) => ((st.futs s).takeR).map fun p =>
      (st.setFut s p.1, ⟨.futureRead, h, p.2.1, p.2.2⟩)
  | some (.futureW s) => ((st.futs s).takeW).map fun p =>
      (st.setFut s p.1, ⟨.futureWrite, h, p.2, []⟩)
  | _ => none

/-- **`waitable-set.wait s`**, relationally: any member `h` of `s` with a pending event. -/
def AWait (st : AStore) (s h : Nat) (st' : AStore) (e : Event) : Prop :=
  st.d.tbl s = some .wset ∧ st.d.joined h = some s ∧ atakeEv st h = some (st', e)

/-! ## The host's operations on its ends -/

/-- **One operation of the host** on the stream or future `s` whose end it owns. -/
inductive HStep : AStore → AStore → Prop where
  | read {st s n a r} : (st.sf s).hostR = true → (st.chan s).read n = some (a, r) →
      HStep st (st.setChan s a)
  | write {st s xs a r} : (st.sf s).hostW = true → (st.chan s).write xs = some (a, r) →
      HStep st (st.setChan s a)
  | cancelR {st s now a r} : (st.sf s).hostR = true → (st.chan s).cancelR now = some (a, r) →
      HStep st (st.setChan s a)
  | cancelW {st s now a r} : (st.sf s).hostW = true → (st.chan s).cancelW now = some (a, r) →
      HStep st (st.setChan s a)
  | takeR {st s a p ys} : (st.sf s).hostR = true → (st.chan s).takeR = some (a, p, ys) →
      HStep st (st.setChan s a)
  | takeW {st s a p} : (st.sf s).hostW = true → (st.chan s).takeW = some (a, p) →
      HStep st (st.setChan s a)
  | dropR {st s a} : (st.sf s).hostR = true → (st.chan s).dropR = some a → HStep st (st.setChan s a)
  | dropW {st s a} : (st.sf s).hostW = true → (st.chan s).dropW = some a → HStep st (st.setChan s a)
  | ackR {st s a} : (st.sf s).hostW = true → (st.chan s).ackR = some a → HStep st (st.setChan s a)
  | ackW {st s a} : (st.sf s).hostR = true → (st.chan s).ackW = some a → HStep st (st.setChan s a)
  | fread {st s a r} : (st.futs s).f.hostR = true → (st.futs s).read = some (a, r) →
      HStep st (st.setFut s a)
  | fwrite {st s v a r} : (st.futs s).f.hostW = true → (st.futs s).write v = some (a, r) →
      HStep st (st.setFut s a)
  | fdropR {st s a} : (st.futs s).f.hostR = true → (st.futs s).dropR = some a → HStep st (st.setFut s a)
  | fdropW {st s a} : (st.futs s).f.hostW = true → (st.futs s).dropW = some a → HStep st (st.setFut s a)

/-! ## Item flow -/

/-- One operation on a stream, with the items it hands to the reader. -/
inductive AStep : AChan → AChan → List Val → Prop where
  | read {a a' n r} : a.read n = some (a', r) → AStep a a' (delivered r)
  | write {a a' xs r} : a.write xs = some (a', r) → AStep a a' []
  | cancelR {a a' now r} : a.cancelR now = some (a', r) → AStep a a' (delivered r)
  | cancelW {a a' now r} : a.cancelW now = some (a', r) → AStep a a' []
  | takeR {a a' p ys} : a.takeR = some (a', p, ys) → AStep a a' ys
  | takeW {a a' p} : a.takeW = some (a', p) → AStep a a' []
  | dropR {a a'} : a.dropR = some a' → AStep a a' []
  | dropW {a a'} : a.dropW = some a' → AStep a a' []
  | give {a f} : AStep a { a with f := f } []

/-- Stream operations, iterated. -/
inductive ASteps : AChan → AChan → List Val → Prop where
  | refl (a : AChan) : ASteps a a []
  | tail {a a' a'' ys zs} : ASteps a a' ys → AStep a' a'' zs → ASteps a a'' (ys ++ zs)

/-- One operation on a future, with the values it hands to the reader. -/
inductive AFStep : AFChan → AFChan → List Val → Prop where
  | read {a a' r} : a.read = some (a', r) → AFStep a a' (delivered r)
  | write {a a' v r} : a.write v = some (a', r) → AFStep a a' []
  | takeR {a a' p ys} : a.takeR = some (a', p, ys) → AFStep a a' ys
  | takeW {a a' p} : a.takeW = some (a', p) → AFStep a a' []
  | cancelR {a a' now r} : a.cancelR now = some (a', r) → AFStep a a' (delivered r)
  | cancelW {a a' now r} : a.cancelW now = some (a', r) → AFStep a a' []
  | dropR {a a'} : a.dropR = some a' → AFStep a a' []
  | dropW {a a'} : a.dropW = some a' → AFStep a a' []
  | give {a f} : AFStep a { a with f := f } []

/-- Future operations, iterated. -/
inductive AFSteps : AFChan → AFChan → List Val → Prop where
  | refl (a : AFChan) : AFSteps a a []
  | tail {a a' a'' ys zs} : AFSteps a a' ys → AFStep a' a'' zs → AFSteps a a'' (ys ++ zs)

end Silmaril.Wasm.Component.Streams.ACancel
