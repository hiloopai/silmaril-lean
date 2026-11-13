module

public import Silmaril.Wasm.Component.Async.Defs

/-!
# Streams with the Component Model's drop behaviour

A variant of the stream built-ins of `Silmaril.Wasm.Component.Async` (imported, not modified) that
follows the `End` classes of the Canonical ABI (`design/mvp/canonical-abi/definitions.py`,
component-model `main` as read on 2026-11-09: `End.copy`, `End.drop`, `StreamEnd.notify`, the
module-level `copy` and `drop` helpers, `Waitable`, `WaitableSet`). It has the two behaviours that
`Async` lacks and that the wasmtime tests of `docs/projects/wasm-components.md` exposed:

1. **`DROPPED` with a count.** A copy that has made progress keeps its buffer open; its event is
   computed when it is delivered (`StreamEnd.notify` stores a closure). If the peer drops first,
   the copy ends with `DROPPED` *and* the progress so far (the items copied are delivered).
2. **`DROPPED` on an idle end.** `End.drop` notifies the other end with progress `0` whenever it is
   not `DONE` and has no pending event, so an end with no copy in progress receives a `DROPPED`
   event (by `waitable-set.wait`, or synchronously from its next copy).

## The state of a stream (`DChan`)

* each end (`DEnd`): its copy state `IDLE | COPYING | DONE` (`EState`; cancellation is not
  modelled), its pending event, kept as the progress it reports (the event code and result are
  computed at delivery, as in `stream_event`), and whether its handle has been dropped;
* the pending buffers: the writer's remaining items `wbuf`, or the reader's remaining capacity
  `rcap` and the items already copied into its buffer `rgot`;
* the ghost `sent`: every item transferred so far, in order.

## The built-ins

* `DChan.read n` / `DChan.write xs` (`End.copy` through `copy`): trap unless the end is `IDLE`
  (and not dropped); if the peer has dropped, deliver the pending event at once (`DROPPED` with its
  progress; the end becomes `DONE`); if the peer has no buffer, keep this one (`BLOCKED`);
  otherwise copy `min` of the two remaining sizes, complete this copy at once with its count, and
  notify the peer with its total progress, closing the peer's buffer when it is full.
* `DChan.takeR` / `DChan.takeW` (`stream_event`): deliver the pending event of an end: `DROPPED`
  (and `DONE`) if the peer has gone, `COMPLETED` (and `IDLE`) otherwise, with the progress; the
  buffer is closed.
* `DChan.dropR` / `DChan.dropW` (`End.drop` through `drop`): trap while copying; mark the handle
  dropped (a pending event is discarded) and notify the peer with progress `0` if it is not
  `DONE`, has not gone and has no pending event.

`DStore` is a handle table over these channels and waitable sets, as in `Async` (a channel's id
is the handle of its readable end); `dstep` runs a built-in on handles and `DWait` is
`waitable-set.wait`, relationally: any member with a pending event may be chosen (`WaitableSet.
get_pending_event` shuffles its elements).

## Simplifications (stated)

Zero-length copies trap here (the Canonical ABI gives them a meaning), as do reads of `0` items;
`stream.cancel-*`, futures, subtasks, the same-instance trap of `End.copy`, `forward`, and sync
copies (`opts.async_ = false`) are not modelled. Items are `Val`s (no guest memory).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Drop

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)

/-- `End.State` without `CANCELLING_COPY`. -/
inductive EState where
  | idle
  | copying
  | done
  deriving DecidableEq, Repr

/-- One end of a stream. -/
structure DEnd where
  st : EState := .idle
  /-- The pending event, as the progress it reports (`none`: no pending event). -/
  ev : Option Nat := none
  /-- The handle has been dropped. -/
  gone : Bool := false

/-- The state of a stream. -/
structure DChan where
  r : DEnd := {}
  w : DEnd := {}
  /-- The items the writer's open buffer still offers. -/
  wbuf : Option (List Val) := none
  /-- The reader's open buffer: the capacity left. -/
  rcap : Option Nat := none
  /-- The items copied into the reader's current buffer. -/
  rgot : List Val := []
  /-- Ghost: the items transferred so far. -/
  sent : List Val := []

namespace DChan

/-- `stream.read` of up to `n` items. -/
def read (c : DChan) (n : Nat) : Option (DChan × Res) :=
  if c.r.gone ∨ c.r.st ≠ .idle ∨ n = 0 then none
  else if c.w.gone then
    match c.r.ev with
    | some p =>
      some ({ c with r := { c.r with st := .done, ev := none }, rcap := none, rgot := [] },
        .read (packCopy .dropped p) c.rgot)
    | none => none
  else
    match c.wbuf with
    | none => some ({ c with r := { c.r with st := .copying }, rcap := some n, rgot := [] },
        .nat blocked)
    | some [] => none
    | some xs =>
      let m := min n xs.length
      some ({ c with w := { c.w with ev := some (c.w.ev.getD 0 + m) },
                     wbuf := if xs.drop m = [] then none else some (xs.drop m),
                     sent := c.sent ++ xs.take m },
        .read (packCopy .completed m) (xs.take m))

/-- `stream.write` of the items `xs`. -/
def write (c : DChan) (xs : List Val) : Option (DChan × Res) :=
  if c.w.gone ∨ c.w.st ≠ .idle ∨ xs = [] then none
  else if c.r.gone then
    match c.w.ev with
    | some p =>
      some ({ c with w := { c.w with st := .done, ev := none }, wbuf := none },
        .nat (packCopy .dropped p))
    | none => none
  else
    match c.rcap with
    | none => some ({ c with w := { c.w with st := .copying }, wbuf := some xs }, .nat blocked)
    | some n =>
      let m := min n xs.length
      some ({ c with r := { c.r with ev := some (c.rgot.length + m) },
                     rgot := c.rgot ++ xs.take m,
                     rcap := if n - m = 0 then none else some (n - m),
                     sent := c.sent ++ xs.take m },
        .nat (packCopy .completed m))

/-- Deliver the pending event of the readable end: the packed result and the items. -/
def takeR (c : DChan) : Option (DChan × Nat × List Val) :=
  match c.r.ev with
  | none => none
  | some p =>
    some ({ c with r := { c.r with st := if c.w.gone then .done else .idle, ev := none },
                   rcap := none, rgot := [] },
      (if c.w.gone then packCopy .dropped p else packCopy .completed p), c.rgot)

/-- Deliver the pending event of the writable end: the packed result. -/
def takeW (c : DChan) : Option (DChan × Nat) :=
  match c.w.ev with
  | none => none
  | some p =>
    some ({ c with w := { c.w with st := if c.r.gone then .done else .idle, ev := none },
                   wbuf := none },
      if c.r.gone then packCopy .dropped p else packCopy .completed p)

/-- `stream.drop-readable`. -/
def dropR (c : DChan) : Option DChan :=
  if c.r.gone ∨ c.r.st = .copying then none
  else
    some { c with r := { c.r with gone := true, ev := none },
                  w := if c.w.gone = false ∧ c.w.st ≠ .done ∧ c.w.ev = none
                    then { c.w with ev := some 0 } else c.w }

/-- `stream.drop-writable`. -/
def dropW (c : DChan) : Option DChan :=
  if c.w.gone ∨ c.w.st = .copying then none
  else
    some { c with w := { c.w with gone := true, ev := none },
                  r := if c.r.gone = false ∧ c.r.st ≠ .done ∧ c.r.ev = none
                    then { c.r with ev := some 0 } else c.r }

end DChan

/-! ## The store -/

/-- Handle table, streams and waitable-set membership. -/
structure DStore where
  next : Nat := 1
  tbl : Nat → Option Obj := fun _ => none
  chans : Nat → DChan := fun _ => {}
  joined : Nat → Option Nat := fun _ => none

namespace DStore

/-- Set the stream `s`. -/
def setChan (st : DStore) (s : Nat) (c : DChan) : DStore := { st with chans := upd st.chans s c }

/-- Remove the handle `h` (and its set membership). -/
def remove (st : DStore) (h : Nat) : DStore :=
  { st with tbl := upd st.tbl h none, joined := upd st.joined h none }

/-- The pending event of the handle `h`, if it denotes a stream end. -/
def evOf (st : DStore) (h : Nat) : Option Nat :=
  match st.tbl h with
  | some (.streamR s) => (st.chans s).r.ev
  | some (.streamW s) => (st.chans s).w.ev
  | _ => none

end DStore

/-- The stream built-ins and waitable-set built-ins of this variant. -/
inductive DOp where
  | streamNew
  | streamWrite (w : Nat) (xs : List Val)
  | streamRead (r n : Nat)
  | streamDropR (r : Nat)
  | streamDropW (w : Nat)
  | wsNew
  | join (h s : Nat)

/-- **The built-ins** (`none`: a trap). -/
def dstep (st : DStore) : DOp → Option (DStore × Res)
  | .streamNew =>
    let r := st.next
    some ({ st with next := r + 2,
                    tbl := upd (upd st.tbl r (some (.streamR r))) (r + 1) (some (.streamW r)),
                    chans := upd st.chans r {} }, .ends r (r + 1))
  | .streamWrite w xs =>
    match st.tbl w with
    | some (.streamW s) => ((st.chans s).write xs).map fun p => (st.setChan s p.1, p.2)
    | _ => none
  | .streamRead r n =>
    match st.tbl r with
    | some (.streamR s) => ((st.chans s).read n).map fun p => (st.setChan s p.1, p.2)
    | _ => none
  | .streamDropR r =>
    match st.tbl r with
    | some (.streamR s) => ((st.chans s).dropR).map fun c => ((st.setChan s c).remove r, .unit)
    | _ => none
  | .streamDropW w =>
    match st.tbl w with
    | some (.streamW s) => ((st.chans s).dropW).map fun c => ((st.setChan s c).remove w, .unit)
    | _ => none
  | .wsNew => some ({ st with next := st.next + 1, tbl := upd st.tbl st.next (some .wset) },
      .nat st.next)
  | .join h s =>
    match st.tbl h with
    | some (.streamR _) | some (.streamW _) =>
      if st.tbl s = some .wset then some ({ st with joined := upd st.joined h (some s) }, .unit)
      else none
    | _ => none

/-- Deliver the pending event of the handle `h`. -/
def takeEv (st : DStore) (h : Nat) : Option (DStore × Event) :=
  match st.tbl h with
  | some (.streamR s) => ((st.chans s).takeR).map fun p =>
      (st.setChan s p.1, ⟨.streamRead, h, p.2.1, p.2.2⟩)
  | some (.streamW s) => ((st.chans s).takeW).map fun p =>
      (st.setChan s p.1, ⟨.streamWrite, h, p.2, []⟩)
  | _ => none

/-- **`waitable-set.wait s`**, relationally: any member `h` of `s` with a pending event. -/
def DWait (st : DStore) (s h : Nat) (st' : DStore) (e : Event) : Prop :=
  st.tbl s = some .wset ∧ st.joined h = some s ∧ takeEv st h = some (st', e)

end Silmaril.Wasm.Component.Streams.Drop
