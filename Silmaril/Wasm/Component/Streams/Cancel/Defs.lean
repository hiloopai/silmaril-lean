module

public import Silmaril.Wasm.Component.Streams.Drop.Defs

/-!
# Streams with cancellation and zero-length copies, and futures

`Silmaril.Wasm.Component.Streams.Drop` follows the `End` classes of the Canonical ABI for reads,
writes, drops and events, and leaves out `stream.cancel-read`/`cancel-write`, zero-length copies
and futures. This module adds them, over the same channel state `DChan` (imported, not
modified), following `design/mvp/canonical-abi/definitions.py` at component-model revision
`d095e2f60ddae1f9a1e9b1e2fb547ec1114da677` (the revision pinned by the wasip3-rust work;
`End.copy`, `End.cancel`, `End.drop`, `StreamEnd.notify`, `FutureEnd.notify`, `copy`,
`cancel_copy`, `drop`):

* **Zero-length copies** (`zread`, `zwrite`, the five cases of `End.copy`). A copy is kept
  (`BLOCKED`) when the peer has no buffer, whatever its length; when both buffers have room, `min`
  of the two is copied (as in `Drop`); a nonzero copy meeting a zero-length peer buffer completes
  the peer with `COMPLETED` and progress `0` and keeps its own buffer (`BLOCKED`); a zero-length
  read meeting a zero-length write does the same; otherwise (a zero-length copy meeting a nonzero
  peer buffer, or a zero-length write meeting a zero-length read) the copy completes at once with
  `COMPLETED` and `0`, and the peer keeps its buffer. A zero-length buffer is `wbuf = some []` or
  `rcap = some 0`, which `Drop` never creates (`Good`).
* **Cancellation** (`cancelR`, `cancelW`; `End.cancel` then `cancel_copy`). Trap unless a copy is
  in progress. When the peer is a component instance (`other.owner is not None`, the case of
  every stream between components here) `End.cancel` notifies the end with progress `0` unless it
  already has a pending event, and `cancel_copy` delivers that event at once, so cancelling never
  returns `BLOCKED` here: the result is `CANCELLED` (or `DROPPED` if the peer has gone) with the
  progress of the copy, and for a read the items already copied into the buffer. The end is
  `IDLE` again (`DONE` after `DROPPED`), its buffer released. A copy that has completed but whose
  event is not yet delivered also reports `CANCELLED` with its full progress (the result is
  computed at delivery).
* **Futures** (`FChan`, `fread`, `fwrite`, `ftakeR`, `ftakeW`, `fcancelR`, `fcancelW`, `fdropR`,
  `fdropW`): one value; the payload of an event is the bare `CopyResult` (no count); a copy that
  has transferred the value is `COMPLETED` and the end `DONE`, also when cancelled after the
  fact; **dropping the writable end traps unless it is `DONE`** (the value was written, or the
  reader had gone).

The store (`cstep`, over `DStore` with the extra operations `COp`) answers the operations of
`Drop` by `dstep`, except reads and writes, which go through `zread`/`zwrite`.

## Observed in wasmtime 50.0.0

`tools/wasm-streams/tests/cancel.sh` runs the component-model reference tests of `test/async`
at `d095e2f` (among them `cancel-stream`, `zero-length`, `futures-must-write`,
`partial-stream-copies`, `idle-drop`, `trap-if-done`, `same-component-stream-future`) and this
module's own `cancel-model.wast` under wasmtime 50.0.0; the behaviour above is what they observe
(see `docs/projects/wasm-components.md`, *asyncmodel, an earlier step*).

## Simplifications (stated)

Asynchronous cancellation (`BLOCKED` from `cancel-*`, possible when the peer end is owned by the
host) and the state `CANCELLING_COPY` it leaves behind are not modelled; nor are sync copies and
cancels (`async_ = false`), `forward`, futures of other than one value, or the same-instance trap
of `End.copy` (streams of `u8` are exempt from it). Items are `Val`s.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Cancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)
open Silmaril.Wasm.Component.Streams.Drop

/-! ## Streams -/

end Silmaril.Wasm.Component.Streams.Cancel

namespace Silmaril.Wasm.Component.Streams.Drop.DChan

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res CopyResult packCopy blocked)

/-- `stream.read` of up to `n ≥ 0` items (`End.copy` with `is_read`). -/
def zread (c : DChan) (n : Nat) : Option (DChan × Res) :=
  if c.r.gone ∨ c.r.st ≠ .idle then none
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
    | some [] =>
      -- the writer's zero-length buffer completes with `0`; this read is kept
      some ({ c with w := { c.w with ev := some 0 }, wbuf := none,
                     r := { c.r with st := .copying }, rcap := some n, rgot := [] }, .nat blocked)
    | some xs =>
      if n = 0 then some (c, .read (packCopy .completed 0) [])
      else
        let m := min n xs.length
        some ({ c with w := { c.w with ev := some (c.w.ev.getD 0 + m) },
                       wbuf := if xs.drop m = [] then none else some (xs.drop m),
                       sent := c.sent ++ xs.take m },
          .read (packCopy .completed m) (xs.take m))

/-- `stream.write` of the items `xs`, possibly none (`End.copy` without `is_read`). -/
def zwrite (c : DChan) (xs : List Val) : Option (DChan × Res) :=
  if c.w.gone ∨ c.w.st ≠ .idle then none
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
      if xs = [] then some (c, .nat (packCopy .completed 0))
      else if n = 0 then
        -- the reader's zero-length buffer completes with `0`; this write is kept
        some ({ c with r := { c.r with ev := some 0 }, rcap := none,
                       w := { c.w with st := .copying }, wbuf := some xs }, .nat blocked)
      else
        let m := min n xs.length
        some ({ c with r := { c.r with ev := some (c.rgot.length + m) },
                       rgot := c.rgot ++ xs.take m,
                       rcap := if n - m = 0 then none else some (n - m),
                       sent := c.sent ++ xs.take m },
          .nat (packCopy .completed m))

/-- `stream.cancel-read`: the pending (or new, progress `0`) event of the read, delivered at once
as `CANCELLED` (`DROPPED` if the writer has gone), with the items copied so far. -/
def cancelR (c : DChan) : Option (DChan × Res) :=
  if c.r.gone ∨ c.r.st ≠ .copying then none
  else
    let p := c.r.ev.getD 0
    some ({ c with r := { c.r with st := if c.w.gone then .done else .idle, ev := none },
                   rcap := none, rgot := [] },
      .read (if c.w.gone then packCopy .dropped p else packCopy .cancelled p) c.rgot)

/-- `stream.cancel-write`: the pending (or new) event of the write, delivered at once as
`CANCELLED` (`DROPPED` if the reader has gone), with its progress; the items not copied are not
sent. -/
def cancelW (c : DChan) : Option (DChan × Res) :=
  if c.w.gone ∨ c.w.st ≠ .copying then none
  else
    let p := c.w.ev.getD 0
    some ({ c with w := { c.w with st := if c.r.gone then .done else .idle, ev := none },
                   wbuf := none },
      .nat (if c.r.gone then packCopy .dropped p else packCopy .cancelled p))

/-- The channels `Drop` creates: no zero-length buffer. -/
def Good (c : DChan) : Prop := c.wbuf ≠ some [] ∧ c.rcap ≠ some 0

end Silmaril.Wasm.Component.Streams.Drop.DChan

namespace Silmaril.Wasm.Component.Streams.Cancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)
open Silmaril.Wasm.Component.Streams.Drop

/-- The operations of this variant: those of `Drop`, and the cancellations. -/
inductive COp where
  | op (o : DOp)
  | cancelRead (r : Nat)
  | cancelWrite (w : Nat)

/-- **The built-ins** (`none`: a trap): `Drop`'s, with zero-length copies and cancellation. -/
def cstep (st : DStore) : COp → Option (DStore × Res)
  | .op (.streamWrite w xs) =>
    match st.tbl w with
    | some (.streamW s) => ((st.chans s).zwrite xs).map fun p => (st.setChan s p.1, p.2)
    | _ => none
  | .op (.streamRead r n) =>
    match st.tbl r with
    | some (.streamR s) => ((st.chans s).zread n).map fun p => (st.setChan s p.1, p.2)
    | _ => none
  | .op o => dstep st o
  | .cancelRead r =>
    match st.tbl r with
    | some (.streamR s) => ((st.chans s).cancelR).map fun p => (st.setChan s p.1, p.2)
    | _ => none
  | .cancelWrite w =>
    match st.tbl w with
    | some (.streamW s) => ((st.chans s).cancelW).map fun p => (st.setChan s p.1, p.2)
    | _ => none

/-- Every stream of the store is `Good`. -/
def GoodS (st : DStore) : Prop := ∀ s, (st.chans s).Good

/-! ## Item flow -/

/-- The items an operation hands to the reader. -/
def delivered : Res → List Val
  | .read _ ys => ys
  | _ => []

/-- One operation on a channel, with the items it hands to the reader. -/
inductive CStep : DChan → DChan → List Val → Prop where
  | read {c c' n r} : c.zread n = some (c', r) → CStep c c' (delivered r)
  | write {c c' xs r} : c.zwrite xs = some (c', r) → CStep c c' []
  | cancelR {c c' r} : c.cancelR = some (c', r) → CStep c c' (delivered r)
  | cancelW {c c' r} : c.cancelW = some (c', r) → CStep c c' []
  | takeR {c c' p ys} : c.takeR = some (c', p, ys) → CStep c c' ys
  | takeW {c c' p} : c.takeW = some (c', p) → CStep c c' []
  | dropR {c c'} : c.dropR = some c' → CStep c c' []
  | dropW {c c'} : c.dropW = some c' → CStep c c' []

/-- Operations, iterated, with the items handed to the reader, in order. -/
inductive CSteps : DChan → DChan → List Val → Prop where
  | refl (c : DChan) : CSteps c c []
  | tail {c c' c'' ys zs} : CSteps c c' ys → CStep c' c'' zs → CSteps c c'' (ys ++ zs)

/-! ## Futures -/

/-- A future: two ends, the writer's offered value, whether the reader has a buffer, the value
copied into the reader's buffer and not yet delivered, and the ghost value transferred. -/
structure FChan where
  r : DEnd := {}
  w : DEnd := {}
  wval : Option Val := none
  rbuf : Bool := false
  rgot : Option Val := none
  sent : Option Val := none

/-- The payload of a future event: the bare `CopyResult`. -/
def fcode (r : CopyResult) : Nat := r.toNat

namespace FChan

/-- `future.read`. -/
def fread (c : FChan) : Option (FChan × Res) :=
  if c.r.gone ∨ c.r.st ≠ .idle then none
  else if c.w.gone then
    match c.r.ev with
    | some _ => some ({ c with r := { c.r with st := .done, ev := none }, rbuf := false },
        .read (fcode .dropped) [])
    | none => none
  else
    match c.wval with
    | none => some ({ c with r := { c.r with st := .copying }, rbuf := true }, .nat blocked)
    | some v =>
      let c' := { c with r := { c.r with st := .done }, w := { c.w with ev := some 1 } }
      some ({ c' with wval := none, sent := some v }, .read (fcode .completed) [v])

/-- `future.write` of `v`. -/
def fwrite (c : FChan) (v : Val) : Option (FChan × Res) :=
  if c.w.gone ∨ c.w.st ≠ .idle then none
  else if c.r.gone then
    match c.w.ev with
    | some _ => some ({ c with w := { c.w with st := .done, ev := none }, wval := none },
        .nat (fcode .dropped))
    | none => none
  else if c.rbuf then
    let c' := { c with w := { c.w with st := .done }, r := { c.r with ev := some 1 } }
    some ({ c' with rbuf := false, rgot := some v, sent := some v }, .nat (fcode .completed))
  else some ({ c with w := { c.w with st := .copying }, wval := some v }, .nat blocked)

/-- The event of the readable end (`future_event`): the payload and the value, if delivered. -/
def ftakeR (c : FChan) : Option (FChan × Nat × List Val) :=
  match c.r.ev with
  | none => none
  | some p =>
    if p = 1 then some ({ c with r := { c.r with st := .done, ev := none }, rgot := none },
      fcode .completed, c.rgot.toList)
    else if c.w.gone then some ({ c with r := { c.r with st := .done, ev := none }, rbuf := false },
      fcode .dropped, [])
    else some ({ c with r := { c.r with st := .idle, ev := none }, rbuf := false },
      fcode .cancelled, [])

/-- The event of the writable end. -/
def ftakeW (c : FChan) : Option (FChan × Nat) :=
  match c.w.ev with
  | none => none
  | some p =>
    if p = 1 then some ({ c with w := { c.w with st := .done, ev := none } }, fcode .completed)
    else if c.r.gone then some ({ c with w := { c.w with st := .done, ev := none }, wval := none },
      fcode .dropped)
    else some ({ c with w := { c.w with st := .idle, ev := none }, wval := none }, fcode .cancelled)

/-- `future.cancel-read`: trap unless reading; deliver the pending (or new) event at once. -/
def fcancelR (c : FChan) : Option (FChan × Nat × List Val) :=
  if c.r.gone ∨ c.r.st ≠ .copying then none
  else ftakeR { c with r := { c.r with ev := some (c.r.ev.getD 0) } }

/-- `future.cancel-write`. -/
def fcancelW (c : FChan) : Option (FChan × Nat) :=
  if c.w.gone ∨ c.w.st ≠ .copying then none
  else ftakeW { c with w := { c.w with ev := some (c.w.ev.getD 0) } }

/-- `future.drop-readable`. -/
def fdropR (c : FChan) : Option FChan :=
  if c.r.gone ∨ c.r.st = .copying then none
  else
    let w' := if c.w.gone = false ∧ c.w.st ≠ .done ∧ c.w.ev = none then { c.w with ev := some 0 } else c.w
    some { c with r := { c.r with gone := true, ev := none }, w := w' }

/-- `future.drop-writable`: **traps unless the writable end is `DONE`**. -/
def fdropW (c : FChan) : Option FChan :=
  if c.w.gone ∨ c.w.st ≠ .done then none
  else
    let r' := if c.r.gone = false ∧ c.r.st ≠ .done ∧ c.r.ev = none then { c.r with ev := some 0 } else c.r
    some { c with w := { c.w with gone := true, ev := none }, r := r' }

end FChan

/-- One operation on a future, with the values it hands to the reader. -/
inductive FStep : FChan → FChan → List Val → Prop where
  | read {c c' r} : c.fread = some (c', r) → FStep c c' (delivered r)
  | write {c c' v r} : c.fwrite v = some (c', r) → FStep c c' []
  | takeR {c c' p ys} : c.ftakeR = some (c', p, ys) → FStep c c' ys
  | takeW {c c' p} : c.ftakeW = some (c', p) → FStep c c' []
  | cancelR {c c' p ys} : c.fcancelR = some (c', p, ys) → FStep c c' ys
  | cancelW {c c' p} : c.fcancelW = some (c', p) → FStep c c' []
  | dropR {c c'} : c.fdropR = some c' → FStep c c' []
  | dropW {c c'} : c.fdropW = some c' → FStep c c' []

/-- Future operations, iterated. -/
inductive FSteps : FChan → FChan → List Val → Prop where
  | refl (c : FChan) : FSteps c c []
  | tail {c c' c'' ys zs} : FSteps c c' ys → FStep c' c'' zs → FSteps c c'' (ys ++ zs)

end Silmaril.Wasm.Component.Streams.Cancel
