module

public import Silmaril.Wasm.Component.Async.CabiRef.Defs
public import Silmaril.Wasm.Component.Async.Defs

@[expose] public section

/-!
# A protocol fragment on which the store model simulates `definitions.py`

`Silmaril.Wasm.Component.Async.CabiAgree` compares the store model `Silmaril.Wasm.Component.Async`
with the transcription `Silmaril.Wasm.Component.Async.Cabi` on bounded families of traces. This
module sets up an **unbounded** comparison on a protocol fragment, at the level of one stream
and its two ends:

* **the store model**: the channel `s` with the reader handle `r` and the writer handle `w`,
  operated by `stream.read r c`, `stream.write w xs` and the taking of a handle's pending event
  (`Silmaril.Wasm.Component.Async.take`);
* **the transcription**: the ends `er` (readable) and `ew` (writable), operated by `End.copy`
  with a fresh buffer followed, as in the canon `copy` built-in, by the delivery of the end's
  event when it is already there (`cCopy`), and by the delivery of a pending event
  (`deliverEnd`). Buffers are host buffers: a writer's values are the buffer's `src`.

**The fragment** (`Allowed`): every copy moves exactly `c > 0` elements (`stream.write` of `c`
values, `stream.read` of `c`); an end starts a copy only when it has no pending copy and its
previous event was taken (`definitions.py` traps otherwise: difference 4); events are taken
only when present; no end is dropped. Outside it the models differ (differences 1–8 of
`CabiAgree`); inside it they agree on every answer (`CabiSim.Thms`).

**Answers** (`Nat`): `BLOCKED`, or the packed result of a copy that completed at once, or the
payload of a taken event.
-/

namespace Silmaril.Wasm.Component.Async.CabiSim

open Silmaril.Wasm.Component (Val)

/-- The fragment's operations. -/
inductive FOp where
  /-- `stream.write w xs`. -/
  | write (xs : List Val)
  /-- `stream.read r c`. -/
  | read
  /-- Take the reader's pending event. -/
  | takeR
  /-- Take the writer's pending event. -/
  | takeW

/-- The store model's answer as a number. -/
def resNat : Silmaril.Wasm.Component.Async.Res → Nat
  | .nat n => n
  | .read code _ => code
  | .event e => e.payload
  | _ => 0

/-- One step of the store model. -/
def mStep (r w c : Nat) (m : Silmaril.Wasm.Component.Async.Store) :
    FOp → Option (Silmaril.Wasm.Component.Async.Store × Nat)
  | .write xs => (Silmaril.Wasm.Component.Async.streamWrite m w xs).map fun p => (p.1, resNat p.2)
  | .read => (Silmaril.Wasm.Component.Async.streamRead m r c).map fun p => (p.1, resNat p.2)
  | .takeR => (Silmaril.Wasm.Component.Async.take m r).map fun p => (p.1, p.2.payload)
  | .takeW => (Silmaril.Wasm.Component.Async.take m w).map fun p => (p.1, p.2.payload)

/-- `End.copy` with the buffer `b`, then the delivery of the end's event if it is already
there (the canon `copy` built-in, L2442–2460, with `opts.async_`). -/
def cCopy (st : Cabi.Store Val) (e : Nat) (bx : Cabi.Buf Val) : Cabi.M (Cabi.Store Val × Nat) :=
  let (st, b) := st.newBuf bx
  do
    let st ← st.copyEnd e b
    if st.hasPending (.end_ e) then do
      let (st, (_, _, p)) ← st.deliverEnd e
      pure (st, p)
    else pure (st, Cabi.BLOCKED)

/-- One step of the transcription. -/
def cStep (er ew c : Nat) (st : Cabi.Store Val) : FOp → Cabi.M (Cabi.Store Val × Nat)
  | .write xs => cCopy st ew { inst := none, length := xs.length, src := xs }
  | .read => cCopy st er { inst := none, length := c }
  | .takeR => (st.deliverEnd er).map fun p => (p.1, p.2.2.2)
  | .takeW => (st.deliverEnd ew).map fun p => (p.1, p.2.2.2)

/-- The protocol fragment, judged on the store model's state. -/
def Allowed (r w c s : Nat) (m : Silmaril.Wasm.Component.Async.Store) : FOp → Prop
  | .write xs => xs.length = c ∧ m.ev w = none ∧
      ∀ h ys, (m.chans s).pend ≠ .write h ys
  | .read => m.ev r = none ∧ ∀ h n, (m.chans s).pend ≠ .read h n
  | .takeR => (m.ev r).isSome
  | .takeW => (m.ev w).isSome

/-- A run of the store model inside the fragment, with its answers. -/
inductive MRun (r w c s : Nat) :
    Silmaril.Wasm.Component.Async.Store → List FOp → List Nat → Prop where
  | nil (m) : MRun r w c s m [] []
  | cons {m m' o os a as} : Allowed r w c s m o → mStep r w c m o = some (m', a) →
      MRun r w c s m' os as → MRun r w c s m (o :: os) (a :: as)

/-- A run of the transcription: its answers. -/
def cRun (er ew c : Nat) : Cabi.Store Val → List FOp → Cabi.M (List Nat)
  | _, [] => pure []
  | st, o :: os => do
    let (st', a) ← cStep er ew c st o
    let as ← cRun er ew c st' os
    pure (a :: as)

/-! ## The simulation relation -/

/-- The transcription's readable end for the store model's pending copy and reader event:
taken-or-idle, parked (a fresh host buffer for `c` values), or with its completion pending. -/
def RShape (c : Nat) (st : Cabi.Store Val) (pend : Silmaril.Wasm.Component.Async.Pend)
    (ev : Option Silmaril.Wasm.Component.Async.Event) (x : Cabi.End) : Prop :=
  match ev, pend with
  | some _, _ => x.state = .copying ∧ x.buffer = none ∧ x.pending = some c
  | none, .read _ _ => x.state = .copying ∧ x.pending = none ∧
      ∃ b bx, x.buffer = some b ∧ st.bufs b = some bx ∧ b < st.nBufs ∧ bx.inst = none ∧
        bx.length = c ∧ bx.progress = 0
  | none, _ => x.state = .idle ∧ x.buffer = none ∧ x.pending = none

/-- The transcription's writable end, likewise; a parked write is a host buffer holding the
values. -/
def WShape (c : Nat) (st : Cabi.Store Val) (pend : Silmaril.Wasm.Component.Async.Pend)
    (ev : Option Silmaril.Wasm.Component.Async.Event) (x : Cabi.End) : Prop :=
  match ev, pend with
  | some _, _ => x.state = .copying ∧ x.buffer = none ∧ x.pending = some c
  | none, .write _ xs => x.state = .copying ∧ x.pending = none ∧
      ∃ b bx, x.buffer = some b ∧ st.bufs b = some bx ∧ b < st.nBufs ∧ bx.inst = none ∧
        bx.length = c ∧ bx.progress = 0 ∧ bx.src = xs
  | none, _ => x.state = .idle ∧ x.buffer = none ∧ x.pending = none

/-- **The simulation relation** between the store model's channel `s` (handles `r`, `w`) and
the transcription's ends `er`, `ew`, for chunks of `c` values. -/
structure Rel (r w s er ew c : Nat) (m : Silmaril.Wasm.Component.Async.Store)
    (st : Cabi.Store Val) : Prop where
  pos : 0 < c
  tblR : m.tbl r = some (.streamR s)
  tblW : m.tbl w = some (.streamW s)
  hrw : r ≠ w
  noDropR : (m.chans s).rDropped = false
  noDropW : (m.chans s).wDropped = false
  pendRead : ∀ h n, (m.chans s).pend = .read h n → h = r ∧ n = c ∧ m.ev r = none
  pendWrite : ∀ h xs, (m.chans s).pend = .write h xs → h = w ∧ xs.length = c ∧ m.ev w = none
  evR : ∀ e, m.ev r = some e → e.payload = 16 * c
  evW : ∀ e, m.ev w = some e → e.payload = 16 * c
  hne : er ≠ ew
  endR : ∃ x, st.ends er = some x ∧ x.kind = .streamR ∧ x.other = some ew ∧ x.owner = none ∧
    RShape c st (m.chans s).pend (m.ev r) x
  endW : ∃ x, st.ends ew = some x ∧ x.kind = .streamW ∧ x.other = some er ∧ x.owner = none ∧
    WShape c st (m.chans s).pend (m.ev w) x

/-- The store model with one new stream (handles `1`, `2`; channel `1`). -/
def mInit : Silmaril.Wasm.Component.Async.Store :=
  (Silmaril.Wasm.Component.Async.Store.empty.alloc2 .streamR .streamW).1

/-- The transcription with one new stream of element type `t` (ends `0`, `1`). -/
def cInit (t : Cabi.Ty) : Cabi.Store Val := ((Cabi.Store.init 0 : Cabi.Store Val).newPair true t none).1

end Silmaril.Wasm.Component.Async.CabiSim
