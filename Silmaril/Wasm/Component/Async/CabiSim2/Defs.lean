module

public import Silmaril.Wasm.Component.Async.CabiSim.Defs

@[expose] public section

/-!
# The protocol fragment with a waitable set and the values a read delivers

`Silmaril.Wasm.Component.Async.CabiSim` compares the store model `Silmaril.Wasm.Component.Async` with
the transcription `Silmaril.Wasm.Component.Async.Cabi` of `definitions.py` on one stream, at the
level of the end state machine, comparing the copy results and the payloads of taken events.
This module widens that comparison:

* **a waitable set**: both ends joined to one set (the store model's handle `3`, joined by
  `waitable.join 1 3` and `waitable.join 2 3`; the transcription's set `0` with members
  `[end 0, end 1]` in join order), and the operations `waitable-set.poll` and
  `waitable-set.wait` on it (`waitable-set.wait` only when an event is there; otherwise it
  suspends the caller in both models and returns nothing). The answer of `poll`/`wait` names
  the waitable whose event was taken (the store model's handle; the transcription's end
  mapped to the same handle: end `0` is handle `1`, end `1` handle `2`) and its payload; with
  no event, `poll` answers `[0, 0]` (`EventCode.NONE`) in both;
* **the values**: what the reader received, in order (the store model's ghost `sent`,
  the transcription's `hostRecv` of the reader's host buffers);
* **the final stores**: runs return them, so properties of the end state can be compared.

The fragment is otherwise that of `CabiSim` (copies of exactly `c` values, an end copies only
with no pending copy and no untaken event, no drops).
-/

namespace Silmaril.Wasm.Component.Async.CabiSim2

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async.CabiSim

/-- The operations: those of `CabiSim`, and `poll`/`wait` on the set. -/
inductive POp where
  | op (o : FOp)
  /-- `waitable-set.poll 3`. -/
  | poll
  /-- `waitable-set.wait 3`, with an event there. -/
  | wait

/-- `waitable-set.poll 3` (and `wait 3` with an event there) of the store model, with the
handle whose event was taken: `Silmaril.Wasm.Component.Async.step` on `.poll 3`
(`mPoll_step`), answering the handle and the payload, `[0, 0]` for none. -/
def mPoll (m : Silmaril.Wasm.Component.Async.Store) :
    Option (Silmaril.Wasm.Component.Async.Store × List Nat) :=
  if m.tbl 3 = some .wset then
    match Silmaril.Wasm.Component.Async.firstReady m 3 (List.range m.next) with
    | some h => (Silmaril.Wasm.Component.Async.take m h).map fun p => (p.1, [h, p.2.payload])
    | none => some (m, [0, 0])
  else none

/-- One step of the store model (the reader's handle `1`, the writer's `2`, the set `3`). -/
def mStep2 (c : Nat) (m : Silmaril.Wasm.Component.Async.Store) :
    POp → Option (Silmaril.Wasm.Component.Async.Store × List Nat)
  | .op o => (mStep 1 2 c m o).map fun p => (p.1, [p.2])
  | .poll => mPoll m
  | .wait => mPoll m

/-- The handle of the transcription's waitable: end `0` is the reader `1`, end `1` the
writer `2`. -/
def handleOf : Cabi.WRef → Nat
  | .end_ 0 => 1
  | .end_ _ => 2
  | .sub _ => 0

/-- `waitable-set.poll` of the set `0` (L2342–2350, with the event returned instead of
stored): the first member in join order with a pending event, delivered. -/
def cPoll (st : Cabi.Store Val) : Cabi.M (Cabi.Store Val × List Nat) :=
  if st.wsHasPending 0 then do
    let ws ← st.getWs 0
    match ws.elems.find? st.hasPending with
    | some r => do
      let (st, (_, _, p)) ← st.deliver r
      pure (st, [handleOf r, p])
    | none => .error (.assert "get_pending_event: none")
  else pure (st, [0, 0])

/-- One step of the transcription (the reader's end `0`, the writer's `1`). -/
def cStep2 (c : Nat) (st : Cabi.Store Val) : POp → Cabi.M (Cabi.Store Val × List Nat)
  | .op o => (cStep 0 1 c st o).map fun p => (p.1, [p.2])
  | .poll => cPoll st
  | .wait => cPoll st

/-- The fragment. -/
def Allowed2 (c : Nat) (m : Silmaril.Wasm.Component.Async.Store) : POp → Prop
  | .op o => Allowed 1 2 c 1 m o
  | .poll => True
  | .wait => (m.ev 1).isSome ∨ (m.ev 2).isSome

/-- A run of the store model inside the fragment, its answers and its final store. -/
inductive MRun2 (c : Nat) :
    Silmaril.Wasm.Component.Async.Store → List POp → List (List Nat) →
      Silmaril.Wasm.Component.Async.Store → Prop where
  | nil (m) : MRun2 c m [] [] m
  | cons {m m' m'' o os a as} : Allowed2 c m o → mStep2 c m o = some (m', a) →
      MRun2 c m' os as m'' → MRun2 c m (o :: os) (a :: as) m''

/-- A run of the transcription: its final store and answers. -/
def cRun2 (c : Nat) : Cabi.Store Val → List POp → Cabi.M (Cabi.Store Val × List (List Nat))
  | st, [] => pure (st, [])
  | st, o :: os => do
    let (st', a) ← cStep2 c st o
    let (st'', as) ← cRun2 c st' os
    pure (st'', a :: as)

/-- The store model after `stream.new`, `waitable-set.new` (handle `3`) and the joins of both
ends. -/
def mInit2 : Silmaril.Wasm.Component.Async.Store :=
  { mInit with next := 4, tbl := Silmaril.Wasm.Component.Async.upd mInit.tbl 3 (some .wset),
               joined := Silmaril.Wasm.Component.Async.upd
                 (Silmaril.Wasm.Component.Async.upd mInit.joined 1 (some 3)) 2 (some 3) }

/-- The transcription after `new_stream`, a new waitable set `0` and the joins of both ends
(in that order). -/
def cInit2 (t : Cabi.Ty) : Cabi.Store Val :=
  let st := cInit t
  { st with wsets := Cabi.upd st.wsets 0 (some { elems := [.end_ 0, .end_ 1] }), nWsets := 1,
            ends := fun j => (st.ends j).map fun x => { x with wset := some 0 } }

end Silmaril.Wasm.Component.Async.CabiSim2
