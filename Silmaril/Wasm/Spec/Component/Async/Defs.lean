module

public import Silmaril.Wasm.Spec.Component.Logic.Defs
public import Silmaril.Wasm.Spec.Joint.Defs

@[expose] public section

/-!
# Streams, futures and async calls: events and logics

The fourth stage of component types (`Level.async`: `stream`, `future`, handles) needs events
for *partial* results: values flow on a stream after the call that created it has returned.
This module keeps the trace-institution format and changes only the payloads (as
`docs/projects/wasm-wasi.md` anticipated: "a payload type with chunks"):

* `AMsg` (questions): `args vs` (a call), `write e vs` (values written to the stream or future
  end `e`), `read e n` (a read of at most `n` values from `e`), `close e` (the end `e` is
  dropped);
* `AOut` (answers): `out o` (the outcome of a call), `written e n` (a write to `e` completed with
  `n` values consumed), `chunk e vs` (a read of `e` delivered `vs`), `closed e` (the peer of `e`
  was dropped: `DROPPED` in the reference's copy results);
* `AEvent X = Event AMsg AOut X`. A stream event sits at the side and index of the function
  whose activation the end belongs to (the call that passed or returned it); the logics below
  do not depend on that index. Async calls need not be well bracketed: a trace may have several
  pending calls.

End identifiers are `ℕ` (the reference's `Runtime.EndId.idx`; `Val.stream e`/`Val.future e`
carry them).

Logics:

* `streamSafe`: every end is closed at most once and never written after it is closed (safety;
  an action invariant, `StreamSafe.toAct`);
* `closedExactlyOnce`: on maximal finite traces, every end that is written is closed exactly once
  (`Logic.ofMaximal`).

**The sync stage inside the async one.** Synchronous component events embed (`args`, `out`):
`syncToAsync S` pushes a synchronous component semantics along this change of base
(`Silmaril.Wasm.Spec.Joint`), with the comorphism `syncCoHom L S` from the institution of pulled
async specifications of `S`-programs. Synchronous programs have no stream traffic, so they
satisfy `streamSafe` (`syncToAsync_streamSafe`).

**Grounding.** The reference semantics copied into `Silmaril.Raw.Wasm.Component` has the
concurrency ABI (`Runtime.Stream`, `Canon.Builtins`: `stream.read/write`, `future.read/write`,
`*.drop-*`, `task.return`, waitable sets) and `refSem` already observes the outcome of
top-level async calls. What it does not provide is a trace interface for the stream traffic of
a run (the machine relates configurations, and `exportBehaviours` only exposes outcomes), and
Silmaril's IR has no streams. So the async logics are tested on the loose semantics and on
embedded synchronous programs; no Core 3.0 program is yet a model with stream events.
-/

namespace Silmaril.Wasm.Spec.Component

/-- Async questions. -/
inductive AMsg where
  /-- A call with arguments. -/
  | args (vs : List RVal)
  /-- Values written to the stream or future end `e`. -/
  | write (e : ℕ) (vs : List RVal)
  /-- A read of at most `n` values from the end `e`. -/
  | read (e n : ℕ)
  /-- The end `e` is dropped. -/
  | close (e : ℕ)

/-- Async answers. -/
inductive AOut where
  /-- The outcome of a call. -/
  | out (o : Outcome)
  /-- A write to `e` completed, `n` values consumed. -/
  | written (e n : ℕ)
  /-- A read of `e` delivered `vs`. -/
  | chunk (e : ℕ) (vs : List RVal)
  /-- The peer of `e` was dropped. -/
  | closed (e : ℕ)

/-- Async events. -/
abbrev AEvent (X : CIface) : Type := Event AMsg AOut X

/-- The end closed by an event, if any. -/
def AMsg.closeEnd? : AMsg → Option ℕ
  | .close e => some e
  | _ => none

/-- The end written by an event, if any. -/
def AMsg.writeEnd? : AMsg → Option ℕ
  | .write e _ => some e
  | _ => none

/-- The question of an event, if it is one. -/
def AEvent.msg? {X : CIface} : AEvent X → Option AMsg
  | .inl (.ask _ m) => some m
  | .inr (.ask _ m) => some m
  | _ => none

/-- The event closes the end `e`. -/
def AEvent.Closes {X : CIface} (e : ℕ) (ev : AEvent X) : Prop :=
  ((AEvent.msg? ev).bind AMsg.closeEnd?) = some e

/-- The event writes to the end `e`. -/
def AEvent.Writes {X : CIface} (e : ℕ) (ev : AEvent X) : Prop :=
  ((AEvent.msg? ev).bind AMsg.writeEnd?) = some e

instance {X : CIface} (e : ℕ) (ev : AEvent X) : Decidable (AEvent.Closes e ev) :=
  inferInstanceAs (Decidable (_ = _))

instance {X : CIface} (e : ℕ) (ev : AEvent X) : Decidable (AEvent.Writes e ev) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Logics -/

/-- The position predicate of `streamSafe`: a close of an already closed end, or a write to
one, never happens. -/
def StreamSafe.pos {X : CIface} : PosPred AMsg AOut X :=
  fun h ev => ∀ e, (AEvent.Closes e ev ∨ AEvent.Writes e ev) → ∀ ev' ∈ h, ¬ AEvent.Closes e ev'

/-- **Stream safety**: every end is closed at most once and never written after closing. -/
abbrev streamSafe : Logic CFn AMsg AOut :=
  Logic.ofTrace (fun _ => Unit) fun _ t => EveryPos StreamSafe.pos t

/-- Stream safety as an action invariant. -/
def StreamSafe.toAct : LogicMap streamSafe (act CFn AMsg AOut) :=
  LogicMap.ofTrace (fun _ => StreamSafe.pos) fun _ _ => Iff.rfl

/-- "Every end written in `t` is closed exactly once in `t`." -/
def ClosedOnce.holds {X : CIface} (_ : Unit) (t : List (AEvent X)) : Prop :=
  ∀ e, (∃ ev ∈ t, AEvent.Writes e ev) → t.countP (fun ev => decide (AEvent.Closes e ev)) = 1

/-- **"Closed exactly once"** (on maximal finite traces). -/
abbrev closedExactlyOnce : Logic CFn AMsg AOut :=
  Logic.ofMaximal (fun _ => Unit) ClosedOnce.holds

/-! ## The synchronous stage inside the asynchronous one -/

/-- A synchronous component semantics with its events read as async events. -/
abbrev syncToAsync (S : Semantics CFn (List RVal) Outcome) : Semantics CFn AMsg AOut :=
  S.push id AMsg.args AOut.out

/-- **The comorphism from pulled async specifications of synchronous programs to async
specifications.** -/
def syncCoHom (L : Logic CFn AMsg AOut) (S : Semantics CFn (List RVal) Outcome) :
    Silmaril.Logic.Institution.Inst.CoHom (inst (L.pull id AMsg.args AOut.out) S)
      (inst L (syncToAsync S)) :=
  pushCoHom L S AMsg.args AOut.out Function.injective_id

end Silmaril.Wasm.Spec.Component
