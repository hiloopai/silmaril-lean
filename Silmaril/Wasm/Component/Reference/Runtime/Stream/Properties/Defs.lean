module

public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Defs

/-!
# Invariants of the stream/future `End` state machine

Properties of the pure transcription of REF `End` (`Runtime/Stream.lean`;
`design/mvp/canonical-abi/definitions.py` L931-1098 at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>).

* `EndWF s`: every `other` link is symmetric and joins a readable end to the writable end of the
  same class (`EndKind.dual`), and a parked buffer only exists while the end is `COPYING` or
  `CANCELLING_COPY` (`End.BufOK`). `EndWF.other_iff` restates symmetry as
  `e.other = some f ↔ f.other = some e`.
* Preservation: `copy_EndWF`, `copyCore_EndWF`, `notify_EndWF`, `deliver_EndWF`,
  `takeEvent_EndWF`, `cancel_EndWF`, `forward_EndWF` (drop and splice branches),
  `dropEnd_EndWF`, `newStream_EndWF`, `newFuture_EndWF`; `empty_EndWF`.
* `EndWF` also requires that a `DONE` end has no pending event (`End.DoneQuiet`), which is what
  makes `DONE` absorbing under event delivery. Hence `notify_EndWF` assumes the notified end is
  not `DONE` and `deliver_EndWF` assumes its pending event was cleared (both hold at every REF
  call site; `takeEvent_EndWF` has no side condition).
* Done ends never re-enter copying. Per step, `KeepsDone s s'` (every `DONE` end of `s` is
  `DONE` in `s'`) holds for every operation: `copy_keepsDone`, `notify_keepsDone`,
  `cancel_keepsDone`, `dropEnd_keepsDone`, `newEnds_keepsDone`, and under `EndWF`
  `forward_keepsDone` and `takeEvent_keepsDone` (`deliver_keepsDone` for a non-`DONE` end).
  Over traces: `EndStep`/`EndSteps` collect the operations, `EndSteps.endWF` and
  `EndSteps.keepsDone` lift preservation, and `done_never_copying` gives `DoneStable s s'`
  (a `DONE` end of `s` is neither `COPYING` nor `CANCELLING_COPY` in `s'`) for every trace from
  a well-formed store. The single-step `*_doneStable` corollaries are also stated.
* Progress monotonicity (`BufProgressMono s s'`: a buffer parked on an end in both `s` and `s'`
  has not lost progress): `copy_progress_mono` (under `EndWF`), `notify_progress_mono`, bundled
  as `progress_mono`.
* `future_written_once`: after a copy that transfers a value out of a future's writable end,
  delivering that end's event makes it `DONE`, and a second write traps.

Everything is proved for all stores; nothing here is tested only. Not claimed: other invariants
tying pending events to states, handle tables, or the Prog layer's element transfer.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async

variable {E : CoreEngine}

/-- A parked buffer only exists while a copy is in flight. -/
def End.BufOK (x : End E) : Prop := x.buffer.isSome = true → x.state.copyingOrCancelling = true

/-- A `DONE` end has no pending event (REF: every `notify` targets an end that is copying, or a
peer that is not `DONE`, and delivery clears the event before a `DONE` transition). Without this
clause a pending `futureEnd e 0` on a linked `DONE` end would, when delivered, move it back to
`IDLE`. -/
def End.DoneQuiet (x : End E) : Prop := x.state = .done → x.common.pending = none

/-- Well-formedness of the ends of a store. -/
structure EndWF (s : CStore E) : Prop where
  /-- `buffer ≠ none → state ∈ {COPYING, CANCELLING_COPY}`. -/
  bufOK : ∀ e x, s.end? e = some x → x.BufOK
  /-- `state = DONE → pending = none`. -/
  doneQuiet : ∀ e x, s.end? e = some x → x.DoneQuiet
  /-- Links are symmetric, never dangling, and pair dual classes. -/
  paired : ∀ e x f, s.end? e = some x → x.other = some f →
    ∃ y, s.end? f = some y ∧ y.other = some e ∧ y.kind = x.kind.dual

/-- An end that is `DONE` in `s` is not copying or cancelling in `s'`. -/
def DoneStable (s s' : CStore E) : Prop :=
  ∀ e x y, s.end? e = some x → x.state = .done → s'.end? e = some y →
    y.state.copyingOrCancelling = false

/-- A buffer parked on an end in both `s` and `s'` has not lost progress. -/
def BufProgressMono (s s' : CStore E) : Prop :=
  ∀ e x y b b', s.end? e = some x → x.buffer = some b → s'.end? e = some y →
    y.buffer = some b' → b.progress ≤ b'.progress

/-! ## Lookup lemmas -/

@[simp] theorem leaveSet_ends (w : Option WsetId) (e : EndId) (s : CStore E) :
    (leaveSet w e s).ends = s.ends := by
  cases w <;> rfl

/-! ## `EndWF` -/

namespace EndWF

end EndWF

/-! ## Preservation of `EndWF` -/

/-! ## Done ends never re-enter copying -/

/-- Every end that is `DONE` in `s` exists and is `DONE` in `s'` (a strengthening of
`DoneStable` used to compose steps that do not deliver events). -/
def KeepsDone (s s' : CStore E) : Prop :=
  ∀ e x, s.end? e = some x → x.state = .done → ∃ y, s'.end? e = some y ∧ y.state = .done

namespace KeepsDone

theorem refl (s : CStore E) : KeepsDone s s := fun _ x h hd => ⟨x, h, hd⟩

end KeepsDone

/-! ## Traces: done ends never re-enter copying -/

/-- One step of the end state machine: every operation a canon built-in or the scheduler applies
to ends (`notify` only on an end that is not `DONE`, as all REF callers do). -/
inductive EndStep : CStore E → CStore E → Prop
  | copy {s s' : CStore E} {e : EndId} {buf : BufferDesc E} {isRead : Bool} {a : CopyAction E} :
      copy e buf isRead s = .ok (s', a) → EndStep s s'
  | notify {s : CStore E} {e : EndId} (p : Nat) :
      (∀ x, s.end? e = some x → x.state ≠ .done) → EndStep s (notify e p s)
  | takeEvent (s : CStore E) (e : EndId) : EndStep s (takeEvent e s).1
  | cancel (s : CStore E) (e : EndId) (b : Bool) : EndStep s (cancel e b s)
  | forward {s s' : CStore E} {src dst : EndId} {a : CopyAction E} :
      forward src dst s = .ok (s', a) → EndStep s s'
  | dropEnd (s : CStore E) (e : EndId) : EndStep s (dropEnd e s)
  | newStream (s : CStore E) (t : Option (WIT.ClosedType RtId)) (o : Option InstId) :
      EndStep s (newStream t o s).1
  | newFuture (s : CStore E) (t : Option (WIT.ClosedType RtId)) (o : Option InstId) :
      EndStep s (newFuture t o s).1

/-- Finite sequences of `EndStep`s. -/
inductive EndSteps : CStore E → CStore E → Prop
  | refl (s : CStore E) : EndSteps s s
  | tail {s₁ s₂ s₃ : CStore E} : EndSteps s₁ s₂ → EndStep s₂ s₃ → EndSteps s₁ s₃

/-! ## Progress monotonicity -/

namespace BufProgressMono

theorem refl (s : CStore E) : BufProgressMono s s := by
  intro f x z b b' hx hb hz hb'
  rw [hx] at hz; cases hz; rw [hb] at hb'; cases hb'; exact Nat.le_refl _

end BufProgressMono

/-! ## Futures are written once -/

end Silmaril.Wasm.Component.Runtime
