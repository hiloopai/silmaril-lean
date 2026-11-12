module

public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Handles
public import Silmaril.Raw.Wasm.Component.Runtime.Stream
public import Silmaril.Raw.Wasm.Component.Runtime.Task
public import Silmaril.Raw.Wasm.Component.Runtime.Thread

/-!
# Waitables, waitable sets and subtasks

Transcribes the REF classes `Waitable`, `WaitableSet` and `Subtask` of
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L713-874; `CanonicalABI.md` §"Waitable State" and §"Subtask State") as programs over `Canon.P E σ`,
together with the named pure store updates they issue.

| Lean | REF (line) |
| --- | --- |
| `CStore.waitableCommon?`, `CStore.modifyWaitableCommon` | the `Waitable` base fields (L724-731) |
| `Waitable.setPendingEvent` (`CStore.setPendingSt`) | `Waitable.set_pending_event` (L734-735) |
| `Waitable.hasPendingEvent` (`CStore.waitableHasEvent`) | `Waitable.has_pending_event` (L737-738) |
| `Waitable.inWaitableSet` | `Waitable.in_waitable_set` (L740-741) |
| `Waitable.waitForPendingEvent` | `Waitable.wait_for_pending_event` (L743-747) |
| `Waitable.getPendingEvent` (`takeWaitableEvent`) | `Waitable.get_pending_event` (L749-752) |
| `Waitable.join` (`CStore.joinSt`) | `Waitable.join` (L754-760) |
| `Waitable.dropWaitable` | `Waitable.drop` (L762-764) |
| `wsetHasPendingEvent` (`CStore.wsetHasEvent`) | `WaitableSet.has_pending_event` (L774-775) |
| `wsetGetPendingEvent` | `WaitableSet.get_pending_event` (L777-783), choice C4 |
| `wsetWait` | `WaitableSet.wait` (L785-789) |
| `wsetPoll` | `WaitableSet.poll` (L791-795) |
| `wsetWaitFromCallback` | `WaitableSet.wait_from_callback` (L797-808) |
| `wsetDrop` | `WaitableSet.drop` (L810-812) |
| `CStore.subtaskEvent` | the `subtask_event` closure of `canon_lower` (L2225-2228) |
| `Subtask.addLender` (`Canon.HandleSt.addLender`) | `Subtask.add_lender` (L848-851) |
| `Subtask.resolve` (`CStore.subtaskResolveSt`) | `Subtask.resolve` (L853-858) |
| `Subtask.deliverResolve` (`CStore.deliverResolveSt`) | `Subtask.deliver_resolve` (L860-864) |
| `Subtask.resolveDelivered` (`subtaskResolveDelivered`) | `Subtask.resolve_delivered` (L866-868) |
| `subtaskDrop` | `Subtask.drop` (L870-872) |

Event codes, event tuples and subtask states are the `AsyncRef.EventCode`,
`AsyncRef.EventTuple` and `AsyncRef.SubtaskState` (`Async/Codes.lean`).

**Pending events.** A REF `pending_event` closure is the data `PendingEvent`
(`Runtime/Objects.lean`). `getPendingEvent w` clears the slot and RUNS the closure in one named
store update (`CStore.takeWaitableEventSt`): for a stream/future end this is
`Runtime.takeEvent` (delivery-time state transitions of `stream_event`/`future_event`); for a
subtask it is `CStore.subtaskEvent`, the `subtask_event` closure of an async `canon_lower`
(L2225-2228): `deliver_resolve` if resolved, then `(SUBTASK, subtaski, state)`. The captured
`subtaski` is the subtask's recorded caller handle index `Subtask.index`. As in
`Runtime.takeEvent`, the closure is run on the waitable it is pending on (a closure pending on
a waitable always names that waitable; `subtaskEvent` and `takeEvent` read the waitable's own
id).

**Choice C4.** `wsetGetPendingEvent` issues `choose (.shuffle n)` (through `Canon.shuffle`) and
PERSISTS the permutation into `elems` (REF `random.shuffle(self.elems)` mutates the list) with
the named update `CStore.wsetSetElemsSt`, then takes the first element with a pending event.

**Waiting.** All waits are guest-side (`Thread.waitUntilGuest`, choice C1 with its site):
`waitForPendingEvent` takes the site (K5 `syncCopy` for sync stream/future read/write, K6
`syncCancelCopy` for sync cancel), `wsetWait` is K4 and `wsetWaitFromCallback` is K3.

**Reused transcriptions.** `wsetWaitFromCallback` calls REF `Task.deliver_pending_cancel`
(L481-486) as `Task.deliverPendingCancel` (`Runtime/Task.lean`, named update
`CStore.setTaskState task .cancelDelivered`), and `Subtask.addLender` applies the named update
`Canon.HandleSt.addLender` (`Canon/Handles.lean`, used by `lift_borrow`), so each REF mutation
has exactly one named update.

**Deviations and non-claims.**
* REF `assert`s are preconditions (deviation D-f) and are not checked: `wait_for_pending_event`
  (not in a set, no sync waiter), `join`/`drop` (no sync waiter), `WaitableSet.get_pending_event`
  (some element has an event; each element's `wset` is this set), `add_lender` (not resolved,
  not delivered), `resolve` (state/results shape, not yet resolved), `deliver_resolve`
  (resolved, not yet delivered). Where a fallback is needed: `getPendingEvent` without a
  pending event and `wsetGetPendingEvent` without an eventful element are `TrapReason.internal`
  (REF would crash calling `None`, resp. return `None`); dangling waitable/subtask ids make the
  pure updates of this file no-ops (`joinSt` on a dangling waitable changes nothing; a dangling
  set id only skips that set's `elems` update); `deliverResolveSt` of an already delivered
  subtask (`lenders = none`) changes nothing; `HandleSt.addLender` on a delivered subtask only
  increments the handle's `num_lends` (REF would crash on `None.append`).
* `num_lends -= 1` is truncated `Nat` subtraction (the REF invariant keeps it positive).
* The canon built-ins around these methods (`waitable-set.*`, `waitable.join`,
  `subtask.cancel/drop`: `may_leave`, handle-table lookups and type checks, `unpack_event`)
  belong to the canon built-in items; `wsetDrop` and `subtaskDrop` are the object-level
  `drop` methods only.
* Tests: the pure updates are exercised on a tiny store by kernel `rfl` (generic engine `E`,
  the core store is never inspected); the programs are tested end to end through the machine
  (`Examples/`, `Tests/`). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine AsyncRef Canon

variable {E : CoreEngine}

/-! ## Named pure store updates -/

namespace CStore

end CStore

/-! ## `Waitable` methods -/

namespace Waitable

variable {σ : Type}

end Waitable

/-! ## `WaitableSet` methods -/

section WaitableSetMethods

variable {σ : Type}

end WaitableSetMethods

/-! ## `Subtask` methods -/

namespace Subtask

variable {σ : Type}

end Subtask

/-! ## Program-logic lemmas

Each program preserves a store invariant `I` as soon as the named updates it issues do. -/

section Inv

variable {σ : Type} {I : CStore E → Prop}

theorem Subtask.addLender_inv {st : SubtaskId} {h : HandleObjId}
    (hI : ∀ s, I s → I (HandleSt.addLender st h s)) :
    P.Inv I (Subtask.addLender st h : P E σ Unit) := P.Inv.modifyStore hI

end Inv

/-! ## Basic facts about the pure updates -/

namespace CStore

theorem waitableHasEvent_setPendingSt (s : CStore E) (w : Waitable) (ev : PendingEvent)
    (h : (s.waitableCommon? w).isSome) : (s.setPendingSt w ev).waitableHasEvent w = true := by
  cases w with
  | subtask st =>
    simp only [waitableCommon?, Option.isSome_map] at h
    simp only [setPendingSt, modifyWaitableCommon, waitableHasEvent, subtask?,
      ArenaField.get?_modify_self]
    unfold subtask? at h
    cases hx : ArenaField.subtasks.get? s st <;> simp_all
  | end_ e =>
    simp only [waitableCommon?, Option.isSome_map] at h
    simp only [setPendingSt, modifyWaitableCommon, waitableHasEvent, end?,
      ArenaField.get?_modify_self]
    unfold end? at h
    cases hx : ArenaField.ends.get? s e <;> simp_all

/-- `deliver_resolve` leaves the subtask resolve-delivered. -/
theorem subtaskResolveDelivered_deliverResolveSt (s : CStore E) (st : SubtaskId)
    (h : (s.subtask? st).isSome) : (s.deliverResolveSt st).subtaskResolveDelivered st = true := by
  unfold deliverResolveSt
  cases hx : s.subtask? st with
  | none => simp [hx] at h
  | some x =>
    simp only [subtaskResolveDelivered, subtask?, ArenaField.get?_modify_self]
    have key : ∀ (l : List HandleObjId) (s' : CStore E),
        ArenaField.subtasks.get? (l.foldl (fun s h => ArenaField.resHandles.modify s h
          fun r => { r with numLends := r.numLends - 1 }) s') st =
        ArenaField.subtasks.get? s' st := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih => intro s'; exact ih _
    have hx' : ArenaField.subtasks.get? s st = some x := hx
    simp [key, hx']

end CStore

/-! ## Tests: the pure updates on a tiny store -/

section Tests

/-- A tiny store: subtask 0 started with caller index 3 lending handle 0; subtask 1 returned
with a pending `subtask_event` and caller index 5, lending handles 0 and 1; handle 0 lent
twice, handle 1 once; waitable set 0 containing subtask 1 (whose `wset` is set 0). -/
private def tiny : CStore E :=
  { CStore.empty with
    subtasks := [{ inst := ⟨0⟩, state := .started, index := some 3, lenders := some [⟨0⟩] },
      { inst := ⟨0⟩, state := .returned, index := some 5, lenders := some [⟨0⟩, ⟨1⟩],
        common := { pending := some (.subtask ⟨1⟩), wset := some ⟨0⟩ } }]
    resHandles := [{ rt := ⟨0⟩, rep := 7, own := true, numLends := 2 },
      { rt := ⟨0⟩, rep := 8, own := true, numLends := 1 }]
    wsets := [{ elems := [.subtask ⟨1⟩] }] }

private def lends (s : CStore E) : List Nat := s.resHandles.map (·.numLends)

/-- Delivering subtask 1's pending event: `(SUBTASK, 5, RETURNED)`, lenders released, event
cleared, a second take yields nothing. -/
example : let r := (tiny : CStore E).takeWaitableEvent (.subtask ⟨1⟩)
    (r.2, lends r.1, r.1.subtaskResolveDelivered ⟨1⟩, r.1.waitableHasEvent (.subtask ⟨1⟩),
      (r.1.takeWaitableEvent (.subtask ⟨1⟩)).2) =
    (some ⟨.subtask, 5, 2⟩, [1, 0], true, false, none) := rfl

/-- Subtask 0 has no pending event. -/
example : ((tiny : CStore E).takeWaitableEvent (.subtask ⟨0⟩)).2 = none := rfl

/-- A progress event of an unresolved subtask does not deliver the resolve. -/
example : let s := (tiny : CStore E).setPendingSt (.subtask ⟨0⟩) (.subtask ⟨0⟩)
    let r := s.takeWaitableEvent (.subtask ⟨0⟩)
    (r.2, lends r.1, r.1.subtaskResolveDelivered ⟨0⟩) =
      (some ⟨.subtask, 3, 1⟩, [2, 1], false) :=
  rfl

/-- `add_lender` then `resolve` then `deliver_resolve` on subtask 0. -/
example : let s :=
      ((HandleSt.addLender ⟨0⟩ ⟨1⟩ (tiny : CStore E)).subtaskResolveSt ⟨0⟩ .returned [])
    (lends s, (s.deliverResolveSt ⟨0⟩ |> lends), (s.subtask? ⟨0⟩).map (·.lenders)) =
      ([2, 2], [1, 1], some (some [⟨0⟩, ⟨1⟩])) := rfl

/-- `join` moves subtask 1 from set 0 to a new set 1; `join none` leaves every set. -/
example : let s := { (tiny : CStore E) with wsets := [{ elems := [.subtask ⟨1⟩] }, {}] }
    let s1 := s.joinSt (.subtask ⟨1⟩) (some ⟨1⟩)
    let s2 := s1.joinSt (.subtask ⟨0⟩) (some ⟨1⟩)
    let s3 := s2.joinSt (.subtask ⟨1⟩) none
    (s1.wsets.map (·.elems), s2.wsets.map (·.elems), s3.wsets.map (·.elems),
      (s3.waitableCommon? (.subtask ⟨0⟩)).map (·.wset)) =
      ([[], [.subtask ⟨1⟩]], [[], [.subtask ⟨1⟩, .subtask ⟨0⟩]],
        [[], [.subtask ⟨0⟩]],
        some (some ⟨1⟩)) := rfl

/-- Waitable-set readiness follows its members' pending events. -/
example : (tiny : CStore E).wsetHasEvent ⟨0⟩ = true ∧
    ((tiny : CStore E).takeWaitableEventSt (.subtask ⟨1⟩)).wsetHasEvent ⟨0⟩ = false :=
  ⟨rfl, rfl⟩

/-- `num_waiting` bookkeeping. -/
example :
    (((tiny : CStore E).wsetIncWaitingSt ⟨0⟩).wset? ⟨0⟩).map (·.numWaiting) = some 1 ∧
    ((((tiny : CStore E).wsetIncWaitingSt ⟨0⟩).wsetDecWaitingSt ⟨0⟩).wset? ⟨0⟩).map
      (·.numWaiting) = some 0 := ⟨rfl, rfl⟩

end Tests

end Silmaril.Wasm.Component.Runtime
