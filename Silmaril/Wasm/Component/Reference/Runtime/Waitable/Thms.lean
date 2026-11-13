module

public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Runtime.Waitable`: laws of the component reference

Theorems of the component reference copy `Runtime.Waitable`, refined out of
`Silmaril.Raw.Wasm.Component.Runtime.Waitable`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine AsyncRef Canon
variable {E : CoreEngine}

section Inv

variable {σ : Type} {I : CStore E → Prop}

theorem Waitable.setPendingEvent_inv {w : Waitable} {ev : PendingEvent}
    (h : ∀ s, I s → I (s.setPendingSt w ev)) :
    P.Inv I (Waitable.setPendingEvent w ev : P E σ Unit) := P.Inv.modifyStore h

theorem Waitable.hasPendingEvent_inv (w : Waitable) :
    P.Inv I (Waitable.hasPendingEvent w : P E σ Bool) := P.Inv.gets _

theorem Waitable.inWaitableSet_inv (w : Waitable) :
    P.Inv I (Waitable.inWaitableSet w : P E σ Bool) := P.Inv.gets _

theorem Waitable.getPendingEvent_inv {w : Waitable}
    (h : ∀ s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (Waitable.getPendingEvent w : P E σ EventTuple) := by
  unfold Waitable.getPendingEvent
  refine P.Inv.bind P.Inv.getStore fun s => ?_
  split
  · exact P.Inv.internal _
  · exact P.Inv.bind (P.Inv.modifyStore h) fun _ => P.Inv.pure _

theorem Waitable.waitForPendingEvent_inv (site : WaitSite) {w : Waitable}
    (hs : ∀ o s, I s → I (s.setSyncWaiterSt w o))
    (hw : ∀ t s, I s → I (s.startWaitingSt t (.waitableHasEvent w))) :
    P.Inv I (Waitable.waitForPendingEvent site w : P E σ Unit) :=
  P.Inv.bind P.Inv.currentThreadId fun _ => P.Inv.bind (P.Inv.modifyStore (hs _)) fun _ =>
    P.Inv.bind (Thread.waitUntil_inv _ _ _ hw) fun _ => P.Inv.modifyStore (hs none)

theorem Waitable.join_inv {w : Waitable} {ws : Option WsetId}
    (h : ∀ s, I s → I (s.joinSt w ws)) : P.Inv I (Waitable.join w ws : P E σ Unit) :=
  P.Inv.modifyStore h

theorem Waitable.dropWaitable_inv {w : Waitable} (h : ∀ s, I s → I (s.joinSt w none)) :
    P.Inv I (Waitable.dropWaitable w : P E σ Unit) := Waitable.join_inv h

theorem wsetHasPendingEvent_inv (ws : WsetId) :
    P.Inv I (wsetHasPendingEvent ws : P E σ Bool) := P.Inv.gets _

theorem wsetGetPendingEvent_inv {ws : WsetId}
    (he : ∀ l s, I s → I (s.wsetSetElemsSt ws l))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (wsetGetPendingEvent ws : P E σ EventTuple) := by
  unfold wsetGetPendingEvent
  refine P.Inv.bind (P.Inv.getObj _ _) fun x => ?_
  refine P.Inv.bind (P.Inv.shuffle _) fun l => ?_
  refine P.Inv.bind (P.Inv.modifyStore (he l)) fun _ => ?_
  refine P.Inv.bind P.Inv.getStore fun s => ?_
  split
  · exact Waitable.getPendingEvent_inv (ht _)
  · exact P.Inv.internal _

theorem wsetWait_inv {ws : WsetId}
    (hi : ∀ s, I s → I (s.wsetIncWaitingSt ws)) (hd : ∀ s, I s → I (s.wsetDecWaitingSt ws))
    (hw : ∀ t s, I s → I (s.startWaitingSt t (.wsetHasEvent ws)))
    (he : ∀ l s, I s → I (s.wsetSetElemsSt ws l))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (wsetWait ws : P E σ EventTuple) :=
  P.Inv.bind (P.Inv.modifyStore hi) fun _ =>
    P.Inv.bind (Thread.waitUntil_inv _ _ _ hw) fun _ =>
      P.Inv.bind (P.Inv.modifyStore hd) fun _ => wsetGetPendingEvent_inv he ht

theorem wsetPoll_inv {ws : WsetId}
    (he : ∀ l s, I s → I (s.wsetSetElemsSt ws l))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (wsetPoll ws : P E σ EventTuple) := by
  unfold wsetPoll
  refine P.Inv.bind (wsetHasPendingEvent_inv ws) fun b => ?_
  cases b
  · exact P.Inv.pure _
  · exact wsetGetPendingEvent_inv he ht

theorem wsetWaitFromCallback_inv {ws : WsetId} {task : TaskId}
    (hi : ∀ s, I s → I (s.wsetIncWaitingSt ws)) (hd : ∀ s, I s → I (s.wsetDecWaitingSt ws))
    (hw : ∀ inst t s, I s → I (s.startWaitingSt t (.callbackWait inst task ws)))
    (hc : ∀ s, I s → I (s.setTaskState task .cancelDelivered))
    (he : ∀ l s, I s → I (s.wsetSetElemsSt ws l))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (wsetWaitFromCallback ws task : P E σ EventTuple) := by
  unfold wsetWaitFromCallback
  refine P.Inv.bind (P.Inv.getTask _) fun x => ?_
  refine P.Inv.bind (P.Inv.modifyStore hi) fun _ => ?_
  refine P.Inv.bind (Thread.waitUntil_inv _ _ _ (hw x.inst)) fun _ => ?_
  refine P.Inv.bind (P.Inv.modifyStore hd) fun _ => ?_
  refine P.Inv.bind (Task.deliverPendingCancel_inv task hc) fun b => ?_
  cases b
  · exact wsetGetPendingEvent_inv he ht
  · exact P.Inv.pure _

theorem wsetDrop_inv (ws : WsetId) : P.Inv I (wsetDrop ws : P E σ Unit) :=
  P.Inv.bind (P.Inv.getObj _ _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.trapIf _ _

theorem Subtask.resolve_inv {st : SubtaskId} {state : SubtaskState} {flat : List FlatValue}
    (h : ∀ s, I s → I (s.subtaskResolveSt st state flat)) :
    P.Inv I (Subtask.resolve st state flat : P E σ Unit) := P.Inv.modifyStore h

theorem Subtask.deliverResolve_inv {st : SubtaskId} (h : ∀ s, I s → I (s.deliverResolveSt st)) :
    P.Inv I (Subtask.deliverResolve st : P E σ Unit) := P.Inv.modifyStore h

theorem Subtask.resolveDelivered_inv (st : SubtaskId) :
    P.Inv I (Subtask.resolveDelivered st : P E σ Bool) := P.Inv.gets _

theorem subtaskDrop_inv {st : SubtaskId} (h : ∀ s, I s → I (s.joinSt (.subtask st) none)) :
    P.Inv I (subtaskDrop st : P E σ Unit) :=
  P.Inv.bind (Subtask.resolveDelivered_inv st) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => Waitable.dropWaitable_inv h

end Inv

end Silmaril.Wasm.Component.Runtime
