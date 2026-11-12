module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Builtins.Waitable`: laws of the component reference

Theorems of the component reference copy `Canon.Builtins.Waitable`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Builtins.Waitable`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.AsyncRef _root_.Silmaril.Wasm.Component.Canon
variable {E : CoreEngine} {σ : Type}

namespace Inv

variable {I : CStore E → Prop}

theorem enterWaitableBuiltin : P.Inv I (Builtins.enterWaitableBuiltin : P E σ InstId) :=
  P.Inv.bind P.Inv.currentInst fun _ =>
    P.Inv.bind (P.Inv.getInst _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.pure _

theorem expectWset (e : HandleEntry) : P.Inv I (Builtins.expectWset e : P E σ WsetId) := by
  cases e <;> first | exact P.Inv.pure _ | exact P.Inv.trap _

theorem expectWaitable (e : HandleEntry) :
    P.Inv I (Builtins.expectWaitable e : P E σ Runtime.Waitable) := by
  cases e <;> first | exact P.Inv.pure _ | exact P.Inv.trap _

theorem expectSubtask (e : HandleEntry) :
    P.Inv I (Builtins.expectSubtask e : P E σ SubtaskId) := by
  unfold Builtins.expectSubtask
  split
  · exact P.Inv.pure _
  · exact P.Inv.trap _

theorem subtaskResolvedNow (st : SubtaskId) :
    P.Inv I (Builtins.subtaskResolvedNow st : P E σ Bool) := P.Inv.gets _

theorem waitableHasSyncWaiter (w : Runtime.Waitable) :
    P.Inv I (Builtins.waitableHasSyncWaiter w : P E σ Bool) :=
  P.Inv.bind P.Inv.getStore fun s => by
    cases s.waitableCommon? w <;> first | exact P.Inv.pure _ | exact P.Inv.internal _

theorem waitableSetNew (lim : Limits)
    (hA : ∀ s, I s → I (ArenaOps.allocSt ArenaField.wsets ({} : WaitableSet) s))
    (hH : ∀ inst ws s, I s → I (ArenaField.insts.modify s inst (InstState.addHandle (.wset ws)))) :
    P.Inv I (Builtins.waitableSetNew lim : P E σ _) :=
  P.Inv.bind enterWaitableBuiltin fun inst =>
    P.Inv.bind (P.Inv.allocObj _ _ hA) fun _ =>
      P.Inv.bind (P.Inv.handlesAdd inst _ (hH inst _)) fun _ => P.Inv.pure _

theorem waitableSetWait (lim : Limits) (mem : E.MemAddr) (si ptr : Nat)
    (hi : ∀ ws s, I s → I (s.wsetIncWaitingSt ws))
    (hd : ∀ ws s, I s → I (s.wsetDecWaitingSt ws))
    (hw : ∀ ws t s, I s → I (s.startWaitingSt t (.wsetHasEvent ws)))
    (he : ∀ ws l s, I s → I (s.wsetSetElemsSt ws l))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) (hm : MemWritePres I) :
    P.Inv I (Builtins.waitableSetWait lim mem si ptr : P E σ _) :=
  P.Inv.bind enterWaitableBuiltin fun inst =>
    P.Inv.bind (P.Inv.handlesGet inst si) fun e => P.Inv.bind (expectWset e) fun ws =>
      P.Inv.bind (wsetWait_inv (hi ws) (hd ws) (hw ws) (he ws) ht) fun _ =>
        P.Inv.bind (P.Inv.unpackEvent _ _ _ hm) fun _ => P.Inv.pure _

theorem waitableSetPoll (lim : Limits) (mem : E.MemAddr) (si ptr : Nat)
    (he : ∀ ws l s, I s → I (s.wsetSetElemsSt ws l))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) (hm : MemWritePres I) :
    P.Inv I (Builtins.waitableSetPoll lim mem si ptr : P E σ _) :=
  P.Inv.bind enterWaitableBuiltin fun inst =>
    P.Inv.bind (P.Inv.handlesGet inst si) fun e => P.Inv.bind (expectWset e) fun ws =>
      P.Inv.bind (wsetPoll_inv (he ws) ht) fun _ =>
        P.Inv.bind (P.Inv.unpackEvent _ _ _ hm) fun _ => P.Inv.pure _

theorem waitableSetDrop (lim : Limits) (i : Nat)
    (hR : ∀ inst s, I s → I (ArenaField.insts.modify s inst (InstState.removeHandle i))) :
    P.Inv I (Builtins.waitableSetDrop lim i : P E σ _) :=
  P.Inv.bind enterWaitableBuiltin fun inst =>
    P.Inv.bind (P.Inv.handlesRemove inst i (hR inst)) fun e =>
      P.Inv.bind (expectWset e) fun ws =>
      P.Inv.bind (wsetDrop_inv ws) fun _ => P.Inv.pure _

theorem waitableJoin (lim : Limits) (wi si : Nat)
    (hj : ∀ w ws s, I s → I (s.joinSt w ws)) :
    P.Inv I (Builtins.waitableJoin lim wi si : P E σ _) := by
  unfold Builtins.waitableJoin
  refine P.Inv.bind enterWaitableBuiltin fun inst => ?_
  refine P.Inv.bind (P.Inv.handlesGet inst wi) fun e => P.Inv.bind (expectWaitable e) fun w => ?_
  refine P.Inv.bind (waitableHasSyncWaiter w) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ => ?_
  split
  · exact P.Inv.bind (Runtime.Waitable.join_inv (hj w none)) fun _ => P.Inv.pure _
  · exact P.Inv.bind (P.Inv.handlesGet inst si) fun e => P.Inv.bind (expectWset e) fun ws =>
      P.Inv.bind (Runtime.Waitable.join_inv (hj w (some ws))) fun _ => P.Inv.pure _

theorem subtaskCancelDeliver (st : SubtaskId)
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (Builtins.subtaskCancelDeliver st : P E σ _) :=
  P.Inv.bind (Runtime.Waitable.getPendingEvent_inv (ht _)) fun _ =>
    P.Inv.bind (P.Inv.getObj _ _) fun _ => P.Inv.pure _

theorem subtaskCancelRequest (async_ : Bool) (st : SubtaskId) (r : CancelRef)
    (hc : ∀ t s, I s → I (WaitableSt.requestCancel st t s))
    (hw : ∀ t s, I s → I (s.startWaitingSt t (.subtaskResolved st)))
    (hs : ∀ s, I s → I (s.setSyncWaiterSt (.subtask st) none)) :
    P.Inv I (Builtins.subtaskCancelRequest async_ st r : P E σ Bool) := by
  unfold Builtins.subtaskCancelRequest
  refine P.Inv.bind P.Inv.currentThreadId fun t => P.Inv.bind (P.Inv.modifyStore (hc t)) fun _ => ?_
  refine P.Inv.bind (P.Inv.callUnit _) fun _ => ?_
  refine P.Inv.bind ?_ fun _ =>
    P.Inv.bind (P.Inv.modifyStore hs) fun _ => subtaskResolvedNow st
  unfold Builtins.subtaskCancelSyncWait
  refine P.Inv.bind (subtaskResolvedNow st) fun _ => ?_
  split
  · exact Thread.waitUntil_inv _ _ _ hw
  · exact P.Inv.pure _

theorem subtaskCancel (lim : Limits) (async_ : Bool) (i : Nat)
    (hc : ∀ st t s, I s → I (WaitableSt.requestCancel st t s))
    (hw : ∀ st t s, I s → I (s.startWaitingSt t (.subtaskResolved st)))
    (hs : ∀ st s, I s → I (s.setSyncWaiterSt (.subtask st) none))
    (ht : ∀ w s, I s → I (s.takeWaitableEventSt w)) :
    P.Inv I (Builtins.subtaskCancel lim async_ i : P E σ _) := by
  unfold Builtins.subtaskCancel
  refine P.Inv.bind enterWaitableBuiltin fun inst => ?_
  refine P.Inv.bind (P.Inv.handlesGet inst i) fun e => P.Inv.bind (expectSubtask e) fun st => ?_
  refine P.Inv.bind (Subtask.resolveDelivered_inv st) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => ?_
  refine P.Inv.bind (P.Inv.getObj _ _) fun x => ?_
  refine P.Inv.bind (P.Inv.trapIf _ _) fun _ => ?_
  refine P.Inv.bind (Runtime.Waitable.inWaitableSet_inv _) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => ?_
  split
  · exact subtaskCancelDeliver st ht
  · refine P.Inv.bind (subtaskCancelRequest async_ st _ (hc st) (hw st) (hs st)) fun b => ?_
    cases b
    · exact P.Inv.pure _
    · exact subtaskCancelDeliver st ht

theorem subtaskDrop (lim : Limits) (i : Nat)
    (hR : ∀ inst s, I s → I (ArenaField.insts.modify s inst (InstState.removeHandle i)))
    (hj : ∀ st s, I s → I (s.joinSt (.subtask st) none)) :
    P.Inv I (Builtins.subtaskDrop lim i : P E σ _) :=
  P.Inv.bind enterWaitableBuiltin fun inst =>
    P.Inv.bind (P.Inv.handlesRemove inst i (hR inst)) fun e =>
      P.Inv.bind (expectSubtask e) fun st =>
      P.Inv.bind (subtaskDrop_inv (hj st)) fun _ => P.Inv.pure _

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
