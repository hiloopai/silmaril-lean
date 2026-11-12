module

public import Silmaril.Wasm.Component.Reference.Canon.Lift.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
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
# `Canon.Lift`: laws of the component reference

Theorems of the component reference copy `Canon.Lift`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Lift`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem canonLift (H : LiftHyps I) (lim : Limits) (q : Quirks) (callee : E.FuncAddr)
    (ft : WIT.FuncType Empty RtId) (opts : CanonOpts E) (inst : InstId) (caller : CallerId) :
    P.Inv I (Canon.canonLift lim q callee ft opts inst caller : P E σ (Ret E)) := by
  unfold Canon.canonLift
  refine bind (allocObj _ _ (H.allocTask _ _ _ _)) fun task => ?_
  refine bind (newThread _) fun t => ?_
  refine bind (Thread.resume_inv t (H.stopWaiting t)) fun _ => ?_
  refine bind (ite (callUnit _) (pure _)) fun _ => pure _

theorem syncLiftLoopBody (H : LiftHyps I) (hr : HostReady σ) (task : TaskId) :
    P.Inv I (Canon.syncLiftLoopBody hr task : P E σ (Ret E)) := by
  unfold Canon.syncLiftLoopBody
  refine bind (getTask _) fun tk => ?_
  refine ite (pure _) ?_
  refine bind getStore fun s => bind hostGet fun h => ?_
  split
  · exact trap _
  · exact bind (pickSyncLoop _ _) fun t =>
      bind (Thread.resume_inv t (H.stopWaiting t)) fun _ => callRet _

theorem liftSyncTail (H : LiftHyps I) (lim : Limits) (q : Quirks) (task : TaskId)
    (callee : E.FuncAddr) (tk : Task E) (cx : LiftLowerContext E) (flatArgs : List FlatValue) :
    P.Inv I (Canon.liftSyncTail lim q task callee tk cx flatArgs : P E σ Unit) := by
  unfold Canon.liftSyncTail
  refine bind (callCore _ _) fun fr => ?_
  refine bind (liftFlatValues H.load _ _ _ _ _ _) fun _ => ?_
  refine bind (Task.return_inv task _ (fun s => H.task.setTaskState task _ s)) fun _ => ?_
  refine bind ?_ fun _ => Task.exitImplicitThread_inv task H.task
  split
  · exact bind currentThread fun _ => bind (getInst _) fun _ => bind (trapIf _ _) fun _ =>
      bind (modifyInst _ (H.setMayLeave _ _ _)) fun _ => bind (callCore _ _) fun _ =>
        modifyInst _ (H.setMayLeave _ _ _)
  · exact pure _

theorem canonLiftNoop (H : LiftHyps I) (lim : Limits) (q : Quirks)
    (ft : WIT.FuncType Empty RtId) (opts : CanonOpts E) (inst : InstId) (caller : CallerId) :
    P.Inv I (Canon.canonLiftNoop lim q ft opts inst caller : P E σ (Ret E)) := by
  unfold Canon.canonLiftNoop
  refine bind (allocObj _ _ (H.allocTask _ _ _ _)) fun task => ?_
  refine bind (newThread _) fun t => ?_
  refine bind (Thread.resume_inv t (H.stopWaiting t)) fun _ => ?_
  refine bind (ite (callUnit _) (pure _)) fun _ => pure _

theorem onStartProg (c : CallerId) : P.Inv I (Canon.onStartProg c : P E σ (Ret E)) := by
  unfold Canon.onStartProg
  refine bind (getObj _ _) fun x => ?_
  split
  · exact pure _
  · exact bind getStore fun _ => pure _
  · exact pure _
  · exact internal _

theorem onResolveProg (H : LiftHyps I) (c : CallerId) (r : Option (List Val)) :
    P.Inv I (Canon.onResolveProg c r : P E σ (Ret E)) := by
  unfold Canon.onResolveProg
  refine bind (getObj _ _) fun x => ?_
  split
  · split
    · exact bind (modifyObj _ _ _ (H.updateCaller _ _)) fun _ => pure _
    · exact internal _
  · exact pure _
  · exact pure _
  · exact internal _

theorem reallocProg (H : LiftHyps I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (old oldLen align newLen : Nat) :
    P.Inv I (Canon.reallocProg lim q cx old oldLen align newLen : P E σ (Ret E)) := by
  unfold Canon.reallocProg
  refine bind (ptrType _) fun p => bind (orTrap _ _) fun f => ?_
  refine bind (allocObj _ _ (H.allocCaller _)) fun c => ?_
  refine bind currentThread fun _ => bind (getInst _) fun _ => bind (trapIf _ _) fun _ => ?_
  refine bind (modifyInst _ (H.setMayLeave _ _ _)) fun _ => ?_
  refine bind (modifyStore H.incNesting) fun _ => ?_
  refine bind (canonLift H _ _ _ _ _ _ _) fun _ => ?_
  refine bind (modifyStore H.decNesting) fun _ => ?_
  refine bind (modifyInst _ (H.setMayLeave _ _ _)) fun _ => ?_
  refine bind (getObj _ _) fun x => ?_
  split
  · exact pure _
  · exact internal _

theorem destructorCall (H : LiftHyps I) (lim : Limits) (q : Quirks) (inst : InstId)
    (req : DtorRequest E) : P.Inv I (Canon.destructorCall lim q inst req : P E σ Unit) := by
  unfold Canon.destructorCall
  split
  · exact bind (getInst _) fun _ => bind (trapIf _ _) fun _ =>
      bind (getObj _ _) fun _ => bind (allocObj _ _ (H.allocCaller _)) fun _ =>
        bind (canonLift H _ _ _ _ _ _ _) fun _ => pure _
  · exact bind (getInst _) fun _ => bind (trapIf _ _) fun _ =>
      bind (getObj _ _) fun _ => bind (allocObj _ _ (H.allocCaller _)) fun _ =>
        bind (canonLiftNoop H _ _ _ _ _ _) fun _ => pure _
  · exact pure _

end P.Inv

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem callbackLoopBody (H : LiftHyps I) (lim : Limits) (task : TaskId) (thread : ThreadId)
    (code si : Nat) :
    P.Inv I (Canon.callbackLoopBody lim task thread code si : P E σ (Ret E)) := by
  unfold Canon.callbackLoopBody
  refine ite (bind (Task.exitImplicitThread_inv task H.task) fun _ => pure _) ?_
  refine bind (getTask _) fun tk => ?_
  have hc : ∀ s, I s → I (s.setTaskState task .cancelDelivered) :=
    fun s => H.task.setTaskState task _ s
  refine bind ?_ fun ev => ?_
  · show P.Inv I (Task.deliverPendingCancel task >>= fun b =>
      if b = true then Pure.pure AsyncRef.EventTuple.taskCancelled else _)
    refine bind (Task.deliverPendingCancel_inv task hc) fun b => ?_
    refine ite (pure _) ?_
    refine bind (modifyStore (H.release _ _)) fun _ => ?_
    refine bind ?_ fun _ => bind (modifyStore (H.retake _ _)) fun _ => pure _
    split
    · exact bind (Thread.waitUntil_inv _ _ _ (fun t => H.startWaiting t _)) fun _ =>
        bind (Task.deliverPendingCancel_inv task hc) fun _ => ite (pure _) (pure _)
    · refine bind (handlesGet _ _) fun e => ?_
      split
      · exact wsetWaitFromCallback_inv (H.wsetIncWaiting _) (H.wsetDecWaiting _)
          (fun _ _ => H.startWaiting _ _) hc (H.wsetSetElems _) (H.takeWaitableEvent)
      · exact trap _
    · exact trap _
  · refine bind (orTrap _ _) fun cb => bind (callCore _ _) fun r => ?_
    split
    · exact bind (unpackCallbackResult _) fun _ => callRet _
    · exact internal _

theorem liftThreadBody (H : LiftHyps I) (lim : Limits) (q : Quirks) (task : TaskId)
    (callee : E.FuncAddr) :
    P.Inv I (Canon.liftThreadBody lim q task callee : P E σ (Ret E)) := by
  unfold Canon.liftThreadBody
  refine bind (Task.enterImplicitThread_inv q task H.task) fun b => ?_
  refine ite (pure _) ?_
  refine bind (getTask _) fun tk => ?_
  refine bind (Task.start_inv task (fun s => H.task.setTaskState task _ s)) fun args => ?_
  refine bind (lowerFlatValues H.store _ _ _ _ _ _ _) fun fa => ?_
  refine ite (bind (liftSyncTail H _ _ _ _ _ _ _) fun _ => pure _) ?_
  split
  · exact bind (callCore _ _) fun _ =>
      bind (Task.exitImplicitThread_inv task H.task) fun _ => pure _
  · refine bind (callCore _ _) fun r => ?_
    split
    · exact bind (unpackCallbackResult _) fun _ => bind currentThreadId fun _ => callRet _
    · exact internal _

theorem liftNoopThreadBody (H : LiftHyps I) (lim : Limits) (q : Quirks) (task : TaskId) :
    P.Inv I (Canon.liftNoopThreadBody lim q task : P E σ (Ret E)) := by
  unfold Canon.liftNoopThreadBody
  refine bind (Task.enterImplicitThread_inv q task H.task) fun b => ?_
  refine ite (pure _) ?_
  refine bind (getTask _) fun tk => ?_
  refine bind (Task.start_inv task (fun s => H.task.setTaskState task _ s)) fun args => ?_
  refine bind (lowerFlatValues H.store _ _ _ _ _ _ _) fun _ => ?_
  refine bind (liftFlatValues H.load _ _ _ _ _ _) fun _ => ?_
  refine bind (Task.return_inv task _ (fun s => H.task.setTaskState task _ s)) fun _ => ?_
  exact bind (Task.exitImplicitThread_inv task H.task) fun _ => pure _

end P.Inv

end Silmaril.Wasm.Component.Canon
