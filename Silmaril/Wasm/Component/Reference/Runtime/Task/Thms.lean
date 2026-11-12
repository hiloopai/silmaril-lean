module

public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Runtime.Task`: laws of the component reference

Theorems of the component reference copy `Runtime.Task`, refined out of
`Silmaril.Raw.Wasm.Component.Runtime.Task`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async Canon Value

section Updates

variable {E : CoreEngine}

/-- `register_thread` touches only the task, instance and thread arenas. -/
theorem CStore.registerThreadSt_frame (task : TaskId) (t : ThreadId) (s : CStore E) :
    let s' := s.registerThreadSt task t
    s'.core = s.core ∧ s'.waiting = s.waiting ∧ s'.subtasks = s.subtasks ∧ s'.ends = s.ends ∧
      s'.wsets = s.wsets ∧ s'.nestingDepth = s.nestingDepth ∧ s'.lockdown = s.lockdown ∧
      s'.resourceTypes = s.resourceTypes ∧ s'.funcs = s.funcs ∧
      s'.resHandles = s.resHandles ∧ s'.errCtxs = s.errCtxs ∧ s'.callers = s.callers := by
  simp only [registerThreadSt]
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `unregister_thread` touches only the task and instance arenas. -/
theorem CStore.unregisterThreadSt_frame (task : TaskId) (t : ThreadId) (i : Nat)
    (s : CStore E) :
    let s' := s.unregisterThreadSt task t i
    s'.core = s.core ∧ s'.threads = s.threads ∧ s'.waiting = s.waiting ∧
      s'.subtasks = s.subtasks ∧ s'.ends = s.ends ∧ s'.wsets = s.wsets ∧
      s'.nestingDepth = s.nestingDepth ∧ s'.lockdown = s.lockdown ∧
      s'.resourceTypes = s.resourceTypes ∧ s'.funcs = s.funcs ∧
      s'.resHandles = s.resHandles ∧ s'.errCtxs = s.errCtxs ∧ s'.callers = s.callers := by
  simp only [unregisterThreadSt]
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Updates

namespace Task

variable {E : CoreEngine} {σ : Type}

section Inv

variable {I : CStore E → Prop}

theorem deliverPendingCancel_inv (task : TaskId)
    (h : ∀ s, I s → I (s.setTaskState task .cancelDelivered)) :
    P.Inv I (deliverPendingCancel task : P E σ Bool) := by
  unfold deliverPendingCancel
  refine P.Inv.bind (P.Inv.getTask task) fun tk => ?_
  split
  · exact P.Inv.bind (P.Inv.modifyStore h) fun _ => P.Inv.pure _
  · exact P.Inv.pure _

theorem start_inv (task : TaskId) (h : ∀ s, I s → I (s.setTaskState task .started)) :
    P.Inv I (start task : P E σ (List Val)) :=
  P.Inv.bind (P.Inv.getTask task) fun _ =>
    P.Inv.bind (P.Inv.modifyStore h) fun _ => P.Inv.callVals _

theorem return_inv (task : TaskId) (vs : List Val)
    (h : ∀ s, I s → I (s.setTaskState task .resolved)) :
    P.Inv I (return_ task vs : P E σ Unit) :=
  P.Inv.bind (P.Inv.getTask task) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
      P.Inv.bind (P.Inv.callUnit _) fun _ => P.Inv.modifyStore h

theorem cancel_inv (task : TaskId) (h : ∀ s, I s → I (s.setTaskState task .resolved)) :
    P.Inv I (cancel task : P E σ Unit) :=
  P.Inv.bind (P.Inv.getTask task) fun _ =>
    P.Inv.bind (P.Inv.trapIf _ _) fun _ => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
      P.Inv.bind (P.Inv.callUnit _) fun _ => P.Inv.modifyStore h

theorem registerThread_inv (task : TaskId) (t : ThreadId)
    (h : ∀ s, I s → I (s.registerThreadSt task t)) :
    P.Inv I (registerThread task t : P E σ Nat) := by
  unfold registerThread
  refine P.Inv.bind (P.Inv.getTask task) fun tk => ?_
  refine P.Inv.bind (P.Inv.getInst _) fun st => ?_
  split
  · exact P.Inv.trap _
  · exact P.Inv.bind (P.Inv.modifyStore h) fun _ => P.Inv.pure _

theorem unregisterThread_inv (task : TaskId) (t : ThreadId)
    (h : ∀ i s, I s → I (s.unregisterThreadSt task t i)) :
    P.Inv I (unregisterThread task t : P E σ Unit) := by
  unfold unregisterThread
  refine P.Inv.bind (P.Inv.getTask task) fun tk => ?_
  refine P.Inv.bind (P.Inv.trapIf _ _) fun _ => ?_
  refine P.Inv.bind (P.Inv.getThread t) fun th => ?_
  refine P.Inv.bind (P.Inv.orTrap _ _) fun i => ?_
  refine P.Inv.bind (P.Inv.getInst _) fun st => ?_
  split
  · exact P.Inv.trap _
  · exact P.Inv.modifyStore (h i)

theorem backpressureWait_inv (task : TaskId) (inst : InstId) (ne : Bool) (H : InvHyps I) :
    P.Inv I (backpressureWait task inst ne : P E σ Bool) := by
  unfold backpressureWait
  refine P.Inv.bind (P.Inv.modifyInst inst (H.incWaitingToEnter inst)) fun _ => ?_
  refine P.Inv.bind (Thread.waitUntil_inv _ _ _ fun t => H.startWaiting t inst ne) fun _ => ?_
  refine P.Inv.bind (P.Inv.modifyInst inst (H.decWaitingToEnter inst)) fun _ => ?_
  refine P.Inv.bind (deliverPendingCancel_inv task (H.setTaskState task _)) fun b => ?_
  cases b
  · exact P.Inv.pure _
  · exact P.Inv.bind (cancel_inv task (H.setTaskState task _)) fun _ => P.Inv.pure _

theorem asyncGate_inv (q : Quirks) (task : TaskId) (t : ThreadId) (tk : Task E)
    (H : InvHyps I) : P.Inv I (asyncGate q task t tk : P E σ Bool) := by
  unfold asyncGate
  refine P.Inv.bind (P.Inv.getInst _) fun st => ?_
  refine P.Inv.bind ?_ fun b => ?_
  · split
    · exact backpressureWait_inv task _ _ H
    · exact P.Inv.pure _
  · cases b
    · exact P.Inv.pure _
    · refine P.Inv.bind ?_ fun _ => P.Inv.pure _
      split
      · exact P.Inv.modifyInst _ (H.withExclusive _ _)
      · exact P.Inv.pure _

theorem enterImplicitThread_inv (q : Quirks) (task : TaskId) (H : InvHyps I) :
    P.Inv I (enterImplicitThread q task : P E σ Bool) := by
  unfold enterImplicitThread
  refine P.Inv.bind P.Inv.currentThreadId fun t => ?_
  refine P.Inv.bind (P.Inv.modifyStore (H.setImplicitThread task t)) fun _ => ?_
  refine P.Inv.bind (P.Inv.getTask task) fun tk => ?_
  refine P.Inv.bind ?_ fun b => ?_
  · split
    · exact asyncGate_inv q task t tk H
    · exact P.Inv.pure _
  · cases b
    · exact P.Inv.pure _
    · exact P.Inv.bind (registerThread_inv task t (H.registerThread task t)) fun _ =>
        P.Inv.pure _

theorem exitImplicitThread_inv (task : TaskId) (H : InvHyps I) :
    P.Inv I (exitImplicitThread task : P E σ Unit) := by
  unfold exitImplicitThread
  refine P.Inv.bind (P.Inv.getTask task) fun tk => ?_
  refine P.Inv.bind (P.Inv.orTrap _ _) fun t => ?_
  refine P.Inv.bind (unregisterThread_inv task t (H.unregisterThread task t)) fun _ => ?_
  split
  · exact P.Inv.modifyInst _ (H.withExclusive _ _)
  · exact P.Inv.pure _

theorem requestCancellation_inv (hr : HostReady σ) (task : TaskId) (H : InvHyps I) :
    P.Inv I (requestCancellation hr task : P E σ Unit) := by
  unfold requestCancellation
  refine P.Inv.bind (P.Inv.getTask task) fun tk => ?_
  split
  swap
  · exact P.Inv.internal _
  refine P.Inv.bind (P.Inv.orTrap _ _) fun t => ?_
  refine P.Inv.bind (P.Inv.modifyStore (H.setTaskState task _)) fun _ => ?_
  split
  · exact Thread.resume_inv t (H.stopWaiting t)
  · refine P.Inv.bind (P.Inv.getThread t) fun th => ?_
    refine P.Inv.bind (Thread.isReady_inv hr t) fun r => ?_
    split
    · exact Thread.resume_inv t (H.stopWaiting t)
    · exact P.Inv.pure _

end Inv

end Task

end Silmaril.Wasm.Component.Runtime
