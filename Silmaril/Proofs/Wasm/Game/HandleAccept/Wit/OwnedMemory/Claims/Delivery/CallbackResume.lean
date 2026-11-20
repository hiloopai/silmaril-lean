module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Callback.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackEarly
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall ComponentCall.Delivery

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start atResume : Config (core3 grow) (HostState sig)} {wait : CallbackWait grow sig}
  {rest : List (Activation (core3 grow) (HostState sig))}

private theorem appendRun {first middle last : Config (core3 grow) (HostState sig)} {leading trailing}
    (left : Steps profile ready (specDispatch ready impl) first leading middle)
    (right : Steps profile ready (specDispatch ready impl) middle trailing last) :
    Steps profile ready (specDispatch ready impl) first (leading ++ trailing) last := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem resumeCallback (resume : CallbackResume wait atResume)
    (saved : atResume.cont? wait.thread = some wait.saved) :
    Steps profile ready (specDispatch ready impl) atResume resume.labels resume.resumed := by
  have get := Step.get (prof := profile) (hr := ready) (dispatch := specDispatch ready impl) resume.focused
  cases waiting : atResume.store.threadIs Thread.waiting wait.thread with
  | false =>
    simp [Prog.bind, pure, waiting] at get
    simp only [CallbackResume.labels, CallbackResume.resumed, waiting, Bool.false_eq_true, ite_false]
    exact .cons get (.cons (.resumeThread rfl saved) (.refl _))
  | true =>
    simp [Prog.bind, waiting, Thread.stopWaiting] at get
    simp only [CallbackResume.labels, CallbackResume.resumed, waiting, ite_true]
    exact .cons get (.cons (.modify rfl) (.cons (.resumeThread rfl saved) (.refl _)))

theorem resumeTrackedCallback (resume : CallbackResume wait atResume) {leading}
    (path : ParkedPrefix profile ready (specDispatch ready impl) wait.thread (wait.blocked start rest) leading atResume) :
    Steps profile ready (specDispatch ready impl) (wait.blocked start rest) (leading ++ resume.labels) resume.resumed := by
  obtain ⟨run, kept⟩ := path.reaches
  exact appendRun run (resumeCallback resume (kept.trans (Config.cont?_setCont_self _ _ _)))

theorem resumeCallbackEmpty (resume : CallbackResume wait atResume) {leading}
    (path : ParkedPrefix profile ready (specDispatch ready impl) wait.thread (wait.blocked start rest) leading atResume)
    {set : WsetId} (kind : wait.kind = .wait set)
    {task : Task (core3 grow)} (live : resume.resumed.store.task? wait.taskId = some task)
    (noCancel : task.state ≠ .pendingCancel)
    {record : WaitableSet} (setLive : (wait.decrement resume.resumed.store).wset? set = some record)
    (empty : (wait.decrement resume.resumed.store).wsetHasEvent set = false)
    {permutation : List Nat} (allowed : Allowed profile (.shuffle record.elems.length) permutation) :
    Steps profile ready (specDispatch ready impl) (wait.blocked start rest)
      ((leading ++ resume.labels) ++ [.tau, .tau, .tau, .choice (.shuffle record.elems.length) permutation, .tau, .tau,
        .trap (.internal "WaitableSet.get_pending_event: no pending event")])
      (StepDefs.trapCfg { resume.resumed with store := wait.shuffled resume.resumed.store set record permutation }) :=
  appendRun (resumeTrackedCallback resume path) (callbackWaitEmpty wait kind rfl live noCancel setLive empty allowed)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery
