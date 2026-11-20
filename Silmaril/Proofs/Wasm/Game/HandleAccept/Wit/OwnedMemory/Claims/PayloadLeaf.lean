module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Field)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (Spend)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}
variable {profile : ProfileKind} {ready : HostReady (HostState sig)}
variable {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

private def readPlan (initial : CStore (core3 grow)) (item : Field) (index : Nat) :
    Session grow sig (Except RecordLower.Issue (Option Spend)) :=
  match item with
  | .owner _ => do return liveLeafPlan initial (← hostGet).writer index item
  | .endpoint .. | .context _ => do
    let state ← hostGet
    return liveLeafPlan (← getStore) state.writer index item
  | _ => pure (.ok none)

private def applyPlan : Except RecordLower.Issue (Option Spend) → Session grow sig (Except RecordLower.Issue Unit)
  | .error reason => pure (.error reason)
  | .ok none => pure (.ok ())
  | .ok (some spend) => do
    claims.spend spend
    return .ok ()

private theorem transfer_eq (initial : CStore (core3 grow)) (item : Field) (index : Nat) :
    Effects.transfer (recordClaims (sig := sig)) item index = (readPlan initial item index >>= applyPlan) := by
  cases item with
  | owner receipt =>
    simp only [Effects.transfer, recordClaims, claims, readPlan, liveLeafPlan, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    simp only [Prog.pure_eq, Prog.pure_bind']
    cases prepareOwner state.writer receipt <;> rfl
  | endpoint channel element id =>
    simp only [Effects.transfer, recordClaims, claims, readPlan, liveLeafPlan, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    simp only [Prog.pure_eq, Prog.pure_bind']
    congr 1
    funext store
    cases prepareEndpoint store state.writer channel element id <;> rfl
  | context id =>
    simp only [Effects.transfer, recordClaims, claims, readPlan, liveLeafPlan, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    simp only [Prog.pure_eq, Prog.pure_bind']
    congr 1
    funext store
    by_cases missing : (store.errCtx? id).isNone <;> simp [missing, applyPlan]
  | _ => rfl

private theorem reads (reached : Machine.Config (core3 grow) (HostState sig)) (item : Field) (index : Nat)
    (finish : Except RecordLower.Issue (Option Spend) → Session grow sig (Ret (core3 grow))) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (readPlan reached.store item index >>= finish), segments⟩ :: rest) :
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧ RetainsActiveSlots profile ready dispatch reached labels
      { reached with ctl := ⟨thread, .prog (finish (liveLeafPlan reached.store reached.host.writer index item)),
        segments⟩ :: rest } := by
  cases item with
  | owner => exact ⟨[.tau], by simp, fun depth => .step (.hostGet focused)
      (by rw [transitionEdit, focused]; rfl) (.done _ _)⟩
  | endpoint | context => exact ⟨[.tau, .tau], by simp, fun _ => .step (.hostGet focused)
      (by rw [transitionEdit, focused]; rfl) (.step (.get rfl) rfl (.done _ _))⟩
  | _ =>
    refine ⟨[], by simp, ?_⟩
    change reached.ctl = ⟨thread, .prog (finish (.ok none)), segments⟩ :: rest at focused
    change RetainsActiveSlots profile ready dispatch reached []
      { reached with ctl := ⟨thread, .prog (finish (.ok none)), segments⟩ :: rest }
    rw [← focused]
    cases reached
    exact fun _ => .done _ _

private theorem spends (reached : Machine.Config (core3 grow) (HostState sig)) (spend : Spend)
    (finish : Session grow sig (Ret (core3 grow))) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (claims.spend spend >>= fun _ => finish), segments⟩ :: rest) :
    RetainsActiveSlots profile ready dispatch reached [.tau, .tau]
      { reached with host := { reached.host with writer := spend.apply reached.host.writer }
                     ctl := ⟨thread, .prog finish, segments⟩ :: rest } :=
  fun _ => .step (.hostGet focused) (by rw [transitionEdit, focused]; rfl) (.step (.hostSet rfl) rfl (.done _ _))

theorem leaf_prefix (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (item : Field) (index : Nat) (output : Lower.Output)
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Effects.checkedLeaf recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= finish), segments⟩ :: rest) :
    let canonical := RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
      destination.width item output >>= fun result => finish (.ok result)
    let (postHost, next) := match liveLeafPlan reached.store reached.host.writer index item with
      | .error issue => (reached.host, finish (.error issue))
      | .ok none => (reached.host, canonical)
      | .ok (some spend) => ({ reached.host with writer := spend.apply reached.host.writer }, canonical)
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧ RetainsActiveSlots profile ready dispatch reached labels
      { reached with host := postHost, ctl := ⟨thread, .prog next, segments⟩ :: rest } := by
  let canonical := RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
    destination.width item output >>= fun result => finish (.ok result)
  have leafEq : Effects.canonical Limits.spec Quirks.none (destination.context inst)
      destination.width item output = (RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
        destination.width item output : Session grow sig output.Result) := by cases output <;> rfl
  let afterTransfer : Except RecordLower.Issue Unit → Session grow sig (Except RecordLower.Issue output.Result) :=
    fun outcome => match outcome with
    | .error issue => pure (.error issue)
    | .ok () => do
      let result ← RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
        destination.width item output
      return .ok result
  have onSuccess : afterTransfer (.ok ()) >>= finish = canonical := by
    simp only [afterTransfer, canonical, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
  let next := fun plan => applyPlan plan >>= fun verdict => afterTransfer verdict >>= finish
  have atRead : reached.ctl = ⟨thread, .prog (readPlan reached.store item index >>= next), segments⟩ :: rest := by
    simp only [Effects.checkedLeaf, transfer_eq reached.store, bind_assoc, leafEq, next, afterTransfer] at focused ⊢
    exact focused
  obtain ⟨labels, silent, readSteps⟩ := reads (profile := profile) (ready := ready) (dispatch := dispatch)
    reached item index next atRead
  dsimp only
  cases plan : liveLeafPlan reached.store reached.host.writer index item with
  | error issue => exact ⟨labels, silent, by simpa only [plan, next, applyPlan, afterTransfer, pure_bind] using readSteps⟩
  | ok result =>
    cases result with
    | none => exact ⟨labels, silent, by simpa only [plan, next, applyPlan, pure_bind, onSuccess] using readSteps⟩
    | some spend =>
      let afterRead := { reached with ctl := ⟨thread, .prog (next (.ok (some spend))), segments⟩ :: rest }
      have readDone : RetainsActiveSlots profile ready dispatch reached labels afterRead := by
        simpa only [plan, afterRead] using readSteps
      have spendSteps := spends (profile := profile) (ready := ready) (dispatch := dispatch) afterRead spend canonical
        (thread := thread) (segments := segments) (rest := rest) (by
          simp only [afterRead, next, applyPlan, bind_assoc, pure_bind, onSuccess])
      refine ⟨labels ++ [.tau, .tau], ?_, fun depth => (readDone depth).append (spendSteps depth)⟩
      intro label member
      rcases List.mem_append.mp member with front | back
      · exact silent label front
      · simpa using back

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf
