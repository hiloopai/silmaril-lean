module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

private theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch before leading middle) (back : Steps profile ready dispatch middle trailing after) :
    Steps profile ready dispatch before (leading ++ trailing) after := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem invisible {labels : Trace grow sig} (silent : labels.all (· matches .tau) = true) :
    PayloadPrefix.visible labels = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro label member
  have tau := List.all_eq_true.mp silent label member
  cases label <;> simp_all

private theorem noAssignmentPeer (paired : HostFrame.Related.Paired older start incoming)
    (closed : NoHostAssignment start) : NoHostAssignment incoming := by
  intro thread value next frames rest focused
  change ReturnFrame.Related.Paired older (HostFrame.replace start incoming.host) incoming at paired
  generalize incoming.host = observer at paired
  cases paired with
  | @mk active _ control _ =>
    change List.Forall₂ (ReturnFrame.Related.Active older) start.ctl _ at control
    change active = _ at focused
    rw [focused] at control
    generalize leftFocus : start.ctl = leftControl at control
    cases control with
    | cons head _ =>
      cases head
      exact closed _ _ _ _ _ leftFocus

private theorem stepHost {other : Config (core3 grow) (HostState sig)} {label}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (closed : NoHostAssignment start) (step : Step profile ready dispatch start label other) : other.host = start.host := by
  cases step <;> try rfl
  case hostDone => unfold StepDefs.hostFinish; split <;> rfl
  case hostSet focused => exact (closed _ _ _ _ _ focused).elim
  case emit => rename_i observation _ _ _ _; cases observation <;> rfl

theorem coreInternal {protectedReturn thread core next frames rest store coreNext}
    (focused : start.ctl = ⟨thread, .core core next, frames⟩ :: rest)
    (running : (core3 grow).status start.store.core core = .running ∨ (core3 grow).status start.store.core core = .stuck)
    (executed : (core3 grow).Internal (start.store.core, core) (store, coreNext))
    (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn
      { start with store := { start.store with core := store }, ctl := ⟨thread, .core coreNext next, frames⟩ :: rest } seen finish) :
    ClosedCallbackPrefix bindings profile ready base protectedReturn start (.core :: seen) finish := by
  refine .step ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_ (.coreInternal focused running executed) tail
  · intros; simp [focused]
  · intros; simp [focused]
  · intro _ _ _ _ _ other
    rw [focused] at other
    cases other
  · intro _ _ _ _ _ _ _ other calling
    rw [focused] at other
    cases other
    rcases running with status | status <;> rw [status] at calling <;> contradiction
  · intro _ _ _ _ _; simp [focused]
  · simp [CoreUpdateGrows, focused]

theorem replay {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready base) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels reached ∧
      HostFrame.Related.Paired older finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted := by
  induction path generalizing incoming with
  | done => exact ⟨[], [], incoming, .refl _, .refl _, paired, rfl, rfl, .refl _, rfl, rfl⟩
  | @step current next last label rest interior unchanged noAssignment grows run _ ih =>
    have live : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) current label next := by
      rcases LiveDispatch.classify_step (bindings := bindings) run with live | install
      · exact live
      · cases install with
        | direct focused overlaid => exact (overlaid (unchanged.direct focused)).elim
        | core focused calling overlaid => exact (overlaid (unchanged.core focused calling)).elim
    obtain ⟨peer, replay, aligned⟩ := HostFrame.Related.interior_step covers paired interior grows live
    have peerStep : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming label peer := by
      cases replay with
      | cons _ step tail => cases tail; exact step
    obtain ⟨checkedLabels, canonLabels, reached, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots⟩ := ih aligned
    exact ⟨_, _, reached, .cons run checked, .cons peerStep canonical, final,
      (List.filter_append [_] checkedLabels).trans (congrArg (_ ++ ·) checkSeen),
      (List.filter_append [_] canonLabels).trans (congrArg (_ ++ ·) canonSeen),
      (CoreGrowthSteps.cons grows run (.refl _)).grows.trans growth,
      checkRoots.trans (congrArg (·.writer.accepted) (stepHost noAssignment run)),
      canonRoots.trans (congrArg (·.writer.accepted) (stepHost (noAssignmentPeer paired noAssignment) peerStep))⟩
  | confinedGive callout _ ih =>
    obtain ⟨count, checked, _, _⟩ := Plain.parked_closed_give_steps bindings callout.name callout.type callout.args
      callout.inst callout.destination callout.schema _ callout.thread profile ready callout.parked callout.calling
      callout.linked callout.caller callout.live callout.closed base embedder
    obtain ⟨leading, peer, silent, canonical, aligned, host⟩ :=
      LiveDispatch.closed_give_paired (profile := profile) (ready := ready) (base := base) callout paired
    obtain ⟨checkLabels, canonLabels, reached, checkTail, canonTail, final, checkSeen, canonSeen, growth, checkRoots, canonRoots⟩ := ih aligned
    have tau : (List.replicate count (.tau : Label (core3 grow) (HostState sig))).all (· matches .tau) = true := by
      apply List.all_eq_true.mpr
      intro label member
      rw [List.eq_of_mem_replicate member]
    exact ⟨_, _, reached, append checked.steps checkTail, append canonical canonTail, final,
      (List.filter_append _ checkLabels).trans (by rw [← PayloadPrefix.visible, invisible tau, List.nil_append]; exact checkSeen),
      (List.filter_append _ canonLabels).trans (by rw [← PayloadPrefix.visible, invisible silent, List.nil_append]; exact canonSeen),
      growth, checkRoots, canonRoots.trans (congrArg (·.writer.accepted) host)⟩
  | @syncReady current _ _ task inst thread frames rest focused agrees _ ih =>
    let residual := syncLiftCandidates (E := core3 grow) (σ := HostState sig) task
      (current.store.instCandidates (ready current.host) inst)
    obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focused (.prog residual) current.host incoming.host
    have candidates := HostFrame.instCandidates_eq current.store inst (ready current.host) (ready incoming.host)
      (fun entry live blockedThread member suspended found blocked query condition =>
        agrees entry live blockedThread member suspended found blocked query condition incoming.host)
    have peerStep : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := ⟨thread, .prog residual, peerFrames⟩ :: peerRest } := by
      unfold residual
      rw [candidates]
      exact .hostGet atPeer
    obtain ⟨_, _, reached, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots⟩ := ih aligned
    exact ⟨_, _, reached, .cons (.hostGet focused) checked, .cons peerStep canonical, final,
      checkSeen, canonSeen, growth, checkRoots, canonRoots⟩

theorem stringReallocPrefix (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (path : ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = PayloadPrefix.stringPlanResume cx steps checkNext)
      (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check) seen finish) :
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready base) start (.tau :: checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (.tau :: canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older (PayloadPrefix.stringPlanResume cx steps checkNext)
        (PayloadPrefix.stringPlanResume cx steps canonNext)) finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted := by
  obtain ⟨_, _, paired⟩ := frame.string_realloc_pair (profile := profile) (ready := ready) (bindings := bindings)
    cx ptr oldSize alignment size steps checkNext canonNext checkAt canonAt
  obtain ⟨checkedLabels, canonLabels, reached, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots⟩ :=
    replay path embedder (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) paired
  have enterLeft := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    cx ptr oldSize alignment size steps checkNext start check checkAt
  have enterRight := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size steps canonNext incoming canon canonAt
  exact ⟨checkedLabels, canonLabels, reached, .cons enterLeft checked, .cons enterRight canonical, final,
    checkSeen, canonSeen, growth, checkRoots, canonRoots⟩

theorem collectionPrefix (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout destination.width element
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first) seen finish →
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready base) start ([.tau, .tau, .tau] ++ checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming ([.tau, .tau] ++ canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted := by
  intro area first second path
  obtain ⟨_, _, paired⟩ := frame.collection_install_pair (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext width prepared checkAt canonAt
  have atCallback : HostFrame.Related.Paired (ReturnFrame.Extend older first second)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        incoming canon second) := paired
  obtain ⟨checkedLabels, canonLabels, reached, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots⟩ :=
    replay path embedder (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) atCallback
  have enterLeft := (PayloadPrefix.collection_install_steps (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    destination inst type element entries output index start incoming check canon checkNext canonNext width prepared checkAt canonAt).1
  have enterRight := (PayloadPrefix.collection_install_steps (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) destination inst type element entries output index
    start incoming check canon checkNext canonNext width prepared checkAt canonAt).2
  exact ⟨checkedLabels, canonLabels, reached, append enterLeft checked, append enterRight canonical, final,
    checkSeen, canonSeen, growth, checkRoots, canonRoots⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
