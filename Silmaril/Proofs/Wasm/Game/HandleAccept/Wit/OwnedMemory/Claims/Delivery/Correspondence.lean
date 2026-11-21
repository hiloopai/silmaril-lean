module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall.Delivery ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start finish : State grow sig}

private def pollOnHost {target : SubtaskId} (poll : ParkedPoll start target profile) (other : HostState sig) :
    ParkedPoll (HostFrame.replace start other) target profile :=
  { poll with toPollAdmission := { poll.toPollAdmission with focused := poll.focused } }

private def waitOnHost (wait : ParkedWait start) (other : HostState sig) : ParkedWait (HostFrame.replace start other) :=
  { wait with focused := wait.focused }

private def cancelOnHost {target : SubtaskId} (cancel : ParkedCancel start target) (other : HostState sig) :
    ParkedCancel (HostFrame.replace start other) target :=
  { cancel with focused := cancel.focused }

private def cancelResumeOnHost {initial atResume : State grow sig} {target : SubtaskId}
    {cancel : ParkedCancel initial target} (resume : SyncCancelResume cancel atResume) (other : HostState sig) :
    SyncCancelResume cancel (HostFrame.replace atResume other) :=
  { resume with focused := resume.focused }

theorem neutralStep {action labels} (edge : Transition profile ready impl start action labels finish)
    (neutral : JournalNeutralAction action) (other : HostState sig) :
    Transition profile ready impl (HostFrame.replace start other) action labels (HostFrame.replace finish other) := by
  cases edge <;> try contradiction
  case coreInternal focused running steps => exact .coreInternal focused running steps
  case coreReturned focused returned => exact .coreReturned focused returned
  case coreTrap focused trapped => exact .coreTrap focused trapped
  case poll poll pending branch =>
    cases branch with
    | unaligned bad => exact .poll (pollOnHost poll other) pending (.unaligned bad)
    | outside aligned sized bad => exact .poll (pollOnHost poll other) pending (.outside aligned sized bad)
    | inside aligned sized fits => exact .poll (pollOnHost poll other) pending (.inside aligned sized fits)
  case waitBlock wait empty => exact .waitBlock (waitOnHost wait other) empty
  case waitReady early allowed wait available =>
    cases early
    · exact .waitReady (waitOnHost wait other) available false allowed
    · exact .waitReady (waitOnHost wait other) available true allowed
  case waitResume resume saved =>
    exact .waitResume (start := HostFrame.replace _ other) { resume with focused := resume.focused } saved
  case waitTake delivery focused pending branch =>
    cases branch with
    | unaligned bad =>
      exact .waitTake (start := HostFrame.replace _ other) { delivery with setLive := delivery.setLive } focused pending (.unaligned bad)
    | outside aligned sized bad =>
      exact .waitTake (start := HostFrame.replace _ other) { delivery with setLive := delivery.setLive } focused pending (.outside aligned sized bad)
    | inside aligned sized fits =>
      exact .waitTake (start := HostFrame.replace _ other) { delivery with setLive := delivery.setLive } focused pending (.inside aligned sized fits)
  case cancelReturned cancel pending available => exact .cancelReturned (cancelOnHost cancel other) pending available
  case cancelReply cancel record cancelled pending focused live =>
    exact .cancelReply cancel record focused live cancelled pending
  case cancelPark wait => exact .cancelPark (start := HostFrame.replace _ other) { wait with focused := wait.focused }
  case cancelResume resume saved => exact .cancelResume (cancelResumeOnHost resume other) saved
  case cancelTake resume pending => exact .cancelTake (cancelResumeOnHost resume other) pending

theorem neutralRun {actions labels} (path : Run profile ready impl start actions labels finish)
    (neutral : ∀ action ∈ actions, JournalNeutralAction action) (other : HostState sig) :
    Run profile ready impl (HostFrame.replace start other) actions labels (HostFrame.replace finish other) := by
  induction path with
  | stop _ => exact .stop _
  | next edge _ ih => exact .next (neutralStep edge (neutral _ (.head _)) other) (ih fun _ present => neutral _ (.tail _ present))

private theorem equalLists {Elem : Type} {relation : Elem → Elem → Prop} {left right : List Elem}
    (equal : ∀ {lhs rhs}, relation lhs rhs → lhs = rhs) (related : List.Forall₂ relation left right) : left = right := by
  induction related with
  | nil => rfl
  | cons head _ ih => rw [equal head, ih]

private theorem sameActive {left right : Activation (core3 grow) (HostState sig)}
    (related : ReturnFrame.Related.Active (fun _ _ => False) left right) : left = right := by
  cases related with
  | mk frames =>
    have same := equalLists (fun segment => by cases segment with
      | same => rfl
      | swap impossible => exact False.elim impossible) frames
    cases same
    rfl

private theorem sameSaved {left right : Option (Activation (core3 grow) (HostState sig))}
    (related : ReturnFrame.Related.Saved (fun _ _ => False) left right) : left = right := by
  cases related with
  | none => rfl
  | some active => exact congrArg some (sameActive active)

private theorem sameMachine {left right : State grow sig}
    (related : ReturnFrame.Related.Paired (fun _ _ => False) left right) : right = left := by
  cases related with
  | mk active blocked =>
    have activeEq := equalLists (fun related => sameActive related) active
    have savedEq := equalLists (fun related => sameSaved related) blocked
    cases left
    dsimp only at activeEq savedEq ⊢
    subst_vars
    rfl

theorem afterGive {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route} {value : route.output.Result}
    {reached reference left right : State grow sig} {actions labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right)
    (tail : Run profile ready impl left actions labels finish) (neutral : ∀ action ∈ actions, JournalNeutralAction action) :
    Run profile ready impl right actions labels (HostFrame.replace finish right.host) := by
  have aligned := sameMachine replies.2.2.2.2.2
  exact aligned ▸ neutralRun tail neutral right.host

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : State grow sig} {leading trailing : Trace grow sig}
    (first : Steps profile ready dispatch start leading middle) (tail : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction first with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem giveThenDelivery {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (value : route.output.Result)
    {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference)
    (select : ∀ left right, LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right →
      ∃ actions labels last, Run profile ready (ComponentCall.hostWithComponent bindings callees) left actions labels last ∧
        ∀ action ∈ actions, JournalNeutralAction action) :
    ∃ actions checked canonical last,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) site.checked (.give route .returned :: actions) checked last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) (site.reference site.referenceReply) canonical
        (HostFrame.replace last reference.host) ∧ PayloadPrefix.visible checked = PayloadPrefix.visible canonical := by
  obtain ⟨checkLabels, canonLabels, left, right, checkRun, canonRun, seen, replies⟩ :=
    Transition.give_returned site value comparison agreement
  obtain ⟨actions, labels, last, tail, neutral⟩ := select left right replies
  have canonical := (afterGive replies tail neutral).steps
  rw [show right.host = reference.host from replies.2.2.2.2.1] at canonical
  refine ⟨_, _, _, last, .next checkRun tail, appendSteps canonRun canonical, ?_⟩
  unfold PayloadPrefix.visible at seen ⊢
  simp only [List.filter_append, List.filter_cons, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil, seen]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence
