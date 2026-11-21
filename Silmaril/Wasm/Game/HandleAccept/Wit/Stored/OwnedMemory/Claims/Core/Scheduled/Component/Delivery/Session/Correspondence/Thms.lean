module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {impl : HostImpl (core3 grow) (HostState sig)}
  {start finish : State grow sig}

theorem _root_.Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.GiveReplies.scheduler_rejoin
    {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route} {value : route.output.Result}
    {reached reference left right : State grow sig}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right) :
    right = HostFrame.replace left right.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.replyRejoin replies

/-- Re-run a classified finite Core and delivery path with a different
journal. Delivery uses the reached event and keeps any consume-then-trap effect. -/
theorem Run.replay_journal_neutral {actions labels} (path : Run profile ready impl start actions labels finish)
    (neutral : ∀ action ∈ actions, JournalNeutralAction action) (other : HostState sig) :
    Run profile ready impl (HostFrame.replace start other) actions labels (HostFrame.replace finish other) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.neutralRun path neutral other

/-- Continue from an actual successful public give reply into the same
classified finite tail. The two hosts stay separate; the rejoin covers saved
threads and scheduler data, not just the currently active Core caller. -/
theorem Run.after_returned_give {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {value : route.output.Result} {reached reference left right : State grow sig} {actions labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference left right)
    (tail : Run profile ready impl left actions labels finish) (neutral : ∀ action ∈ actions, JournalNeutralAction action) :
    Run profile ready impl right actions labels (HostFrame.replace finish right.host) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.afterGive replies tail neutral

/-- Compare a returning public give body and its selected Core/poll/wait/cancel
tail. Both sides retain the reached scheduler and store, with separate
journals. The dispatcher contract applies to the reached give body only. -/
theorem Run.give_then_delivery {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
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
        (HostFrame.replace last reference.host) ∧ PayloadPrefix.visible checked = PayloadPrefix.visible canonical :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.giveThenDelivery
    site value comparison agreement select

/-- This includes finite suspended and trapped prefixes; no final return
or preservation of host writes is required. -/
theorem JournalReplay.of_steps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {labels}
    (path : Steps profile ready dispatch start labels finish) (incoming : HostState sig) :
    JournalReplay profile ready dispatch start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.replayJournal path incoming

theorem JournalReplay.complete_of_reads_agree {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {incoming labels} (path : JournalReplay profile ready dispatch start incoming labels finish)
    (agrees : ReachedReadsAgree (profile := profile) (ready := ready) dispatch start incoming labels finish) :
    ∃ outgoing, Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.completeJournal path agrees

/-- A complete replay is ready for the next paired action with its actual
outgoing host, not the host of the baseline trace. -/
theorem JournalReplay.rejoin_of_reads_agree {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {incoming labels} {checked : State grow sig} (path : JournalReplay profile ready dispatch start incoming labels finish)
    (aligned : finish = HostFrame.replace checked finish.host)
    (agrees : ReachedReadsAgree (profile := profile) (ready := ready) dispatch start incoming labels finish) :
    ∃ reached, Steps profile ready dispatch (HostFrame.replace start incoming) labels reached ∧
      reached = HostFrame.replace checked reached.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.completeRejoin path aligned agrees

theorem ReadFreeThrough.agrees {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {incoming labels}
    (closed : ReadFreeThrough (profile := profile) (ready := ready) dispatch start labels finish) :
    ReachedReadsAgree (profile := profile) (ready := ready) dispatch start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.readFreeAgreement closed

/-- Follow the first give's actual canonical reply through the intervening
Core and delivery actions, then replay the next canonical body with the
reached journal. The checked entry still tests the actual checked writer.
The reference-body cut is separate from dispatch of that checked entry. -/
theorem Run.next_returned_give {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} {left right : State grow sig}
    (aligned : right = HostFrame.replace left right.host)
    (site : PayloadRoot.Site grow sig route) {actions labels entryLabels}
    (between : Run profile ready (ComponentCall.hostWithComponent bindings callees) left actions labels site.start)
    (neutral : ∀ action ∈ actions, JournalNeutralAction action)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    (value : route.output.Result) {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference) :
    let parked := HostFrame.replace site.start right.host
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels canonicalLabels checked baseline,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) left
        (actions ++ [.give route .entered, .give route .returned]) checkedLabels checked ∧
      Steps profile ready dispatch right labels parked ∧
      Steps profile ready dispatch (site.reference site.referenceReply) canonicalLabels baseline ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonicalLabels) ∧
      baseline = HostFrame.replace checked baseline.host ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) parked.host canonicalLabels baseline :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.nextReturnedGive
    aligned site between neutral entry value comparison agreement

/-- Run the reached publication on the other journal. Registration is
checked afresh there, and agreement of the emitted handle (not equality of
writers) gives the same result bytes and pending-event update. -/
theorem Transition.commit_on_journal {target index} (resolve : LinkedResolution start target index) (other : HostState sig)
    {writer : OwnedMemory.Claims.State sig} (registered : other.writer.register resolve.tree = .ok writer)
    (sameHandle : writer.accepted.length = resolve.writer.accepted.length) :
    ∃ reached, Transition profile ready impl (HostFrame.replace start other) (.commit target index) (List.replicate 17 .tau) reached ∧
      reached = HostFrame.replace resolve.committed reached.host ∧ PendingAt reached.store target index ∧
      reached.host = (({ other with writer } : HostState sig).record (.published resolve.ticket writer.accepted.length)).record
        (.returned resolve.ticket writer.accepted.length) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.commitOnJournal
    resolve other registered sameHandle

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
