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

/-- Commit at the reached caller and result cursor while older continuations
remain paired. The live journal registers afresh; no earlier event or transfer
authority is assumed to survive. -/
theorem Transition.commit_paired {target index} (resolve : LinkedResolution start target index) {other : State grow sig}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} (paired : HostFrame.Related.Paired older start other)
    {writer : OwnedMemory.Claims.State sig} (registered : other.host.writer.register resolve.tree = .ok writer)
    (sameHandle : writer.accepted.length = resolve.writer.accepted.length) :
    ∃ reached, Transition profile ready impl other (.commit target index) (List.replicate 17 .tau) reached ∧
      HostFrame.Related.Paired older resolve.committed reached ∧ PendingAt reached.store target index ∧
      reached.host = (({ other.host with writer } : HostState sig).record (.published resolve.ticket writer.accepted.length)).record
        (.returned resolve.ticket writer.accepted.length) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.commitPaired
    resolve paired registered sameHandle

/-- Re-select and consume the reached event with older return frames paired.
Both buffer traps retain the consumed event and lock down the delivered store. -/
theorem Transition.poll_paired {target index result suffix} (poll : ParkedPoll start target profile)
    (pending : PendingAt start.store target index)
    (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.poll target index result) (pollLabels poll ++ suffix) reached ∧
      HostFrame.Related.Paired older
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] }) reached ∧
      reached.host = other.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.pollPaired poll pending branch paired

/-- Compare a wait at the actual reached selection, not its historical
admission. Rejoin the saved Core caller or retain the consumed event on trap. -/
theorem Transition.wait_take_paired {initial : State grow sig} {wait : ParkedWait initial} {target index result suffix}
    (delivery : WaitDelivery wait start profile target)
    (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
    (pending : PendingAt start.store target index)
    (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.wait target index result) (delivery.labels ++ suffix) reached ∧
      HostFrame.Related.Paired older
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] }) reached ∧
      reached.host = other.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.waitTakePaired
    delivery focused pending branch paired

/-- Deliver a returned event through cancel, without invoking an open cancel hook. -/
theorem Transition.cancel_returned_paired {target index} (cancel : ParkedCancel start target)
    (pending : PendingAt start.store target index) (available : CancelAvailable start.store target)
    {other : State grow sig} {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    ∃ reached, Transition profile ready impl other (.cancel target .returned) (List.replicate 15 .tau) reached ∧
      HostFrame.Related.Paired older cancel.resumed reached ∧ reached.host = other.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.cancelReturnedPaired
    cancel pending available paired

/-- Replay the actual selected candidate, not an arbitrary runnable
thread. No host-read premise is needed for store-only ready conditions. -/
theorem Transition.tick_on_journal {thread} (tick : SelectedTick thread start ready profile) (other : HostState sig)
    (agrees : TickReadsAgree ready start other) :
    Transition profile ready impl (HostFrame.replace start other) (.tick thread) tick.selectionLabels
      (HostFrame.replace tick.atResume other) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.tickOnJournal tick other agrees

/-- Closed waiting conditions cannot observe a changed journal. -/
theorem TickReadsAgree.of_closed {other : HostState sig}
    (closed : let entered := StepDefs.enterHostSt start.store
      ∀ thread ∈ entered.waiting, ∀ entry, entered.thread? thread = some entry → entry.blocked = true →
        ∀ query, entry.readyCond ≠ some (.host query)) : TickReadsAgree ready start other :=
  fun thread member entry live blocked query condition => (closed thread member entry live blocked query condition).elim

/-- Both projections are actual classified runs. In particular, a
delivery step inspects the event at that step, not at the initial commit. -/
theorem JournalInterleaving.runs {actions labels incoming outgoing}
    (path : JournalInterleaving profile ready impl start incoming actions labels finish outgoing) :
    Run profile ready impl start actions labels finish ∧
      Run profile ready impl (HostFrame.replace start incoming) actions labels (HostFrame.replace finish outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.interleavingRuns path

theorem JournalInterleaving.append {middle : State grow sig} {incoming middleHost outgoing first rest leading trailing}
    (firstPath : JournalInterleaving profile ready impl start incoming first leading middle middleHost)
    (restPath : JournalInterleaving profile ready impl middle middleHost rest trailing finish outgoing) :
    JournalInterleaving profile ready impl start incoming (first ++ rest) (leading ++ trailing) finish outgoing :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.interleavingAppend firstPath restPath

theorem JournalInterleaving.of_neutral_run {actions labels} (run : Run profile ready impl start actions labels finish)
    (closed : ∀ action ∈ actions, JournalNeutralAction action) (other : HostState sig) :
    JournalInterleaving profile ready impl start other actions labels finish other :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.ofNeutralRun run closed other

/-- Complete and exit the reached stackful worker. Unregistration and its
exclusive-mode update use the live task and thread record, without reading
the two journals or requiring an earlier event to remain pending. -/
theorem JournalInterleaving.finish_stackful {reached : State grow sig} {site : StackfulReturn reached}
    {incoming outgoing actions labels} (run : JournalInterleaving profile ready impl start incoming actions labels reached outgoing)
    (exit : StackfulExit site) (empty : site.segments = []) :
    JournalInterleaving profile ready impl start incoming (actions ++ [.stackfulComplete site.taskId, .workerExit site.thread])
      (labels ++ (exit.labels ++ [.tau])) exit.finished outgoing :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.stackfulCompletion run exit empty

/-- The next returning give starts from the journals reached after any
finite classified interleaving. An observation mismatch stops at its
actual host read; it is not a checked refusal or a canonical trap. -/
theorem JournalInterleaving.next_returned_give {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) {actions labels incoming outgoing entryLabels}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels site.start outgoing)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    (value : route.output.Result) {reached reference : State grow sig}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference)
    (agreement : GiveBodyAgreement profile ready bindings callees site reached reference) :
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels canonicalLabels checked baseline,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route .returned]) checkedLabels checked ∧
      Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace site.start outgoing) ∧
      Steps profile ready dispatch (site.reference site.referenceReply) canonicalLabels baseline ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonicalLabels) ∧
      baseline = HostFrame.replace checked baseline.host ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) outgoing canonicalLabels baseline :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.interleavedGive
    site between entry value comparison agreement

/-- A typed guard refusal ends at the reached canonical prefix, without
a canonical refusal reply. A trap keeps the actual canonical trap label
and store effects. A journal mismatch is a separate reached boundary. -/
theorem JournalInterleaving.next_stopped_give {bindings : List (Binding sig)} {callees : List (ComponentCall.Callee sig)}
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {actions labels incoming outgoing entryLabels phase checkLabels canonLabels reached reference}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels site.start outgoing)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.start (.give route .entered)
      entryLabels site.checked)
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (stop : GiveStop site check phase canonLabels reached reference) (sameStore : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (checked : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (canonical : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (agreement : GiveCutDispatch profile ready bindings callees site) :
    let dispatch := Dispatch.linked ready bindings callees
    ∃ checkedLabels,
      Run profile ready (ComponentCall.hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route phase]) checkedLabels reached ∧
      Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace site.start outgoing) ∧
      Steps profile ready dispatch (site.reference site.referenceReply) canonLabels reference ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonLabels) ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) outgoing canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.interleavedStop
    site between entry stop sameStore seen checked canonical agreement

/-- Follow the actual allocator occurrence through a finite body prefix.
A saved mark still denotes a suspended call, not an allocator return. -/
theorem JournalInterleaving.next_allocator_prefix {route : GiveEffectRoute} {bindings : List (Binding sig)}
    {callees : List (Callee sig)} (site : PayloadRoot.Site grow sig route)
    {actions labels incoming outgoing entryLabels}
    (between : JournalInterleaving profile ready (hostWithComponent bindings callees) start incoming actions labels site.start outgoing)
    (entry : Transition profile ready (hostWithComponent bindings callees) site.start (.give route .entered) entryLabels site.checked)
    {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : State grow sig}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark)
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right)
    (checked : Dispatch.Compatible profile ready bindings callees left checkLabels reached)
    (canonical : Dispatch.Compatible profile ready bindings callees right canonLabels reference) :
    let dispatch := Dispatch.linked ready bindings callees
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    ∃ checkedLabels,
      Run profile ready (hostWithComponent bindings callees) start
        (actions ++ [.give route .entered, .give route (.allocatorPrefix mark)]) checkedLabels reached ∧
      Steps profile ready dispatch (HostFrame.replace start incoming) labels (HostFrame.replace site.start outgoing) ∧
      PayloadPrefix.visible checkedLabels = PayloadPrefix.visible (labels ++ canonTrace) ∧
      JournalReplay profile ready dispatch (site.reference site.referenceReply) outgoing canonTrace reference :=
  let compared := cut.session checkEntry canonEntry seenEntry checkInstall canonInstall checked canonical
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.Correspondence.interleavedCut
    site between entry compared.1 compared.2.1 compared.2.2

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
