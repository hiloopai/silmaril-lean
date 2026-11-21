module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open PayloadRoot ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {bindings : List (Binding sig)}

/-- The give overlay does not replace the program installed at an on-cancel
request. The installed program can still consult the reached host later. -/
theorem LiveDispatch.cancel_dispatch (callback : CancelRef) :
    specDispatch ready base (.onCancel callback) = specDispatch ready (LiveDispatch.host bindings base) (.onCancel callback) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.dispatchUnchanged trivial

/-- Each reached call uses the same dynamic dispatcher, but selects the root from
its own live journal. The selected-site replacement and its exclusion of later
matching requests are not needed for this entry. This does not assert that the
body returns, or that a callback preserves the root's live transfer authority. -/
theorem LiveDispatch.entry (site : Site grow sig route) (linked : site.Linked bindings) (other : HostState sig)
    (selected : Stored.Endpoints.Core.childFromHistory other.writer.accepted site.handle = some site.tree) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace site.start other)
        labels (HostFrame.replace (site.reference site.referenceReply) other) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.entry site linked other selected

/-- Enter a new give at a reached paired Core request. The live reference
caller selects its current root, and both active and blocked older frame
substitutions survive installation of the canonical body. -/
theorem LiveDispatch.entry_paired (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree) :
    ∃ labels entered,
      labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      HostFrame.Related.Paired older (site.reference site.referenceReply) entered :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedEntry site linked paired selected

/-- Compose live nested entry, a reached canonical body and its actual
caller rejoin. A divergent host read or pop of an older substituted frame
is reported at that step rather than being replayed as the remaining body. -/
theorem LiveDispatch.nested_return (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other checked baseline : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree)
    {value : route.output.Result} {reached reference : Config (core3 grow) (HostState sig)} {labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
    (body : CoreGrowthSteps profile ready (specDispatch ready base) (site.reference site.referenceReply) labels baseline)
    (closed : LiveDispatch.UnchangedThrough bindings profile ready base (site.reference site.referenceReply) labels baseline) :
    let dispatch := specDispatch ready (LiveDispatch.host bindings base)
    ∃ installed entered, installed.all (· matches .tau) = true ∧ Steps profile ready dispatch other installed entered ∧
      LiveDispatch.NestedReplay profile ready dispatch older (site.reference site.referenceReply) entered labels checked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.nestedReturn
    site linked paired selected replies body closed

variable {start finish : Config (core3 grow) (HostState sig)}

/-- Discover the actual nested installation in a finite growth-certified run.
No blanket exclusion of nested gives is needed. The live replay stops before
dispatching the give, or at an earlier divergent read or substituted return. -/
theorem LiveDispatch.paired_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {incoming : Config (core3 grow) (HostState sig)} {labels}
    (paired : HostFrame.Related.Paired older start incoming)
    (run : CoreGrowthSteps profile ready (specDispatch ready base) start labels finish) :
    LiveDispatch.PairedReplay bindings profile ready base older start incoming labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.pairedReplay paired run

theorem LiveDispatch.GiveInstall.step {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {label}
    (install : LiveDispatch.GiveInstall bindings dispatch start label finish) :
    Step profile ready dispatch start label finish := by
  cases install with
  | direct focused _ => exact .call focused
  | core focused calling _ => exact .coreCallout focused calling

/-- Enter on the live root and compare the reached prefix of the nested body,
even if it has not returned or executes another public give. Further requests
are exposed at their real caller and with all older frames still paired. -/
theorem LiveDispatch.nested_prefix (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {incoming : Config (core3 grow) (HostState sig)} {labels}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (body : CoreGrowthSteps profile ready (specDispatch ready base) (site.reference site.referenceReply) labels finish) :
    ∃ installed entered, installed.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming installed entered ∧
      LiveDispatch.PairedReplay bindings profile ready base older (site.reference site.referenceReply) entered labels finish := by
  obtain ⟨installed, entered, silent, entry, aligned⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
  exact ⟨installed, entered, silent, entry, LiveDispatch.paired_replay aligned body⟩

/-- Closed steps preserve their actual configurations under the reference overlay.
An open handler is unchanged when installed, but later requests it issues are classified separately. -/
theorem LiveDispatch.replay {labels} (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : LiveDispatch.UnchangedThrough bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.replay run closed

/-- A classified interleaving runs under the live give overlay with the
same steps against its reached store and journal. -/
theorem LiveDispatch.interleaving_steps {actions labels incoming outgoing}
    (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base))
      (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.interleavingSteps between

/-- The classified Core, delivery, publication and tick transitions do not install
an embedder body. Their dispatcher compatibility follows from their constructors,
not a premise that the two finished runs agree. The reached readiness and root
selection witnesses are still required where these transitions read the host. -/
theorem LiveDispatch.entry_after_interleaving (site : Site grow sig route) (linked : site.Linked bindings)
    {incoming outgoing : HostState sig}
    (selected : Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted site.handle = some site.tree)
    {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.afterInterleaving
    site linked selected prior between

/-- The same starting observations give the same selected root after a classified
interleaving. Each commit registers on the live journal; no equality or retention
of held claims, lenders, event slots, or guest bytes is needed. -/
theorem LiveDispatch.entry_after_equal_roots (site : Site grow sig route) (linked : site.Linked bindings)
    {incoming outgoing : HostState sig} (roots : incoming.writer.accepted = finish.host.writer.accepted)
    {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.afterSameRoots
    site linked roots prior between

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
