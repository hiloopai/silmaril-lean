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

variable {start finish : Config (core3 grow) (HostState sig)}

/-- Closed steps preserve their actual configurations under the reference overlay.
An open handler is unchanged when installed, but later requests it issues are classified separately. -/
theorem LiveDispatch.replay {labels} (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : LiveDispatch.UnchangedThrough bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch.replay run closed

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
