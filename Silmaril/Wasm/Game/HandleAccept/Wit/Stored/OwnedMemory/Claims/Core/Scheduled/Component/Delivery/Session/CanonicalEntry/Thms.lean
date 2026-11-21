module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.CanonicalEntry.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish : Config (core3 grow) (HostState sig)}

/-- The actual Core callout and canonical caller/store reads install the
reference body at the original activation, under the reached canonical host. -/
theorem Site.reference_entry (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace site.start other)
      [.tau, .tau, .tau] (HostFrame.replace (site.reference site.referenceReply) other) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.entered site linked other

theorem Site.replay_under_reference_host (site : Site grow sig route) {labels}
    (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : site.NoEntryThrough profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.replay site run closed

/-- If replay reaches another matching request, keep the exact common
prefix up to that request. No substitute trap or reply is taken there. -/
theorem Site.replay_until_request (site : Site grow sig route) {labels}
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start labels finish ∨
      ∃ leading label trailing reached, labels = leading ++ label :: trailing ∧
        Steps profile ready (specDispatch ready base) start leading reached ∧
        Steps profile ready (specDispatch ready (site.referenceHost base)) start leading reached ∧
        Steps profile ready (specDispatch ready base) reached (label :: trailing) finish ∧ ¬ site.NoEntryAt reached :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.replayOrRequest site run

/-- Ordinary Core steps do not consult the replacement. Their resulting
store, including guest byte writes, is the actual reached store. -/
theorem Site.replay_guest_steps (site : Site grow sig route) {count : Nat}
    (run : Steps profile ready (specDispatch ready base) start (List.replicate count .core) finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start (List.replicate count .core) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.replayCore site run

/-- The entry and body now use one fixed canonical dispatcher. The body can
be a finite suspended, trapped, or returning prefix; this adds no liveness. -/
theorem Site.reference_call (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) {labels}
    (body : Steps profile ready (specDispatch ready base) (HostFrame.replace (site.reference site.referenceReply) other) labels finish)
    (closed : site.NoEntryThrough profile ready base (HostFrame.replace (site.reference site.referenceReply) other) labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace site.start other)
      (.tau :: .tau :: .tau :: labels) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.execute site linked other body closed

/-- A finite preceding path, the actual Core entry, and the canonical
give body can share the same fixed dispatcher. Only reached replacement
requests delimit this comparison. -/
theorem Site.reference_call_after (site : Site grow sig route) {bindings : List (Binding sig)} (linked : site.Linked bindings)
    (other : HostState sig) {leading labels}
    (prior : Steps profile ready (specDispatch ready base) start leading (HostFrame.replace site.start other))
    (priorClosed : site.NoEntryThrough profile ready base start leading (HostFrame.replace site.start other))
    (body : Steps profile ready (specDispatch ready base) (HostFrame.replace (site.reference site.referenceReply) other) labels finish)
    (bodyClosed : site.NoEntryThrough profile ready base (HostFrame.replace (site.reference site.referenceReply) other) labels finish) :
    Steps profile ready (specDispatch ready (site.referenceHost base)) start (leading ++ .tau :: .tau :: .tau :: labels) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.executeAfter
    site linked other prior priorClosed body bodyClosed

/-- Carry the interleaving's actual outgoing journal through the selected
reference call. This concatenates real machine steps, including the entry,
rather than presenting two paths separated by an unexecuted cut. -/
theorem Site.reference_call_after_interleaving (site : Site grow sig route) {bindings : List (Binding sig)}
    (linked : site.Linked bindings) {incoming outgoing actions leading labels}
    (between : JournalInterleaving profile ready base start incoming actions leading site.start outgoing)
    (journal : JournalReplay profile ready (specDispatch ready base) (site.reference site.referenceReply) outgoing labels finish)
    (reads : ReachedReadsAgree (profile := profile) (ready := ready) (specDispatch ready base)
      (site.reference site.referenceReply) outgoing labels finish)
    (priorClosed : site.NoEntryThrough profile ready base (HostFrame.replace start incoming) leading
      (HostFrame.replace site.start outgoing))
    (bodyClosed : ∀ {after}, Steps profile ready (specDispatch ready base)
      (HostFrame.replace (site.reference site.referenceReply) outgoing) labels (HostFrame.replace finish after) →
      site.NoEntryThrough profile ready base (HostFrame.replace (site.reference site.referenceReply) outgoing) labels
        (HostFrame.replace finish after)) :
    ∃ after, Steps profile ready (specDispatch ready (site.referenceHost base)) (HostFrame.replace start incoming)
      (leading ++ .tau :: .tau :: .tau :: labels) (HostFrame.replace finish after) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CanonicalEntry.executeInterleaved
    site linked between journal reads priorClosed bodyClosed

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot
