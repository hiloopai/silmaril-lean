module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Stored.Endpoints.RecordLower
open PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Both linked give bindings use the very field described by the compiler
certificate. This is a static fact, not a promise about live claims. -/
theorem Site.Linked.emitted {site : Site grow sig route} (linked : site.Linked bindings) : site.field.Emitted := by
  obtain ⟨plan, compiled⟩ := linked.compiled
  exact Record.preflightValue_emitted _ _ _ _ _ plan compiled

/-- Either public give reaches a typed refusal, traps at the ABI placement
guard, or enters the compiled effect body with the real reply continuation. -/
theorem Site.parked (site : Site grow sig route) (linked : site.Linked bindings) : Cut site profile ready bindings :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.parked site linked

/-- Extend the actual refused branch of a parked give through its checked
completion. This records the typed error and resumes the original Core
frame. There is no corresponding canonical return for this branch. -/
theorem Site.refusal_resumes (site : Site grow sig route) (issue : Stored.Endpoints.RecordLower.Issue) {labels}
    {impl : HostImpl (core3 grow) (HostState sig)}
    (run : Steps profile ready (specDispatch ready impl) site.start labels
      (site.withBody (site.reply (.error issue)))) :
    let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
    let reached := site.withBody (site.reply (.error issue))
    Steps profile ready (specDispatch ready impl) site.start (labels ++ [.tau, .tau, .tau])
      { reached with host := reached.host.record reply.1
                     ctl := ⟨site.thread, .core ((core3 grow).resume reached.store.core site.core (.values reply.2))
                       site.resume, site.frames⟩ :: site.rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.refusalResumes site issue run

/-- A finite prefix that tracks the original Core occurrence back to the
top identifies the actual caller about to receive a reply, even if other
instances of the same frame were installed during reentry. -/
theorem Site.reached_caller (site : Site grow sig route) {reached : Config (core3 grow) (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {labels} {cursor : Cursor (E := core3 grow) (HostState sig)} {body} (control : reached.ctl = cursor.control body)
    (run : ReturnFrame.Occurrence.Prefix profile ready dispatch
      site.checked (.active 0 0) labels reached (.active 0 0)) :
    ∃ segments, cursor.frames = .core site.core site.resume :: segments :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.reachedCaller site control run

/-- Use the actual public allocation guard only on the placed branch.
The refusal and placement-trap branches never require a body comparison. -/
theorem Site.parked_after_fit (site : Site grow sig route) (linked : site.Linked bindings) (body : Prop)
    (afterFit : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
      site.payload.val.value = true → body)
    (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) : Cut site profile ready bindings body impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.parkedAfterAdmission site linked body
    (fun fits _ _ => afterFit fits) impl embedder

/-- Use both public guards only on the branch that enters the actual body. -/
theorem Site.parked_after_placement (site : Site grow sig route) (linked : site.Linked bindings) (body : Prop)
    (afterPlacement : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
      site.payload.val.value = true →
      rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok () → body)
    (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) : Cut site profile ready bindings body impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.parkedAfterAdmission site linked body
    (fun fits placed _ => afterPlacement fits placed) impl embedder

/-- The placed branch exposes the successful live dry run with the actual
fit and placement checks. The fact authorizes no later transfer by itself. -/
theorem Site.parked_after_admission (site : Site grow sig route) (linked : site.Linked bindings) (body : Prop)
    (afterAdmission : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
      site.payload.val.value = true →
      rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok () →
      Record.prepare site.start.store site.start.host.writer site.field.objects = .ok () → body)
    (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    Cut site profile ready bindings body impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.parkedAfterAdmission site linked body afterAdmission impl embedder

theorem Site.reference_at (site : Site grow sig route) (linked : site.Linked bindings) (next : site.ReferenceNext) :
    (site.reference next).ctl = site.cursor.control
      (CanonicalTree.field Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
        site.field route.output >>= next) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot.referenceAt site bindings linked next

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot
