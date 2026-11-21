module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

theorem NestedPlan.source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.source plan

/-- Descend through compared nested bodies, then continue from the actual
caller rejoin with the reached host. Only the completed case has the full
checked observable trace as a guarantee. A cut records a reached configuration
and a matching observable prefix, not execution of the unvisited suffix. -/
theorem NestedPlan.runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      PayloadPrefix.visible trace <+: PayloadPrefix.visible labels ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.runs plan paired

/-- Join actual argument lowering and Core entry to a classified body,
worker completion and delivery under one linked dispatcher. The body may
contain nested gives; it is selected only at the reached Core entry. An
argument trap or suspension instead ends the finite plan before entry. -/
theorem stackful_worker_plan {reached first : Config (core3 grow) (HostState sig)} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {callees : List (ComponentCall.Callee sig)}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (body : ∀ (entry : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      ∃ bodyLabels afterBody exitLabels afterExit deliveryLabels last,
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry bodyLabels afterBody ∧
        StackfulBodyEnd args.task afterBody exitLabels afterExit ∧
        (∀ (site : StackfulReturn afterBody), site.segments = []) ∧
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) afterExit deliveryLabels last) :
    ∃ leading entry trailing last,
      Steps profile ready (Dispatch.linked ready bindings callees) first leading entry ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) first (leading ++ trailing) last ∧
      ((∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
          entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest ∧
          NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry trailing last) ∨
        (StringPlanStopped profile ready bindings first leading entry ∧ trailing = [] ∧ last = entry)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.stackfulWorker
    args words lowered asyncMode callback body

/-- A placed public memory or flat give with a nonallocating data root has
its body comparison derived from the compiled field and linked width.
It rejoins the original Core caller on success; a canonical trap instead
keeps the common reached store and does not issue a completion reply. -/
theorem local_data_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    ∃ bodyLabels reached, NestedPlan bindings profile ready base site.start (entryLabels ++ bodyLabels) reached ∧
      ((∃ value checkedLabels atReply,
        Steps profile ready (specDispatch ready base) site.checked checkedLabels atReply ∧
        atReply.ctl = site.cursor.control (site.reply (.ok value)) ∧ bodyLabels = checkedLabels ++ [.tau, .tau, .tau] ∧
        reached.host = atReply.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1) ∨
      (reached.ctl = [] ∧ ∃ leading reason, PayloadPrefix.visible bodyLabels = leading ++ [.trap reason])) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.localDataGive
    site linked data payload field entryPath silent placed prepared

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
