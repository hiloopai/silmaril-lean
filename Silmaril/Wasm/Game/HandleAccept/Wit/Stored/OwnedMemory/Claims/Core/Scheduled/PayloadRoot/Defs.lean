module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints Stored.Endpoints.RecordLower PayloadPrefix

structure Site (grow : SingleThreaded.GrowOracle) (sig : Signature) (route : GiveEffectRoute) where
  start : Config (core3 grow) (HostState sig)
  destination : RecordDestination
  inst : InstId
  name : String
  functionType : V1.FuncType
  handle : BitVec IntType.i32.width
  tag : sig.Tag
  payload : OwnedMemory.Payload (sig.payload tag)
  arity : Nat
  children : Fin arity → OwnedMemory.Tree sig
  field : Field
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  resume : List FlatValue → Session grow sig (Ret (core3 grow))
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}

def Site.tree (site : Site grow sig route) : OwnedMemory.Tree sig := .tag ⟨site.tag, site.payload⟩ site.arity site.children

def Site.cursor (site : Site grow sig route) : Cursor (E := core3 grow) (HostState sig) :=
  ⟨site.thread, .core site.core site.resume :: site.frames, site.rest⟩

def Site.reply (site : Site grow sig route) (verdict : Except RecordLower.Issue route.output.Result) :
    Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion (route.reply site.destination site.start.host.nextTicket verdict))

def Site.withBody (site : Site grow sig route) (program : Session grow sig (Ret (core3 grow))) : Config (core3 grow) (HostState sig) :=
  { site.start with host := site.start.host.enter site.name site.functionType (route.args site.handle)
                    ctl := site.cursor.control program }

def Site.refusedReply (site : Site grow sig route) (issue : RecordLower.Issue) : Config (core3 grow) (HostState sig) :=
  let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
  let reached := site.withBody (site.reply (.error issue))
  { reached with host := reached.host.record reply.1
                 ctl := ⟨site.thread, .core ((core3 grow).resume reached.store.core site.core (.values reply.2))
                   site.resume, site.frames⟩ :: site.rest }

def Site.checked (site : Site grow sig route) : Config (core3 grow) (HostState sig) :=
  site.withBody (Record.Effects.field recordClaims Limits.spec Quirks.none (site.destination.context site.inst)
    site.destination.width site.field 0 route.output >>= site.reply)

abbrev Site.ReferenceNext (_site : Site grow sig route) := route.output.Result → Session grow sig (Ret (core3 grow))

/-- Successful reference lowering uses the public reply ABI but not the
checked host's completion journal. A typed refusal has no reference reply. -/
def Site.referenceReply (site : Site grow sig route) : site.ReferenceNext := fun value =>
  pure (.flat (route.reply site.destination site.start.host.nextTicket (.ok value)).2)

noncomputable def Site.reference (site : Site grow sig route) (next : site.ReferenceNext) : Config (core3 grow) (HostState sig) :=
  let context := site.destination.context site.inst
  let schema := sig.payload site.tag
  let value := site.payload.val.value
  let program := Lower.Output.rec (motive := fun output => Session grow sig output.Result)
    (fun ptr => store Limits.spec Quirks.none context value schema ptr)
    (lowerFlatAt Limits.spec Quirks.none context site.destination.width value schema) route.output
  { site.start with ctl := site.cursor.control (program >>= next) }

/-- Facts about the actual caller, binding and selected root. Preparation,
allocation fit and placement are executed rather than assumed. -/
structure Site.Linked (site : Site grow sig route) (bindings : List (Binding sig)) : Prop where
  parked : site.start.ctl = ⟨site.thread, .core site.core site.resume, site.frames⟩ :: site.rest
  calling : (core3 grow).status site.start.store.core site.core = .callout (.embedder site.name site.functionType)
    (route.args site.handle)
  linked : resolveBinding bindings site.name site.functionType = .ok ⟨site.name, site.inst, route.action site.destination⟩
  caller : Plain.callerInstance site.start.store site.thread = .ok (some site.inst)
  mayLeave : (site.start.store.inst? site.inst).any (·.mayLeave) = true
  destination : site.destination.check site.start.store = .ok ()
  selected : Endpoints.Core.childFromHistory site.start.host.writer.accepted site.handle = some site.tree
  admitted : route.admits site.destination site.tree
  compiled : ∃ plan, Record.preflightValue (site.destination.context (grow := grow) site.inst) (sig.payload site.tag)
    site.payload route.output = .ok (site.field, plan)

/-- The actual prefix before the first recursive field. No recursive
comparison, allocator return or completion delivery is assumed. -/
inductive Cut (site : Site grow sig route) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (body : Prop := True) (impl : HostImpl (core3 grow) (HostState sig) := host bindings) : Prop where
  | refused (issue : RecordLower.Issue) {labels} (silent : visible labels = []) :
      Steps profile ready (specDispatch ready impl) site.start labels (site.withBody (site.reply (.error issue))) →
      Cut site profile ready bindings body impl
  | placementTrap (reason : TrapReason) (count : Nat)
      (verdict : rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason) :
      Steps profile ready (specDispatch ready impl) site.start (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg site.checked) → Cut site profile ready bindings body impl
  | placed {labels} (silent : visible labels = [])
      (verdict : rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
      (prepared : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
      Steps profile ready (specDispatch ready impl) site.start labels site.checked → body →
      Cut site profile ready bindings body impl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot
