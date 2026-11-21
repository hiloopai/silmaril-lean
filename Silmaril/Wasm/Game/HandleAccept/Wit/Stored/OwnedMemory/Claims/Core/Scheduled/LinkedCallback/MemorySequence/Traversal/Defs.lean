module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Traversal.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.ABI
open Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

def CarriesFinish (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (compare : FieldComparison grow sig) : Prop :=
  ∀ item index address left right check canon checkNext canonNext {originLeft originRight : State grow sig}
    {finish target : Finish grow sig},
    TrackedAdvance profile ready bindings originLeft originRight left right →
    compare item index address left right check canon checkNext canonNext finish →
    (∀ lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish lhs rhs check canon → target lhs rhs check canon) →
    compare item index address left right check canon checkNext canonNext target

def CarriesFlatFinish (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (compare : FlatFieldComparison grow sig) : Prop :=
  ∀ item index left right check canon checkNext canonNext {originLeft originRight : State grow sig}
    {finish target : FlatResultCut grow sig},
    TrackedAdvance profile ready bindings originLeft originRight left right →
    compare item index left right check canon checkNext canonNext finish →
    (∀ words lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish words lhs rhs check canon → target words lhs rhs check canon) →
    compare item index left right check canon checkNext canonNext target

def GiveReplies {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (value : route.output.Result)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (reached reference left right : State grow sig) : Prop :=
  let reply := route.reply call.destination call.start.host.nextTicket (.ok value)
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  (∀ dispatch, Steps profile ready dispatch reached [.tau, .tau, .tau] left) ∧
    (∀ dispatch, Steps profile ready dispatch reference [.tau] right) ∧ left.store = right.store ∧
    left.host = reached.host.record reply.1 ∧ right.host = reference.host ∧
    HostFrame.Related.Paired older left right

def RejoinedGive {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (value : route.output.Result)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (reached reference : State grow sig) : Prop :=
  TrackedAdvance profile ready bindings call.checked (call.reference call.referenceReply) reached reference ∧
    ∃ left right, GiveReplies call value profile ready reached reference left right

def ParkedMemoryBody {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer)) (depth : Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (finish : State grow sig → State grow sig → Prop) : Prop :=
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  listTree profile ready bindings older call.destination call.inst depth call.field 0 (flatNat pointer)
    call.checked (call.reference call.referenceReply) call.cursor call.cursor call.reply call.referenceReply
    (fun reached reference _ _ => finish reached reference)

def ParkedFlatResult {schema : Stored.TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (flatDepth entryDepth : Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (finish : List FlatValue → State grow sig → State grow sig → Prop) : Prop :=
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  nestedFlatComparison profile ready bindings (flatAllocating profile ready bindings older call.destination call.inst entryDepth)
    older call.destination call.inst flatDepth call.field 0 call.checked (call.reference call.referenceReply)
    call.cursor call.cursor call.reply call.referenceReply
    (fun value reached reference _ _ => finish value reached reference)

def ParkedRejoinedMemory {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer)) (depth : Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ParkedMemoryBody call depth profile ready bindings (RejoinedGive call () profile ready bindings)

def ParkedRejoinedFlat {schema : Stored.TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (flatDepth entryDepth : Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ParkedFlatResult call flatDepth entryDepth profile ready bindings
    (fun words => RejoinedGive call words profile ready bindings)

/-- The exact placed entry, before any recursive lowering effects. Its
continuation is used only on successful body paths and cannot convert a stop
into a return. -/
def OnGiveReturn {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) (impl : HostImpl (core3 grow) (HostState sig))
    (finish : route.output.Result → State grow sig → State grow sig → Prop) : Prop :=
  ∀ {labels}, visible labels = [] → rootPlacement call.destination call.start.store (sig.payload call.tag) route.output = .ok () →
    Record.prepare call.start.store call.start.host.writer call.field.objects = .ok () →
    Steps profile ready (specDispatch ready impl) call.start labels call.checked →
    ∀ value reached reference, RejoinedGive call value profile ready bindings reached reference → finish value reached reference

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
