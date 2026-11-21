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

def ParkedRejoinedMemory {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer)) (depth : Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  listTree profile ready bindings older call.destination call.inst depth call.field 0 (flatNat pointer)
    call.checked (call.reference call.referenceReply) call.cursor call.cursor call.reply call.referenceReply
    (fun reached reference _ _ => RejoinedGive call () profile ready bindings reached reference)

def ParkedRejoinedFlat {schema : Stored.TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (flatDepth entryDepth : Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  let older : ReturnFrame.Substitutions (core3 grow) (HostState sig) := fun _ _ => False
  nestedFlatComparison profile ready bindings (flatAllocating profile ready bindings older call.destination call.inst entryDepth)
    older call.destination call.inst flatDepth call.field 0 call.checked (call.reference call.referenceReply)
    call.cursor call.cursor call.reply call.referenceReply
    (fun value reached reference _ _ => RejoinedGive call value profile ready bindings reached reference)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
