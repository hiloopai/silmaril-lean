module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedPayloadEffects

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

theorem parked {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (handle : BitVec IntType.i32.width)
    (route : GiveEffectRoute) (inst : InstId) (destination : RecordDestination) (tree : OwnedMemory.Tree sig)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) (route.args handle))
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, route.action destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handle = some tree)
    (admitted : route.admits destination tree)
    (impl : HostImpl (core3 grow) (HostState sig)) (embedder : impl.embedder = (host (grow := grow) bindings).embedder) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready (specDispatch ready impl) start labels
        { start with host := start.host.enter name type (route.args handle)
                     ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
                       .core core continuation :: segments⟩ :: rest } := by
  cases route with
  | memory pointer =>
    obtain ⟨labels, silent, steps⟩ := Plain.parked_give_payload bindings name type handle pointer inst destination
      tree start thread profile ready parked calling linked caller mayLeave admitted destinationChecked selected impl embedder
    refine ⟨labels, silent, ?_⟩
    rw [GiveEffectRoute.run, ← OwnedMemory.Claims.Record.Effects.lowerPayloadRoot_eq]
    exact steps
  | flat payload =>
    obtain ⟨labels, silent, steps⟩ := Plain.parked_give_flat bindings name type handle inst destination payload
      tree start thread profile ready parked calling linked caller mayLeave destinationChecked selected admitted impl embedder
    refine ⟨labels, silent, ?_⟩
    rw [GiveEffectRoute.run, ← OwnedMemory.Claims.Record.Effects.lowerPayloadRoot_eq]
    exact steps

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedPayloadEffects
