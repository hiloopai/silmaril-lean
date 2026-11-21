module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedPayloadEffects

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Field Object)

/-- Both linked public give imports run the recursive effect view with the
original Core activation, continuation and reply ticket. This is entry into
the effect program, not a guarantee that an allocator or the export returns. -/
theorem GiveEffectRoute.parked {sig : Signature} {grow : SingleThreaded.GrowOracle}
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
    (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready (specDispatch ready impl) start labels
        { start with host := start.host.enter name type (route.args handle)
                     ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
                       .core core continuation :: segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedPayloadEffects.parked
    bindings name type handle route inst destination tree start thread profile ready parked calling linked caller
    mayLeave destinationChecked selected admitted impl embedder

/-- The actual start steps give the effect view the compiler's value, layout,
and exact receipt order. A failed dry run or width-dependent fit check reaches
typed completion before entering the recursive program. -/
theorem RecordDestination.compiled_payload_effects {sig : Signature} {grow : SingleThreaded.GrowOracle}
    {profile : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) (output : Lower.Output)
    (field : Field) (plan : List Object)
    (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload output = .ok (field, plan))
    (destinationChecked : destination.check reached.store = .ok ()) {thread segments rest}
    {arity : Nat} {children : Fin arity → OwnedMemory.Tree sig}
    (focused : reached.ctl = ⟨thread, .prog (Record.Effects.lowerTree recordClaims Limits.spec Quirks.none
      (destination.context inst) (.tag ⟨tag, payload⟩ arity children) output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let type := sig.payload tag
    field.value = payload.val.value ∧ field.LayoutMatches type ∧
    payload.val.owners = field.objects.filterMap Object.ownerReceipt ∧
    match Record.prepare reached.store reached.host.writer field.objects with
    | .error issue => Machine.Steps profile ready dispatch reached [.tau, .tau]
        { reached with ctl := ⟨thread, .prog (finish (.error issue)), segments⟩ :: rest }
    | .ok () => Machine.Steps profile ready dispatch reached [.tau, .tau, .tau]
        { reached with ctl := ⟨thread, .prog (
          if !Lower.fits Quirks.none destination.encoding destination.width type payload.val.value then
            finish (.error (.preflight (.abi .allocationPrecondition)))
          else Record.Effects.root recordClaims Limits.spec Quirks.none cx destination.width type field output >>= finish),
          segments⟩ :: rest } := by
  rw [← Record.Effects.lowerPayloadRoot_eq] at focused
  dsimp only
  rw [← Record.Effects.emitValue_eq recordClaims Limits.spec Quirks.none
    (destination.context (grow := grow) inst) destination.width (sig.payload tag) field output]
  exact destination.compiled_payload_start reached inst (sig.payload tag)
    payload output field plan finish compiled destinationChecked focused

/-- The comparator for the very field admitted by the public give paths.
It computes the untouched reference program; it has no permission to spend
claims and does not claim the checked path can always reach its suffix. -/
theorem RecordDestination.compiled_payload_reference {grow : SingleThreaded.GrowOracle} {World : Type}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (payload : OwnedMemory.Payload type)
    (output : Lower.Output) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) type payload output = .ok (field, plan)) :
    let cx := destination.context (grow := grow) inst
    Endpoints.RecordLower.CanonicalTree.field Limits.spec Quirks.none cx destination.width field output =
      Lower.Output.rec (motive := fun out => P (core3 grow) World out.Result)
        (fun ptr => store Limits.spec Quirks.none cx payload.val.value type ptr)
        (lowerFlatAt Limits.spec Quirks.none cx destination.width payload.val.value type) output :=
  Endpoints.RecordLower.CanonicalTree.field_reference Limits.spec Quirks.none _ destination.width field type _
    (Record.preflightValue_layout _ _ _ _ _ _ compiled) (Record.preflightValue_value _ _ _ _ _ _ compiled) output

/-- After either public give takes the successful allocation guard, descent
keeps that check's concrete encoding and linked width. This certifies the
static value precondition only; reached range and live authority checks stay
in the effect programs. -/
theorem RecordDestination.compiled_payload_descendant {grow : SingleThreaded.GrowOracle}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (payload : OwnedMemory.Payload type)
    (output : Lower.Output) {field child : Field} {plan : List Object}
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) type payload output = .ok (field, plan))
    (admitted : Lower.fits Quirks.none destination.encoding destination.width type payload.val.value = true)
    (path : field.Descendant child) :
    child.LayoutMatches child.type ∧ Lower.fits Quirks.none destination.encoding destination.width
      child.type child.value = true := by
  rw [← Record.preflightValue_value _ _ _ _ _ _ compiled] at admitted
  exact path.fits (Record.preflightValue_layout _ _ _ _ _ _ compiled) _ _ _ admitted

theorem RecordDestination.compiled_payload_sum_tag {grow : SingleThreaded.GrowOracle}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (payload : OwnedMemory.Payload type)
    (output : Lower.Output) {field : Field} {plan : List Object}
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) type payload output = .ok (field, plan))
    (admitted : Lower.fits Quirks.none destination.encoding destination.width type payload.val.value = true)
    {sumType : TypeOf} {arms : List (Option TypeOf)} {tag : Nat} {selected : Option Field}
    (path : field.Descendant (.sum sumType arms tag selected)) : tag < arms.length := by
  cases (destination.compiled_payload_descendant inst type payload output compiled admitted path).1 <;>
    first | exact (List.getElem?_eq_some_iff.mp ‹_›).1 | simp

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
