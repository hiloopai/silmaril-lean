module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open PayloadPrefix (Cursor)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)} {callees : List (Callee sig)}
  {start : State grow sig}

/-- No allocator progress is required to classify a cut at installation. -/
def ArgumentAllocatorCut.atInstall (alloc : ArgumentStringAllocation start) : ArgumentAllocatorCut profile ready bindings alloc :=
  .suspend (alloc.installed ready bindings) [] (.active 0 0) (.done _ _) (by
    intro leading cut label trailing labels _ _
    simp at labels)

/-- Execute the local canonical plan, and resume at each actual marked
allocator return. The plan decreases only after a successful pointer return.
The reached memory and scheduler tail, including callback effects, are used
for all subsequent reads and writes. Only the selected allocator prefixes
need classification; they need not return. -/
theorem string_plan_pair (context : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (plan : StorePlan) (next : output.Result → Session grow sig (Ret (core3 grow)))
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (ptr : Nat) (steps : List StoreStep) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control
      (runStoreSteps context ptr steps >>= fun final => PayloadPrefix.stringPlanTail context width output plan final >>= next)) :
    StringPlanPair profile ready bindings callees start next :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.walk
    context width output plan next choose ptr steps start cursor focused

/-- Start at the reached selected worker, commit the caller cursor and
lower the first direct string argument. The successful continuation appends
its actual flat words to the canonical lowering of the remaining arguments. -/
theorem CalleeArguments.direct_string_pair {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached : State grow sig} {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
    {value values types} (schema : args.types = .prim .string :: types) (input : returned.values = .string value :: values)
    (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees reached (directStringTail args.context args.width values types args.enter) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.directCallee args schema input fits choose

/-- From the reached outer spill return, validate placement and lower the
first string argument. Tuple placement and any later descriptor writes use
their respective width reads; no saved callback bytes are restored. -/
theorem CalleeSpillReturn.spilled_string_pair {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached state : State grow sig} {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    (result : CalleeSpillReturn args state) {memory size value values types}
    (schema : args.types = .prim .string :: types) (input : returned.values = .string value :: values)
    (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
    (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
    (fits : result.pointer + args.layout.size ≤ size) (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    let field := ABI.layout (ptrTypeIn state.store args.context) (.prim .string : Stored.TypeOf)
    let address := ABI.alignTo result.pointer field.alignment
    StringPlanPair profile ready bindings callees state (fun _ : Unit =>
      storeTuple .spec .none args.context values types (address + field.size) >>= fun _ =>
        args.enter [ptrFlat args.width result.pointer]) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.spilledCallee
    result schema input aligned selected sized fits choose

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
