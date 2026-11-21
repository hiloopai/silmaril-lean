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

/-- Lift a direct owning operand at the actual reached caller cursor. The
cut returns its nominal identity or traps in the reached store; it does
not treat an old numeric slot or an immutable observation as authority. -/
theorem LowerStartAt.direct_owner_read {site : OnStartSite start} (handoff : LowerStartAt site)
    (resource : RtId) (types : List Stored.TypeOf) (operand : FlatValue) (cursor : FlatCursor)
    (schema : handoff.types = .own resource :: types)
    (fits : (flattenTypes handoff.readWidth handoff.types).length ≤ handoff.maxParams)
    (read : (handoff.cursor.next (.int .i32) : Session grow sig (FlatValue × FlatCursor)) = pure (operand, cursor)) :
    StringPlanPair profile ready bindings callees handoff.selectedRead (handoff.afterOwnHead resource types cursor) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.readOwnHead
    handoff resource types operand cursor schema fits read

/-- No allocator progress is required to classify a cut at installation. -/
def ArgumentAllocatorCut.atInstall (alloc : ArgumentStringAllocation start) : ArgumentAllocatorCut profile ready bindings alloc :=
  .suspend (alloc.installed ready bindings) [] (.active 0 0) (.done _ _) (by
    intro leading cut label trailing labels _ _
    simp at labels)

/-- Execute the allocation and live range check shared by canonical flat
and memory list/map lowering. A successful cut passes the reached pointer
to `next`; a trap retains callback effects, and a finite suspension need
not return. This cut ends before the element stores or descriptor writes. -/
theorem collection_range_pair (context : LiftLowerContext (core3 grow)) (layout : ABI.Layout) (count : Nat)
    (next : Nat → Session grow sig (Ret (core3 grow))) (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (allocateListRange context layout count >>= next)) :
    StringPlanPair profile ready bindings callees start next :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.listRange
    context layout count next choose start cursor focused

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

/-- Traverse the supported recursively typed argument values in ABI order.
The collection layout is read at allocation and each child runs at the
reached store, including any earlier allocator effects. -/
theorem CalleeArguments.direct_arguments {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached : State grow sig} {returned : LowerArgumentReturn handoff reached}
    (args : CalleeArguments returned) (fields : List ArgumentField)
    (schema : args.types = fields.map ArgumentField.type) (input : returned.values = fields.map ArgumentField.value)
    (typed : ∀ field ∈ fields, ArgumentField.Valid field)
    (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees reached args.enter :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.directArguments
    args fields schema input typed fits choose

/-- Traverse the supported recursively typed arguments after actual spill
placement. Each dynamic collection writes its real descriptor after the last
element. An indirect map uses the allocation-time key/value layout. A late
trap retains the writes of its reached prefix. -/
theorem CalleeSpillReturn.spilled_arguments {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached state : State grow sig} {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    (result : CalleeSpillReturn args state) (fields : List ArgumentField) {memory size}
    (schema : args.types = fields.map ArgumentField.type) (input : returned.values = fields.map ArgumentField.value)
    (typed : ∀ field ∈ fields, ArgumentField.Valid field)
    (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
    (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
    (fits : result.pointer + args.layout.size ≤ size) (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees state (fun _ : Unit => args.enter [ptrFlat args.width result.pointer]) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.spilledArguments
    result fields schema input typed aligned selected sized fits choose

/-- The direct string-only specialization. -/
theorem CalleeArguments.direct_string_arguments {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached : State grow sig} {returned : LowerArgumentReturn handoff reached}
    (args : CalleeArguments returned) (strings : List Value.StrVal)
    (schema : args.types = stringArgumentTypes strings) (input : returned.values = stringArgumentValues strings)
    (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees reached args.enter := by
  apply args.direct_arguments (strings.map ArgumentField.string) _ _ _ fits choose
  · simpa only [List.map_map, Function.comp_def, ArgumentField.type, stringArgumentTypes] using schema
  · simpa only [List.map_map, Function.comp_def, ArgumentField.value, stringArgumentValues] using input
  · intro field present
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp present
    exact .string value

/-- Compose all spilled string descriptor stores from the live outer spill
return. Each tuple step receives the previous field's ABI end cursor. -/
theorem CalleeSpillReturn.spilled_string_arguments {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached state : State grow sig} {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    (result : CalleeSpillReturn args state) (strings : List Value.StrVal) {memory size}
    (schema : args.types = stringArgumentTypes strings) (input : returned.values = stringArgumentValues strings)
    (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
    (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
    (fits : result.pointer + args.layout.size ≤ size) (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees state (fun _ : Unit => args.enter [ptrFlat args.width result.pointer]) := by
  apply result.spilled_arguments (strings.map ArgumentField.string) _ _ _ aligned selected sized fits choose
  · simpa only [List.map_map, Function.comp_def, ArgumentField.type, stringArgumentTypes] using schema
  · simpa only [List.map_map, Function.comp_def, ArgumentField.value, stringArgumentValues] using input
  · intro field present
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp present
    exact .string value

/-- If the selected argument lowering finishes, enter the actual stackful
Core callee with its canonical operands. A trap or suspended path performs
no entry step. Entry uses the reached activation and does not imply return. -/
theorem CalleeArguments.enter_stackful_after_strings {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached first : State grow sig} {returned : LowerArgumentReturn handoff reached}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none) :
    ∃ labels last, Steps profile ready (Dispatch.coreOnly ready bindings) first labels last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) first labels last ∧
      ((∃ (cursor : Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
        last.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest) ∨
        StringPlanStopped profile ready bindings first labels last) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.enterStackful
    args words lowered asyncMode callback

/-- Continue actual Core entry along a finite classified body. An observed
return takes the live worker exit or last-thread unresolved trap, with no
assumption that the body returns, or preserves bytes, records, or events. -/
theorem CalleeArguments.finish_stackful_after_arguments {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached first : State grow sig} {returned : LowerArgumentReturn handoff reached}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (select : ∀ (entry : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      StackfulBodyCut profile ready bindings callees args.task entry) :
    ∃ labels last, Steps profile ready (Dispatch.coreOnly ready bindings) first labels last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) first labels last ∧
      StackfulWorkerEnd profile ready bindings first args.task args.callee labels last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.finishStackful
    args words lowered asyncMode callback select

/-- Continue from the worker cut into a finite result-delivery path. Poll,
wait and cancel consume events from their own reached stores, including
delivery paths that later trap writing the event buffer. The tail can be
empty, and no open cancellation hook is classified by this theorem. -/
theorem CalleeArguments.finish_stackful_with_delivery {site : OnStartSite start} {handoff : LowerStartAt site}
    {reached first : State grow sig} {returned : LowerArgumentReturn handoff reached}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (select : ∀ (entry : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      StackfulBodyCut profile ready bindings callees args.task entry)
    (delivery : ∀ leading cut, StackfulWorkerEnd profile ready bindings first args.task args.callee leading cut →
      ∃ actions trailing last, Run profile ready (host bindings) cut actions trailing last ∧
        ∀ action ∈ actions, ClosedDeliveryAction action) :
    ∃ leading cut actions trailing last,
      StackfulWorkerEnd profile ready bindings first args.task args.callee leading cut ∧
      Run profile ready (ComponentCall.hostWithComponent bindings callees) cut actions trailing last ∧
      Steps profile ready (Dispatch.coreOnly ready bindings) first (leading ++ trailing) last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) first (leading ++ trailing) last :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan.finishWithDelivery
    args words lowered asyncMode callback select delivery

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
