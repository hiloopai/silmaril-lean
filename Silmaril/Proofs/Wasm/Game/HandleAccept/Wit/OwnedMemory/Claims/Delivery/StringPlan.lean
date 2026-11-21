module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open ComponentCall (Callee)
open ComponentCall.Delivery.FiniteSession
open PayloadPrefix (Cursor StringFront)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)} {callees : List (Callee sig)}

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle last : State grow sig} {leading trailing : Trace grow sig}
    (first : Steps profile ready dispatch start leading middle) (second : Steps profile ready dispatch middle trailing last) :
    Steps profile ready dispatch start (leading ++ trailing) last := by
  induction first with
  | refl => exact second
  | cons step _ ih => exact .cons step (ih second)

private theorem prependEnd {Result : Type} {next : Result → Session grow sig (Ret (core3 grow))}
    {leading labels : Trace grow sig} {start middle last : State grow sig}
    (first : Steps profile ready (Dispatch.coreOnly ready bindings) start leading middle)
    (endAt : StringPlanEnd profile ready bindings middle next labels last) :
    StringPlanEnd profile ready bindings start next (leading ++ labels) last := by
  cases endAt with
  | complete cursor value focused => exact .complete cursor value focused
  | trap reason => rw [← List.append_assoc]; exact .trap reason
  | suspend alloc _ _ mark reached path closed =>
    rw [← List.append_assoc]
    exact .suspend alloc _ _ mark (appendSteps first reached) path closed

private theorem prependPair {Result : Type} {next : Result → Session grow sig (Ret (core3 grow))}
    {leading : Trace grow sig} {start middle : State grow sig}
    (left : Steps profile ready (Dispatch.coreOnly ready bindings) start leading middle)
    (right : Steps profile ready (Dispatch.linked ready bindings callees) start leading middle)
    (tail : StringPlanPair profile ready bindings callees middle next) :
    StringPlanPair profile ready bindings callees start next := by
  obtain ⟨_, _, tailLeft, tailRight, endAt⟩ := tail
  exact ⟨_, _, appendSteps left tailLeft, appendSteps right tailRight, prependEnd left endAt⟩

private theorem continuePair {Field Result : Type}
    {rest : Field → Session grow sig (Ret (core3 grow))} {next : Result → Session grow sig (Ret (core3 grow))}
    {start : State grow sig} (first : StringPlanPair profile ready bindings callees start rest)
    (tail : ∀ (last : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) value,
      last.ctl = cursor.control (rest value) →
      StringPlanPair profile ready bindings callees last next) :
    StringPlanPair profile ready bindings callees start next := by
  obtain ⟨labels, last, left, right, endAt⟩ := first
  cases endAt with
  | complete cursor value focused => exact prependPair left right (tail last cursor value focused)
  | trap reason => exact ⟨_, _, left, right, .trap reason⟩
  | suspend alloc leading trailing mark reached path closed =>
    exact ⟨_, _, left, right, .suspend alloc leading trailing mark reached path closed⟩

private theorem mapPair {Value Result : Type} {start : State grow sig}
    (next : Result → Session grow sig (Ret (core3 grow))) (mapResult : Value → Result)
    (path : StringPlanPair profile ready bindings callees start (fun value => next (mapResult value))) :
    StringPlanPair profile ready bindings callees start next := by
  obtain ⟨_, _, left, right, endAt⟩ := path
  cases endAt with
  | complete cursor value focused => exact ⟨_, _, left, right, .complete cursor (mapResult value) focused⟩
  | trap reason => exact ⟨_, _, left, right, .trap reason⟩
  | suspend alloc leading trailing mark reached prefixAt closed =>
    exact ⟨_, _, left, right, .suspend alloc leading trailing mark reached prefixAt closed⟩

private theorem invalidAnswer {state : State grow sig} (alloc : ArgumentStringAllocation state) (last : State grow sig)
    (reached : Cursor (E := core3 grow) (HostState sig)) (answer : Ret (core3 grow))
    (invalid : ¬ ∃ pointer, answer = .nat pointer) :
    (alloc.resumed last reached answer).ctl = reached.control (trap (.internal "late-bound call: expected Ret.nat")) := by
  cases answer with
  | nat pointer => exact (invalid ⟨pointer, rfl⟩).elim
  | _ =>
    simp only [ArgumentStringAllocation.resumed, ArgumentStringAllocation.resume, PayloadPrefix.stringPlanResume,
      internal, trap, Prog.bind_eq, Prog.bind]
    congr
    funext impossible
    exact nomatch impossible

private theorem followAllocation {Result : Type} {start : State grow sig}
    {next : Result → Session grow sig (Ret (core3 grow))} (alloc : ArgumentStringAllocation start)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (after : ∀ last reached pointer,
      StringPlanPair profile ready bindings callees (alloc.resumed last reached (.nat pointer)) next) :
    StringPlanPair profile ready bindings callees start next := by
  cases choose alloc with
  | suspend last trailing mark path closed =>
    obtain ⟨left, right, _⟩ := alloc.linked_prefix (callees := callees) path closed
    exact ⟨_, _, left, right, .suspend alloc [] trailing mark (.refl _) path closed⟩
  | returned last trailing path closed reached answer resume pop =>
    obtain ⟨left, right⟩ := alloc.linked_return (callees := callees) path closed reached answer pop
    by_cases valid : ∃ pointer, answer = .nat pointer
    · obtain ⟨pointer, rfl⟩ := valid
      exact prependPair left right (after last reached pointer)
    · have focused := invalidAnswer alloc last reached answer valid
      exact ⟨_, _, appendSteps left (.cons (.trap focused) (.refl _)),
        appendSteps right (.cons (.trap focused) (.refl _)), .trap _⟩
  | trapped last trailing reason path closed =>
    obtain ⟨left, right⟩ := alloc.linked_steps (callees := callees) path closed
    exact ⟨_, _, left, right, StringPlanEnd.trap (leading := .tau :: trailing) reason⟩

theorem walk (context : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (plan : StorePlan) (next : output.Result → Session grow sig (Ret (core3 grow)))
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (ptr : Nat) (steps : List StoreStep) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control
      (runStoreSteps context ptr steps >>= fun final => PayloadPrefix.stringPlanTail context width output plan final >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  let finish := fun final => PayloadPrefix.stringPlanTail context width output plan final >>= next
  obtain ⟨store, result, labels, observed, left, right, _⟩ :=
    PayloadPrefix.string_front_cut_between (profile := profile) (ready := ready)
      (dispatch := Dispatch.coreOnly ready bindings) (reference := Dispatch.linked ready bindings callees)
      context ptr steps start start cursor cursor finish finish rfl focused focused
  cases result with
  | error reason =>
    obtain ⟨count, rfl⟩ := observed
    exact ⟨_, _, left.steps, right.steps, .trap reason⟩
  | ok front =>
    cases front with
    | done final =>
      let cut := localLeafEnd start start.host store cursor.thread cursor.frames cursor.rest
        (fun front : StringFront steps.length => front.remaining context >>= finish) (.ok (.done final))
      have atDescriptor : cut.ctl = cursor.control (PayloadPrefix.stringPlanTail context width output plan final >>= next) := rfl
      obtain ⟨storeAfter, resultAfter, trailing, trailObserved, trailLeft, trailRight, _⟩ :=
        PayloadPrefix.string_descriptor_cut_between (profile := profile) (ready := ready)
          (dispatch := Dispatch.coreOnly ready bindings) (reference := Dispatch.linked ready bindings callees)
          context width output plan final cut cut cursor cursor next next rfl atDescriptor atDescriptor
      have endAt : StringPlanEnd profile ready bindings cut next trailing
          (localLeafEnd cut cut.host storeAfter cursor.thread cursor.frames cursor.rest next resultAfter) := by
        cases resultAfter with
        | ok value => exact .complete cursor value rfl
        | error reason =>
          obtain ⟨count, rfl⟩ := trailObserved
          exact .trap reason
      exact prependPair left.steps right.steps ⟨_, _, trailLeft.steps, trailRight.steps, endAt⟩
    | call pointer oldSize alignment size residual shorter =>
      let alloc : ArgumentStringAllocation
          (localLeafEnd start start.host store cursor.thread cursor.frames cursor.rest
            (fun front : StringFront steps.length => front.remaining context >>= finish)
            (.ok (.call pointer oldSize alignment size residual shorter))) :=
        ⟨context, pointer, oldSize, alignment, size, residual, finish, cursor, rfl⟩
      exact prependPair left.steps right.steps (followAllocation alloc choose (fun last reached pointer =>
        walk context width output plan next choose pointer residual (alloc.resumed last reached (.nat pointer)) reached rfl))
termination_by steps.length

private theorem argumentTrap {Result : Type} {next : Result → Session grow sig (Ret (core3 grow))}
    (reason : TrapReason) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (trap reason)) :
    StringPlanPair profile ready bindings callees start next :=
  ⟨[.trap reason], _, .cons (.trap focused) (.refl _), .cons (.trap focused) (.refl _), .trap (leading := []) reason⟩

private theorem bindTrap {Input Result : Type} (reason : TrapReason) (next : Input → Session grow sig Result) :
    (trap reason).bind next = trap reason := by
  apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) (.trap reason))
  funext answer
  exact nomatch answer

private theorem validateRange (context : LiftLowerContext (core3 grow)) (layout : ABI.Layout) (count ptr : Nat)
    (next : Nat → Session grow sig (Ret (core3 grow))) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (validateListRange context layout count ptr >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  by_cases aligned : ptr = ABI.alignTo ptr layout.alignment
  · have notMisaligned : ¬ ptr ≠ ABI.alignTo ptr layout.alignment := fun misaligned => misaligned aligned
    cases selected : context.opts.memory with
    | none =>
      apply argumentTrap .noMemory start cursor
      rw [focused]
      simp [validateListRange, notMisaligned, trapIf, checkInBounds, memLen, memAddr, selected, orTrap, bindTrap]
    | some memory =>
      let body := fun (live : CStore (core3 grow)) =>
        (orTrap (.internal "dangling memory address") ((core3 grow).memSize? live.core memory)).bind
          fun size => (trapIf (decide (ptr + count * layout.size > size)) .outOfBounds).bind fun _ => next ptr
      let afterRead := { start with ctl := cursor.control (body start.store) }
      have readAt : start.ctl = cursor.control (.op .get body) := by
        rw [focused]
        simp [validateListRange, notMisaligned, trapIf, checkInBounds, memLen, memAddr, selected, orTrap, getStore,
          body, Prog.bind_assoc]
        rfl
      apply prependPair (middle := afterRead) (.cons (.get readAt) (.refl _)) (.cons (.get readAt) (.refl _))
      cases sized : (core3 grow).memSize? start.store.core memory with
      | none =>
        apply argumentTrap (.internal "dangling memory address") afterRead cursor
        simp [afterRead, body, sized, orTrap, bindTrap]
      | some size =>
        by_cases fits : ptr + count * layout.size ≤ size
        · exact ⟨[], afterRead, .refl _, .refl _, .complete cursor ptr (by
            simp [afterRead, body, sized, orTrap, trapIf, Nat.not_lt.mpr fits])⟩
        · apply argumentTrap .outOfBounds afterRead cursor
          simp [afterRead, body, sized, orTrap, trapIf, Nat.lt_of_not_ge fits, bindTrap]
  · apply argumentTrap .unalignedPointer start cursor
    rw [focused]
    simp [validateListRange, aligned, trapIf, bindTrap]

theorem listRange (context : LiftLowerContext (core3 grow)) (layout : ABI.Layout) (count : Nat)
    (next : Nat → Session grow sig (Ret (core3 grow))) (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (allocateListRange context layout count >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  let finish := fun ptr => validateListRange context layout count ptr >>= next
  let alloc : ArgumentStringAllocation start := ⟨context, 0, none, layout.alignment, count * layout.size,
    [], finish, cursor, by
      rw [focused]
      simp only [allocateListRange, runStoreSteps, Option.elim, Prog.foldlM, runStoreStep, Prog.bind_eq,
        Prog.bind_assoc, Prog.pure_bind', finish]⟩
  exact followAllocation alloc choose (fun last reached pointer =>
    validateRange context layout count pointer next (alloc.resumed last reached (.nat pointer)) reached rfl)

theorem directCallee {start reached : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned) {value values types}
    (schema : args.types = .prim .string :: types) (input : returned.values = .string value :: values)
    (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees reached (directStringTail args.context args.width values types args.enter) := by
  let plan := storePlanFor .none args.context.opts.encoding (ptrTypeIn returned.resumed.store args.context) value
  let cursor : Cursor (E := core3 grow) (HostState sig) := ⟨some site.thread, site.segments, site.rest⟩
  let tail := directStringTail args.context args.width values types args.enter
  apply prependPair (args.direct_string_plan (impl := host bindings) schema input fits)
    (args.direct_string_plan (impl := ComponentCall.hostWithComponent bindings callees) schema input fits)
  exact walk args.context args.width .flat plan tail choose 0 plan.steps _ cursor
    (congrArg cursor.control (Prog.bind_assoc (runStoreSteps args.context 0 plan.steps)
      (PayloadPrefix.stringPlanTail args.context args.width .flat plan) tail))

theorem spilledCallee {start reached state : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    (result : CalleeSpillReturn args state) {memory size value values types}
    (schema : args.types = .prim .string :: types) (input : returned.values = .string value :: values)
    (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
    (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
    (fits : result.pointer + args.layout.size ≤ size) (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    let field := ABI.layout (ptrTypeIn state.store args.context) (.prim .string : Stored.TypeOf)
    let address := ABI.alignTo result.pointer field.alignment
    StringPlanPair profile ready bindings callees state (fun _ : Unit =>
      storeTuple .spec .none args.context values types (address + field.size) >>= fun _ =>
        args.enter [ptrFlat args.width result.pointer]) := by
  let width := ptrTypeIn state.store args.context
  let field := ABI.layout width (.prim .string : Stored.TypeOf)
  let address := ABI.alignTo result.pointer field.alignment
  let plan := storePlanFor .none args.context.opts.encoding width value
  let cursor : Cursor (E := core3 grow) (HostState sig) := ⟨some site.thread, result.segments, result.rest⟩
  let tail := fun _ : Unit => storeTuple .spec .none args.context values types (address + field.size) >>= fun _ =>
    args.enter [ptrFlat args.width result.pointer]
  apply prependPair (result.spilled_string_plan (impl := host bindings) schema input aligned selected sized fits)
    (result.spilled_string_plan (impl := ComponentCall.hostWithComponent bindings callees) schema input aligned selected sized fits)
  exact walk args.context width (.memory address) plan tail choose 0 plan.steps _ cursor
    (congrArg cursor.control (Prog.bind_assoc (runStoreSteps args.context 0 plan.steps)
      (PayloadPrefix.stringPlanTail args.context width (.memory address) plan) tail))

private theorem flatScalar (context : LiftLowerContext (core3 grow)) (width : AddrType) (arg : DirectArgument) :
    (lowerFlatAt .spec .none context width arg.value arg.type : Session grow sig (List FlatValue)) = pure [arg.flat] := by
  cases arg <;> rw [DirectArgument.value, DirectArgument.type, lowerFlatAt] <;> rfl

private theorem memoryScalar (context : LiftLowerContext (core3 grow)) (arg : DirectArgument) (address : Nat) :
    (store .spec .none context arg.value arg.type address : Session grow sig Unit) = writeMem context address arg.bytes := by
  cases arg <;> rw [DirectArgument.type, DirectArgument.value, store.eq_def] <;> rfl

private theorem argumentStringRead (context : LiftLowerContext (core3 grow)) (width : AddrType)
    (output : Stored.Lower.Output) (value : Value.StrVal) (next : output.Result → Session grow sig (Ret (core3 grow)))
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (.op .get (argumentStringBody context width output value) >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  let plan := storePlanFor .none context.opts.encoding (ptrTypeIn start.store context) value
  let afterRead := { start with ctl := cursor.control (argumentStringBody context width output value start.store >>= next) }
  have readAt : start.ctl = cursor.control (.op .get fun live => argumentStringBody context width output value live >>= next) := focused
  apply prependPair (middle := afterRead) (.cons (.get readAt) (.refl _)) (.cons (.get readAt) (.refl _))
  exact walk context width output plan next choose 0 plan.steps afterRead cursor
    (congrArg cursor.control (Prog.bind_assoc (runStoreSteps context 0 plan.steps)
      (PayloadPrefix.stringPlanTail context width output plan) next))

private theorem argumentWrite (context : LiftLowerContext (core3 grow)) (address : Nat) (bytes : ByteArray)
    (next : Unit → Session grow sig (Ret (core3 grow))) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (writeMem context address bytes >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  obtain ⟨_, result, _, observed, left, right, _⟩ := PayloadPrefix.write_cut_between
    (profile := profile) (ready := ready) (dispatch := Dispatch.coreOnly ready bindings)
    (reference := Dispatch.linked ready bindings callees) context address bytes start start cursor cursor next next rfl focused focused
  cases result with
  | ok written => exact ⟨_, _, left.steps, right.steps, .complete cursor written rfl⟩
  | error reason =>
    obtain ⟨count, rfl⟩ := observed
    exact ⟨_, _, left.steps, right.steps, .trap reason⟩

private theorem descriptor (context : LiftLowerContext (core3 grow)) (ptr count address : Nat)
    (next : Unit → Session grow sig (Ret (core3 grow))) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (storeListDescriptor context ptr count address >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  let tail := fun size => writeMem context (address + size) (intToLE size count) >>= next
  let body := fun live =>
    let size := ptrSizeOf (ptrTypeIn live context)
    writeMem context address (intToLE size ptr) >>= fun _ => tail size
  let afterWidth := { start with ctl := cursor.control (body start.store) }
  have readAt : start.ctl = cursor.control (.op .get body) := by
    rw [focused]
    simp only [storeListDescriptor, ptrSize, storeInt, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    rfl
  apply prependPair (middle := afterWidth) (.cons (.get readAt) (.refl _)) (.cons (.get readAt) (.refl _))
  let size := ptrSizeOf (ptrTypeIn start.store context)
  exact continuePair (argumentWrite context address (intToLE size ptr) (fun _ => tail size) afterWidth cursor rfl)
    (fun last reached _ nextAt => argumentWrite context (address + size) (intToLE size count) next last reached nextAt)

private def publishCollection (context : LiftLowerContext (core3 grow)) (width : AddrType) (ptr count : Nat) :
    (output : Stored.Lower.Output) → (output.Result → Session grow sig (Ret (core3 grow))) → Session grow sig (Ret (core3 grow))
  | .flat, next => next [ptrFlat width ptr, ptrFlat width count]
  | .memory address, next => storeListDescriptor context ptr count address >>= next

private theorem collection (context : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (area : AddrType → ABI.Layout) (elementStore : AddrType → Value.Val → Nat → Session grow sig Unit)
    (values : List Value.Val) (next : output.Result → Session grow sig (Ret (core3 grow)))
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (do
      let liveWidth ← ptrType context
      let ptr ← allocateListRange context (area liveWidth) values.length
      storeListIntoValidRangeWith (area liveWidth).size (elementStore liveWidth) values ptr
      publishCollection context width ptr values.length output next))
    (elements : ∀ liveWidth ptr (last : State grow sig) (reached : Cursor (E := core3 grow) (HostState sig)) tail,
      last.ctl = reached.control (storeListIntoValidRangeWith (area liveWidth).size (elementStore liveWidth) values ptr >>= tail) →
      StringPlanPair profile ready bindings callees last tail) :
    StringPlanPair profile ready bindings callees start next := by
  let publish := fun ptr : Nat => publishCollection context width ptr values.length output next
  let tail := fun liveWidth ptr =>
    storeListIntoValidRangeWith (area liveWidth).size (elementStore liveWidth) values ptr >>= fun _ => publish ptr
  let body := fun live =>
    let liveWidth := ptrTypeIn live context
    allocateListRange context (area liveWidth) values.length >>= tail liveWidth
  let afterWidth := { start with ctl := cursor.control (body start.store) }
  have readAt : start.ctl = cursor.control (.op .get body) := focused
  apply prependPair (middle := afterWidth) (.cons (.get readAt) (.refl _)) (.cons (.get readAt) (.refl _))
  let liveWidth := ptrTypeIn start.store context
  apply continuePair (listRange context (area liveWidth) values.length (tail liveWidth) choose afterWidth cursor rfl)
  intro last reached ptr nextAt
  apply continuePair (elements liveWidth ptr last reached (fun _ => publish ptr) nextAt)
  intro written reached _ published
  cases output with
  | flat => exact ⟨[], written, .refl _, .refl _, .complete reached _ published⟩
  | memory address => exact descriptor context ptr values.length address next written reached published

private theorem flatCollectionProgram (context : LiftLowerContext (core3 grow)) (width : AddrType)
    (element : Stored.TypeOf) (values : List Value.Val) (next : List FlatValue → Session grow sig (Ret (core3 grow))) :
    (lowerFlatAt .spec .none context width (.list values) (.list element) >>= next) = (do
      let liveWidth ← ptrType context
      let ptr ← allocateListRange context (ABI.layout liveWidth element) values.length
      storeListIntoValidRangeWith (ABI.layout liveWidth element).size (fun value address =>
        store .spec .none context value element address) values ptr
      next [ptrFlat width ptr, ptrFlat width values.length]) := by
  rw [lowerFlatAt]
  simp only [storeListIntoRange, storeListIntoRangeWith, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']

private theorem memoryCollectionProgram (context : LiftLowerContext (core3 grow)) (address : Nat)
    (element : Stored.TypeOf) (values : List Value.Val) (next : Unit → Session grow sig (Ret (core3 grow))) :
    (store .spec .none context (.list values) (.list element) address >>= next) = (do
      let liveWidth ← ptrType context
      let ptr ← allocateListRange context (ABI.layout liveWidth element) values.length
      storeListIntoValidRangeWith (ABI.layout liveWidth element).size (fun value slot =>
        store .spec .none context value element slot) values ptr
      storeListDescriptor context ptr values.length address >>= next) := by
  rw [store.eq_def]
  dsimp only
  simp only [storeListWith, Bool.false_eq_true, ite_false, storeListIntoRangeWith, Prog.bind_eq, Prog.bind_assoc,
    Prog.pure_eq, Prog.pure_bind']

private def mapEntryValue (entry : ArgumentField × ArgumentField) : Value.Val := .record [entry.1.value, entry.2.value]

private def mapEntryLayout (key : WIT.KeyType) (valueType : Stored.TypeOf) (width : AddrType) : ABI.Layout :=
  ABI.layout width (.record (ABI.mapEntryFields key valueType))

private def memoryMapEntry (context : LiftLowerContext (core3 grow)) (key : WIT.KeyType) (valueType : Stored.TypeOf)
    (width : AddrType) (entry : Value.Val) (address : Nat) : Session grow sig Unit :=
  match entry with
  | .record [keyValue, value] => do
    let keyLayout := ABI.primitiveLayout width key.toPrimitive
    let keySlot := ABI.alignTo address keyLayout.alignment
    storePrim .spec .none context key.toPrimitive keyValue keySlot
    store .spec .none context value valueType (ABI.alignTo (keySlot + keyLayout.size) (ABI.layout width valueType).alignment)
  | _ => storeMismatch

private theorem flatMapProgram (context : LiftLowerContext (core3 grow)) (width : AddrType) (key : WIT.KeyType)
    (valueType : Stored.TypeOf) (values : List Value.Val) (next : List FlatValue → Session grow sig (Ret (core3 grow))) :
    (lowerFlatAt .spec .none context width (.list values) (.map key valueType) >>= next) = (do
      let liveWidth ← ptrType context
      let ptr ← allocateListRange context (mapEntryLayout key valueType liveWidth) values.length
      storeListIntoValidRangeWith (mapEntryLayout key valueType liveWidth).size (fun value address =>
        store .spec .none context value (.record (ABI.mapEntryFields key valueType)) address) values ptr
      next [ptrFlat width ptr, ptrFlat width values.length]) := by
  rw [lowerFlatAt]
  simp only [storeListIntoRange, storeListIntoRangeWith, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind', mapEntryLayout]

private theorem memoryMapProgram (context : LiftLowerContext (core3 grow)) (address : Nat) (key : WIT.KeyType)
    (valueType : Stored.TypeOf) (values : List Value.Val) (next : Unit → Session grow sig (Ret (core3 grow))) :
    (store .spec .none context (.list values) (.map key valueType) address >>= next) = (do
      let liveWidth ← ptrType context
      let ptr ← allocateListRange context (mapEntryLayout key valueType liveWidth) values.length
      storeListIntoValidRangeWith (mapEntryLayout key valueType liveWidth).size
        (memoryMapEntry context key valueType liveWidth) values ptr
      storeListDescriptor context ptr values.length address >>= next) := by
  rw [store.eq_def]
  dsimp only
  simp only [storeListWith, Bool.false_eq_true, ite_false, storeListIntoRangeWith, Prog.bind_eq, Prog.bind_assoc,
    Prog.pure_eq, Prog.pure_bind', mapEntryLayout]
  rfl

private theorem indexedElements {Entry : Type} (valueOf : Entry → Value.Val)
    (storeElement : Value.Val → Nat → Session grow sig Unit) (stride base index : Nat)
    (members : List Entry) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (next : Unit → Session grow sig (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (Prog.forM ((members.map valueOf).zipIdx index)
      (fun item => storeElement item.1 (base + item.2 * stride)) >>= next))
    (child : ∀ entry ∈ members, ∀ (address : Nat) (last : State grow sig)
      (reached : Cursor (E := core3 grow) (HostState sig)) (tail : Unit → Session grow sig (Ret (core3 grow))),
      last.ctl = reached.control (storeElement (valueOf entry) address >>= tail) →
      StringPlanPair profile ready bindings callees last tail) :
    StringPlanPair profile ready bindings callees start next := by
  induction members generalizing index start cursor with
  | nil => exact ⟨[], start, .refl _, .refl _, .complete cursor () focused⟩
  | cons entry rest ih =>
    let tail := fun _ : Unit => Prog.forM ((rest.map valueOf).zipIdx (index + 1))
      (fun item => storeElement item.1 (base + item.2 * stride)) >>= next
    have atHead : start.ctl = cursor.control (storeElement (valueOf entry) (base + index * stride) >>= tail) := by
      simp only [List.map_cons, List.zipIdx_cons, Prog.forM, Prog.bind_eq, Prog.bind_assoc, tail] at focused ⊢
      exact focused
    exact continuePair (child entry (List.mem_cons_self ..) _ start cursor tail atHead)
      (fun last reached _ nextAt => ih (index + 1) last reached nextAt
        (fun member present => child member (List.mem_cons_of_mem _ present)))

private theorem identicalFlatSlots (types : List CoreType) (words : List FlatValue) :
    (coerceLowerSlots types types words : Session grow sig (List FlatValue × List CoreType)) =
      pure (words, types.drop words.length) := by
  induction types generalizing words with
  | nil => cases words <;> rfl
  | cons slot slots ih =>
    cases words with
    | nil => rfl
    | cons word words =>
      rw [coerceLowerSlots, ih]
      cases slot with
      | int kind => cases kind <;> rfl
      | float kind => cases kind <;> rfl

private theorem sumTag (context : LiftLowerContext (core3 grow)) (payloadAlign : AddrType → ABI.Alignment)
    (count tag ptr : Nat)
    (next : (AddrType × Nat) → Session grow sig (Ret (core3 grow))) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (do
      let width ← ptrType context
      let address ← storeVariantHead context count (payloadAlign width) tag ptr
      next (width, address))) :
    StringPlanPair profile ready bindings callees start next := by
  let address width := ABI.alignTo (ptr + discSize count) (payloadAlign width)
  let bytes := intToLE (discSize count) tag
  let body := fun live =>
    let width := ptrTypeIn live context
    writeMem context ptr bytes >>= fun _ => next (width, address width)
  let afterWidth := { start with ctl := cursor.control (body start.store) }
  have readAt : start.ctl = cursor.control (.op .get body) := by
    rw [focused]
    simp only [storeVariantHead, storeInt, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    rfl
  apply prependPair (middle := afterWidth) (.cons (.get readAt) (.refl _)) (.cons (.get readAt) (.refl _))
  let width := ptrTypeIn start.store context
  exact mapPair next (fun _ : Unit => (width, address width))
    (argumentWrite context ptr bytes _ afterWidth cursor rfl)

private theorem flatFieldNames (context : LiftLowerContext (core3 grow)) (width : AddrType)
    (values : List Value.Val) (types : List (String × Stored.TypeOf)) :
    (lowerFlatFields .spec .none context width values types : Session grow sig (List FlatValue)) =
      lowerFlatTypes .spec .none context width values (types.map Prod.snd) := by
  induction types generalizing values with
  | nil => cases values <;> rfl
  | cons named types ih =>
    obtain ⟨name, type⟩ := named
    cases values <;> simp only [List.map_cons, lowerFlatFields, lowerFlatTypes, ih]

private theorem storeFieldNames (context : LiftLowerContext (core3 grow))
    (values : List Value.Val) (types : List (String × Stored.TypeOf)) (address : Nat) :
    (storeFields .spec .none context values types address : Session grow sig Unit) =
      storeTuple .spec .none context values (types.map Prod.snd) address := by
  induction types generalizing values address with
  | nil => cases values <;> rw [Canon.storeFields.eq_def, storeTuple.eq_def] <;> rfl
  | cons named types ih =>
    obtain ⟨name, type⟩ := named
    cases values <;> rw [Canon.storeFields.eq_def, storeTuple.eq_def] <;> simp only [List.map_cons, ih]

private theorem recordMembersSize (members : List (String × ArgumentField)) :
    sizeOf (members.map Prod.snd) ≤ sizeOf members := by
  induction members with
  | nil => simp
  | cons member rest ih =>
    obtain ⟨name, field⟩ := member
    simp only [List.map_cons, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    omega

private theorem mapEntrySize {members : List (ArgumentField × ArgumentField)} {entry : ArgumentField × ArgumentField}
    (present : entry ∈ members) : sizeOf [entry.1, entry.2] ≤ sizeOf members := by
  induction members with
  | nil => simp at present
  | cons head tail ih =>
    rcases List.mem_cons.mp present with rfl | rest
    · obtain ⟨key, value⟩ := entry
      have positive : 0 < sizeOf tail := by cases tail <;> simp
      simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, List.nil.sizeOf_spec]
      omega
    · have smaller := ih rest
      simp only [List.cons.sizeOf_spec] at smaller ⊢
      omega

mutual

private theorem lowerArgument (context : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (next : output.Result → Session grow sig (Ret (core3 grow))) (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (field : ArgumentField) (typed : field.Valid) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (field.lower context width output >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  cases typed with
  | scalar arg =>
    cases output with
    | flat =>
      refine ⟨[], start, .refl _, .refl _, .complete cursor [arg.flat] ?_⟩
      rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type, flatScalar] at focused
      exact focused
    | memory address =>
      exact argumentWrite context address arg.bytes next start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          memoryScalar, Prog.bind_eq] using focused)
  | string value =>
    cases output with
    | flat =>
      exact argumentStringRead context width .flat value next choose start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          flat_argument_string, Prog.bind_eq] using focused)
    | memory address =>
      exact argumentStringRead context width (.memory address) value next choose start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          memory_argument_string context width, Prog.bind_eq] using focused)
  | @tuple members typed =>
    cases output with
    | flat =>
      exact directSequence context width next choose members typed start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          lowerFlatAt, Prog.bind_eq] using focused)
    | memory address =>
      exact spilledSequence context next choose members typed address start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          store.eq_def, Prog.bind_eq] using focused)
  | @record members typed =>
    have typedMembers : ∀ field ∈ members.map Prod.snd, ArgumentField.Valid field := by
      intro field present
      obtain ⟨member, inMembers, rfl⟩ := List.mem_map.mp present
      exact typed member inMembers
    cases output with
    | flat =>
      exact directSequence context width next choose (members.map Prod.snd) typedMembers start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          lowerFlatAt, flatFieldNames, List.map_map, Function.comp_def, Prog.bind_eq] using focused)
    | memory address =>
      exact spilledSequence context next choose (members.map Prod.snd) typedMembers address start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          store.eq_def, storeFieldNames, List.map_map, Function.comp_def, Prog.bind_eq] using focused)
  | @optionNone payloadShape _ =>
    cases output with
    | flat =>
      change List FlatValue → Session grow sig (Ret (core3 grow)) at next
      refine ⟨[], start, .refl _, .refl _, .complete cursor
        (i32Flat 0 :: (flatten width payloadShape.type).map Execution.Runtime.Value.zero) ?_⟩
      simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
        lowerFlatAt, Nat.zero_ne_one, not_false_eq_true, lowerFlatVariantWith, show 0 < 2 by decide, ite_true,
        optionWants, coerceLowerSlots, List.nil_append, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using focused
    | memory ptr =>
      change Unit → Session grow sig (Ret (core3 grow)) at next
      rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type, store.eq_def] at focused
      dsimp only at focused
      change start.ctl = cursor.control (Prog.bind _ next) at focused
      exact mapPair next (fun _ : AddrType × Nat => ())
        (sumTag context (fun width => ABI.maxCaseAlignment [none, some (ABI.layout width payloadShape.type)])
          2 0 ptr (fun _ => next ()) start cursor (by
          simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using focused))
  | @optionSome payload typed =>
    cases output with
    | flat =>
      change List FlatValue → Session grow sig (Ret (core3 grow)) at next
      let types := flatten width payload.type
      let wrap := fun words : List FlatValue =>
        i32Flat 1 :: (words ++ (types.drop words.length).map Execution.Runtime.Value.zero)
      apply mapPair next wrap
      apply lowerArgument context width .flat (fun words => next (wrap words)) choose payload typed start cursor
      rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type, lowerFlatAt, lowerFlatVariantWith,
        ite_eq_left (by decide : 1 < 2), optionWants] at focused
      simp only [Stored.Lower.Output.Result, ArgumentField.lower, Prog.bind_eq, Prog.bind_assoc,
        identicalFlatSlots, Prog.pure_eq, Prog.pure_bind', wrap, types] at focused ⊢
      exact focused
    | memory ptr =>
      change Unit → Session grow sig (Ret (core3 grow)) at next
      rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type, store.eq_def] at focused
      dsimp only at focused
      change start.ctl = cursor.control (Prog.bind _ next) at focused
      let tail := fun placed : AddrType × Nat => Prog.bind (payload.lower context placed.1 (.memory placed.2)) next
      have tagAt : start.ctl = cursor.control (do
          let liveWidth ← ptrType context
          let address ← storeVariantHead context 2
            (ABI.maxCaseAlignment [none, some (ABI.layout liveWidth payload.type)]) 1 ptr
          tail (liveWidth, address)) := by
        simp only [ArgumentField.lower, Prog.bind_eq, Prog.bind_assoc, tail] at focused ⊢
        exact focused
      exact continuePair (sumTag context (fun width => ABI.maxCaseAlignment [none, some (ABI.layout width payload.type)])
        2 1 ptr tail start cursor tagAt)
        (fun last reached placed nextAt => lowerArgument context placed.1 (.memory placed.2) next choose payload typed
          last reached nextAt)
  | @list element members _ typed schema =>
    cases output with
    | flat =>
      change List FlatValue → Session grow sig (Ret (core3 grow)) at next
      refine collection context width .flat (fun liveWidth => ABI.layout liveWidth element.type)
        (fun _ value address => store .spec .none context value element.type address)
        (members.map ArgumentField.value) next choose start cursor ?_ ?_
      · rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type] at focused
        exact focused.trans (congrArg cursor.control (flatCollectionProgram context width element.type
          (members.map ArgumentField.value) next))
      · intro liveWidth ptr last reached tail atElements
        apply indexedElements ArgumentField.value (fun value slot => store .spec .none context value element.type slot)
          (ABI.layout liveWidth element.type).size ptr 0 members last reached tail atElements
        intro child present slot last cursor after atChild
        apply lowerArgument context liveWidth (.memory slot) after choose child (typed child present) last cursor
        rw [ArgumentField.lower, schema child present]
        exact atChild
    | memory address =>
      change Unit → Session grow sig (Ret (core3 grow)) at next
      refine collection context width (.memory address) (fun liveWidth => ABI.layout liveWidth element.type)
        (fun _ value slot => store .spec .none context value element.type slot)
        (members.map ArgumentField.value) next choose start cursor ?_ ?_
      · rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type] at focused
        exact focused.trans (congrArg cursor.control (memoryCollectionProgram context address element.type
          (members.map ArgumentField.value) next))
      · intro liveWidth ptr last reached tail atElements
        apply indexedElements ArgumentField.value (fun value slot => store .spec .none context value element.type slot)
          (ABI.layout liveWidth element.type).size ptr 0 members last reached tail atElements
        intro child present slot last cursor after atChild
        apply lowerArgument context liveWidth (.memory slot) after choose child (typed child present) last cursor
        rw [ArgumentField.lower, schema child present]
        exact atChild
  | @map key keyShape valueShape members _ _ keySchema keysTyped valuesTyped keysMatch valuesMatch =>
    cases output with
    | flat =>
      change List FlatValue → Session grow sig (Ret (core3 grow)) at next
      let storeMember := fun value address => store (E := core3 grow) (σ := HostState sig) .spec .none context value
        (.record (ABI.mapEntryFields key valueShape.type)) address
      refine collection context width .flat (mapEntryLayout key valueShape.type) (fun _ => storeMember)
        (members.map mapEntryValue) next choose start cursor ?_ ?_
      · rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type] at focused
        exact focused.trans (congrArg cursor.control (flatMapProgram context width key valueShape.type
          (members.map mapEntryValue) next))
      · intro liveWidth ptr last reached tail atElements
        apply indexedElements mapEntryValue storeMember (mapEntryLayout key valueShape.type liveWidth).size ptr 0
          members last reached tail atElements
        intro entry present address last reached after atEntry
        have entryTyped : ∀ field ∈ [entry.1, entry.2], ArgumentField.Valid field := by
          intro field contained
          simp only [List.mem_cons, List.not_mem_nil, or_false] at contained
          rcases contained with rfl | rfl
          · exact keysTyped entry present
          · exact valuesTyped entry present
        have fieldsAt : storeMember (mapEntryValue entry) address = storeTuple .spec .none context
            [entry.1.value, entry.2.value] [.prim key.toPrimitive, valueShape.type] address := by
          dsimp only [storeMember, mapEntryValue]
          rw [store.eq_def]
          exact storeFieldNames context _ (ABI.mapEntryFields key valueShape.type) address
        apply spilledSequence context after choose [entry.1, entry.2] entryTyped address last reached
        simp only [List.map_cons, List.map_nil, keysMatch entry present, valuesMatch entry present, keySchema]
        exact atEntry.trans (congrArg (fun body : Session grow sig Unit => reached.control (body >>= after)) fieldsAt)
    | memory address =>
      change Unit → Session grow sig (Ret (core3 grow)) at next
      let storeMember := memoryMapEntry (sig := sig) context key valueShape.type
      refine collection context width (.memory address) (mapEntryLayout key valueShape.type) storeMember
        (members.map mapEntryValue) next choose start cursor ?_ ?_
      · rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type] at focused
        exact focused.trans (congrArg cursor.control (memoryMapProgram context address key valueShape.type
          (members.map mapEntryValue) next))
      · intro liveWidth ptr last reached tail atElements
        apply indexedElements mapEntryValue (storeMember liveWidth) (mapEntryLayout key valueShape.type liveWidth).size ptr 0
          members last reached tail atElements
        intro entry present entryAddress last reached after atEntry
        let keyLayout := ABI.primitiveLayout liveWidth key.toPrimitive
        let keySlot := ABI.alignTo entryAddress keyLayout.alignment
        let valueSlot := ABI.alignTo (keySlot + keyLayout.size) (ABI.layout liveWidth valueShape.type).alignment
        let afterKey := fun _ : Unit => entry.2.lower context liveWidth (.memory valueSlot) >>= after
        have keyAt : last.ctl = reached.control (entry.1.lower context liveWidth (.memory keySlot) >>= afterKey) := by
          have keyStore : entry.1.lower (sig := sig) context liveWidth (.memory keySlot) =
              storePrim .spec .none context key.toPrimitive entry.1.value keySlot := by
            rw [ArgumentField.lower, keysMatch entry present, keySchema, store.eq_def]
          rw [keyStore]
          simp only [storeMember, memoryMapEntry, mapEntryValue, ArgumentField.lower, valuesMatch entry present,
            Prog.bind_eq, Prog.bind_assoc, afterKey, valueSlot, keySlot, keyLayout] at atEntry ⊢
          exact atEntry
        exact continuePair (lowerArgument context liveWidth (.memory keySlot) afterKey choose entry.1
          (keysTyped entry present) last reached keyAt)
          (fun written remaining _ valueAt => lowerArgument context liveWidth (.memory valueSlot) after choose entry.2
            (valuesTyped entry present) written remaining valueAt)
termination_by sizeOf field
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals first
    | omega
    | have := recordMembersSize members; omega
    | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega
    | have smaller := mapEntrySize ‹_ ∈ _›
      simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec] at smaller
      omega

private theorem directSequence (context : LiftLowerContext (core3 grow)) (width : AddrType)
    (next : List FlatValue → Session grow sig (Ret (core3 grow))) (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (fields : List ArgumentField) (typed : ∀ field ∈ fields, ArgumentField.Valid field)
    (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (lowerFlatTypes .spec .none context width
      (fields.map ArgumentField.value) (fields.map ArgumentField.type) >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  cases fields with
  | nil =>
    refine ⟨[], start, .refl _, .refl _, .complete cursor [] ?_⟩
    simpa only [List.map_nil, lowerFlatTypes, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using focused
  | cons field rest =>
    let tail := fun words => lowerFlatTypes .spec .none context width (rest.map ArgumentField.value)
      (rest.map ArgumentField.type) >>= fun suffix => next (words ++ suffix)
    have atHead : start.ctl = cursor.control (field.lower context width .flat >>= tail) := by
      simpa only [Stored.Lower.Output.Result, List.map_cons, ArgumentField.lower, lowerFlatTypes, Prog.bind_eq, Prog.bind_assoc,
        Prog.pure_eq, Prog.pure_bind', tail] using focused
    exact continuePair (Field := List FlatValue)
      (lowerArgument context width .flat tail choose field (typed field (List.mem_cons_self ..)) start cursor atHead)
      (fun last reached words nextAt => mapPair next (words ++ ·)
        (directSequence context width (fun suffix => next (words ++ suffix)) choose rest
          (fun child present => typed child (List.mem_cons_of_mem _ present)) last reached nextAt))
termination_by sizeOf fields

private theorem spilledSequence (context : LiftLowerContext (core3 grow)) (next : Unit → Session grow sig (Ret (core3 grow)))
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) (fields : List ArgumentField)
    (typed : ∀ field ∈ fields, ArgumentField.Valid field)
    (ptr : Nat) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (storeTuple .spec .none context
      (fields.map ArgumentField.value) (fields.map ArgumentField.type) ptr >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  cases fields with
  | nil =>
    refine ⟨[], start, .refl _, .refl _, .complete cursor () ?_⟩
    simpa only [List.map_nil, storeTuple.eq_def, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using focused
  | cons field rest =>
    let address (width : AddrType) := ABI.alignTo ptr (ABI.layout width field.type).alignment
    let endPtr (width : AddrType) := address width + (ABI.layout width field.type).size
    let tail (width : AddrType) := fun _ : Unit => storeTuple .spec .none context
      (rest.map ArgumentField.value) (rest.map ArgumentField.type) (endPtr width) >>= next
    let body := fun live =>
      let width := ptrTypeIn live context
      field.lower context width (.memory (address width)) >>= tail width
    let afterWidth := { start with ctl := cursor.control (body start.store) }
    have readAt : start.ctl = cursor.control (.op .get body) := by
      rw [focused, List.map_cons, List.map_cons, storeTuple.eq_def]
      simp only [Prog.bind_eq, Prog.bind_assoc]
      rfl
    apply prependPair (middle := afterWidth) (.cons (.get readAt) (.refl _)) (.cons (.get readAt) (.refl _))
    let width := ptrTypeIn start.store context
    exact continuePair
      (lowerArgument context width (.memory (address width)) (tail width) choose field
        (typed field (List.mem_cons_self ..)) afterWidth cursor rfl)
      (fun last reached _ nextAt => spilledSequence context next choose rest
        (fun child present => typed child (List.mem_cons_of_mem _ present)) (endPtr width) last reached nextAt)
termination_by sizeOf fields

end

theorem directArguments {start reached : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned) (fields : List ArgumentField)
    (schema : args.types = fields.map ArgumentField.type) (input : returned.values = fields.map ArgumentField.value)
    (typed : ∀ field ∈ fields, ArgumentField.Valid field)
    (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees reached args.enter := by
  apply prependPair (Transition.lowerArgsReturn (impl := host bindings) returned).steps
    (Transition.lowerArgsReturn (impl := ComponentCall.hostWithComponent bindings callees) returned).steps
  apply prependPair (Transition.calleeDirect (impl := host bindings) args fits).steps
    (Transition.calleeDirect (impl := ComponentCall.hostWithComponent bindings callees) args fits).steps
  apply directSequence args.context args.width args.enter choose fields typed args.direct ⟨some site.thread, site.segments, site.rest⟩
  rw [CalleeArguments.direct, schema, input]
  rfl

theorem spilledArguments {start reached state : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    (result : CalleeSpillReturn args state) (fields : List ArgumentField) {memory size}
    (schema : args.types = fields.map ArgumentField.type) (input : returned.values = fields.map ArgumentField.value)
    (typed : ∀ field ∈ fields, ArgumentField.Valid field)
    (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
    (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
    (fits : result.pointer + args.layout.size ≤ size) (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees state (fun _ : Unit => args.enter [ptrFlat args.width result.pointer]) := by
  apply prependPair (Transition.calleePlaced (impl := host bindings) result aligned selected sized fits).steps
    (Transition.calleePlaced (impl := ComponentCall.hostWithComponent bindings callees) result aligned selected sized fits).steps
  apply spilledSequence args.context _ choose fields typed result.pointer result.writing ⟨some site.thread, result.segments, result.rest⟩
  rw [CalleeSpillReturn.writing, CalleeArguments.write, schema, input, store.eq_def]
  rfl

theorem stackfulEntryAt {start reached state : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
    (cursor : Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue)
    (focused : state.ctl = cursor.control (args.enter flat))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
    Steps profile ready dispatch state [.tau]
      { state with ctl := ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest } := by
  have call : args.enter flat = .op (.callCore args.callee flat) (stackfulTail args.task) := by
    simp only [CalleeArguments.enter, liftArgumentsTail, asyncMode, callback, Bool.not_true, Bool.false_eq_true, ite_false]
    rfl
  exact .cons (.callCore (focused.trans (congrArg cursor.control call))) (.refl _)

theorem enterStackful {start reached first : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
    {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none) :
    ∃ labels last, Steps profile ready (Dispatch.coreOnly ready bindings) first labels last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) first labels last ∧
      ((∃ (cursor : Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
        last.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest) ∨
        StringPlanStopped profile ready bindings first labels last) := by
  obtain ⟨labels, last, left, right, endAt⟩ := lowered
  cases endAt with
  | complete cursor result focused =>
    have enterLeft := stackfulEntryAt (profile := profile) (ready := ready) args cursor (words result) focused asyncMode callback
      (Dispatch.coreOnly ready bindings)
    have enterRight := stackfulEntryAt (profile := profile) (ready := ready) args cursor (words result) focused asyncMode callback
      (Dispatch.linked ready bindings callees)
    exact ⟨_, _, appendSteps left enterLeft, appendSteps right enterRight, .inl ⟨cursor, words result, rfl⟩⟩
  | trap reason => exact ⟨_, _, left, right, .inr (.trap reason)⟩
  | suspend alloc leading trailing mark atCall path closed =>
    exact ⟨_, _, left, right, .inr (.suspend alloc leading trailing mark atCall path closed)⟩

private theorem compatibleCore {entry reached : State grow sig} {labels}
    (path : Dispatch.Compatible profile ready bindings callees entry labels reached) :
    Steps profile ready (Dispatch.coreOnly ready bindings) entry labels reached := by
  induction path with
  | done => exact .refl _
  | next _ step _ tail => exact .cons step tail
  | liftedLookup focus lookup _ tail =>
    exact appendSteps (Dispatch.liftedLookup_steps (impl := host bindings) focus lookup) tail

private theorem bodySteps {entry reached : State grow sig} {labels}
    (body : StackfulBody profile ready bindings callees entry labels reached) :
    Steps profile ready (Dispatch.coreOnly ready bindings) entry labels reached ∧
    Steps profile ready (Dispatch.linked ready bindings callees) entry labels reached := by
  cases body with
  | core run => exact ⟨run, (Dispatch.Compatible.of_core run).steps⟩
  | closed run sites => exact ⟨run, (Dispatch.Compatible.of_closed run sites).steps⟩
  | classified sites => exact ⟨compatibleCore sites, sites.steps⟩

private theorem returnBoth (task : TaskId) {reached : State grow sig} (site : StackfulReturn reached)
    (sameTask : site.taskId = task) (records : StackfulReturnSite site) (empty : site.segments = []) :
    ∃ labels finish, Steps profile ready (Dispatch.coreOnly ready bindings) reached labels finish ∧
      Steps profile ready (Dispatch.linked ready bindings callees) reached labels finish ∧
      StackfulBodyEnd task reached labels finish := by
  cases guard : ((records.record.threads.erase site.thread).isEmpty && !decide (records.record.state = .resolved)) with
  | true =>
    obtain ⟨last, unresolved⟩ := Bool.and_eq_true_iff.mp guard
    have unresolved : records.record.state ≠ .resolved := by simpa using unresolved
    exact ⟨_, _, (Transition.stackfulUnresolved (impl := host bindings) site records.live records.implicitThread last unresolved).steps,
      (Transition.stackfulUnresolved (impl := ComponentCall.hostWithComponent bindings callees)
        site records.live records.implicitThread last unresolved).steps, .unresolved site sameTask records last unresolved⟩
  | false =>
    obtain ⟨registration, slot, inst, removed, threadLive, index, instanceLive, remove⟩ := records.registered guard
    let exit : StackfulExit site := ⟨records.record, registration, inst, slot, removed, records.live, records.implicitThread,
      by simpa only [decide_not] using guard, threadLive, index, instanceLive, remove⟩
    exact ⟨_, _, appendSteps (Transition.stackfulComplete (impl := host bindings) exit).steps
        (Transition.stackfulExit (impl := host bindings) exit empty).steps,
      appendSteps (Transition.stackfulComplete (impl := ComponentCall.hostWithComponent bindings callees) exit).steps
        (Transition.stackfulExit (impl := ComponentCall.hostWithComponent bindings callees) exit empty).steps,
      .exited sameTask exit⟩

theorem finishStackful {start reached first : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
    {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (select : ∀ (entry : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      StackfulBodyCut profile ready bindings callees args.task entry) :
    ∃ labels last, Steps profile ready (Dispatch.coreOnly ready bindings) first labels last ∧
      Steps profile ready (Dispatch.linked ready bindings callees) first labels last ∧
      StackfulWorkerEnd profile ready bindings first args.task args.callee labels last := by
  obtain ⟨leading, entry, left, right, outcome⟩ := enterStackful args words lowered asyncMode callback
  rcases outcome with ⟨cursor, flat, entered⟩ | stopped
  · cases select entry cursor flat entered with
    | «prefix» body =>
      obtain ⟨bodyLeft, bodyRight⟩ := bodySteps body
      exact ⟨_, _, appendSteps left (appendSteps bodyLeft (.refl _)), appendSteps right (appendSteps bodyRight (.refl _)),
        .body cursor flat left entered bodyLeft (.prefix _)⟩
    | returned body returnAt sameTask records empty =>
      obtain ⟨bodyLeft, bodyRight⟩ := bodySteps body
      obtain ⟨_, _, exitLeft, exitRight, endAt⟩ := returnBoth (profile := profile) (ready := ready) (bindings := bindings)
        (callees := callees) args.task returnAt sameTask records empty
      exact ⟨_, _, appendSteps left (appendSteps bodyLeft exitLeft), appendSteps right (appendSteps bodyRight exitRight),
        .body cursor flat left entered bodyLeft endAt⟩
  · exact ⟨_, _, left, right, .stopped stopped⟩

theorem finishWithDelivery {start reached first : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned)
    {Result : Type} (words : Result → List FlatValue)
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
      Steps profile ready (Dispatch.linked ready bindings callees) first (leading ++ trailing) last := by
  obtain ⟨_, _, left, right, endAt⟩ := finishStackful args words lowered asyncMode callback select
  obtain ⟨_, _, _, run, closed⟩ := delivery _ _ endAt
  have linked := run.rehost_delivery (reference := ComponentCall.hostWithComponent bindings callees) closed
  exact ⟨_, _, _, _, _, endAt, linked, appendSteps left run.steps, appendSteps right linked.steps⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan
