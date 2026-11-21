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
      cases choose alloc with
      | suspend last trailing mark path closed =>
        obtain ⟨callLeft, callRight, _⟩ := alloc.linked_prefix (callees := callees) path closed
        exact ⟨_, _, appendSteps left.steps callLeft, appendSteps right.steps callRight,
          .suspend alloc labels trailing mark left.steps path closed⟩
      | returned last trailing path closed reached answer resume pop =>
        obtain ⟨popLeft, popRight⟩ := alloc.linked_return (callees := callees) path closed reached answer pop
        by_cases valid : ∃ pointer, answer = .nat pointer
        · obtain ⟨pointer, rfl⟩ := valid
          exact prependPair (appendSteps left.steps popLeft) (appendSteps right.steps popRight)
            (walk context width output plan next choose pointer residual (alloc.resumed last reached (.nat pointer)) reached rfl)
        · have focused := invalidAnswer alloc last reached answer valid
          exact ⟨_, _, appendSteps (appendSteps left.steps popLeft) (.cons (.trap focused) (.refl _)),
            appendSteps (appendSteps right.steps popRight) (.cons (.trap focused) (.refl _)), .trap _⟩
      | trapped last trailing reason path closed =>
        obtain ⟨callLeft, callRight⟩ := alloc.linked_steps (callees := callees) path closed
        refine ⟨_, _, appendSteps left.steps callLeft, appendSteps right.steps callRight, ?_⟩
        simpa only [List.append_assoc, List.cons_append] using
          (StringPlanEnd.trap (profile := profile) (ready := ready) (bindings := bindings) (start := start) (next := next)
            (last := last) (leading := labels ++ .tau :: trailing) reason)
termination_by steps.length

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

private theorem argumentScalarWrite (context : LiftLowerContext (core3 grow)) (arg : DirectArgument) (address : Nat)
    (next : Unit → Session grow sig (Ret (core3 grow))) (start : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (writeMem context address arg.bytes >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  obtain ⟨_, result, _, observed, left, right, _⟩ := PayloadPrefix.write_cut_between
    (profile := profile) (ready := ready) (dispatch := Dispatch.coreOnly ready bindings)
    (reference := Dispatch.linked ready bindings callees) context address arg.bytes start start cursor cursor next next rfl focused focused
  cases result with
  | ok written => exact ⟨_, _, left.steps, right.steps, .complete cursor written rfl⟩
  | error reason =>
    obtain ⟨count, rfl⟩ := observed
    exact ⟨_, _, left.steps, right.steps, .trap reason⟩

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

mutual

private theorem lowerArgument (context : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (next : output.Result → Session grow sig (Ret (core3 grow))) (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (field : ArgumentField) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (focused : start.ctl = cursor.control (field.lower context width output >>= next)) :
    StringPlanPair profile ready bindings callees start next := by
  cases field with
  | scalar arg =>
    cases output with
    | flat =>
      refine ⟨[], start, .refl _, .refl _, .complete cursor [arg.flat] ?_⟩
      rw [ArgumentField.lower, ArgumentField.value, ArgumentField.type, flatScalar] at focused
      exact focused
    | memory address =>
      exact argumentScalarWrite context arg address next start cursor (by
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
  | tuple members =>
    cases output with
    | flat =>
      exact directSequence context width next choose members start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          lowerFlatAt, Prog.bind_eq] using focused)
    | memory address =>
      exact spilledSequence context next choose members address start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          store.eq_def, Prog.bind_eq] using focused)
  | record members =>
    cases output with
    | flat =>
      exact directSequence context width next choose (members.map Prod.snd) start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          lowerFlatAt, flatFieldNames, List.map_map, Function.comp_def, Prog.bind_eq] using focused)
    | memory address =>
      exact spilledSequence context next choose (members.map Prod.snd) address start cursor (by
        simpa only [Stored.Lower.Output.Result, ArgumentField.lower, ArgumentField.value, ArgumentField.type,
          store.eq_def, storeFieldNames, List.map_map, Function.comp_def, Prog.bind_eq] using focused)
termination_by sizeOf field
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals first | omega | have := recordMembersSize members; omega

private theorem directSequence (context : LiftLowerContext (core3 grow)) (width : AddrType)
    (next : List FlatValue → Session grow sig (Ret (core3 grow))) (choose : ArgumentAllocatorSelection grow sig profile ready bindings)
    (fields : List ArgumentField) (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
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
    exact continuePair (Field := List FlatValue) (lowerArgument context width .flat tail choose field start cursor atHead)
      (fun last reached words nextAt => mapPair next (words ++ ·)
        (directSequence context width (fun suffix => next (words ++ suffix)) choose rest last reached nextAt))
termination_by sizeOf fields

private theorem spilledSequence (context : LiftLowerContext (core3 grow)) (next : Unit → Session grow sig (Ret (core3 grow)))
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) (fields : List ArgumentField)
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
    exact continuePair (lowerArgument context width (.memory (address width)) (tail width) choose field afterWidth cursor rfl)
      (fun last reached _ nextAt => spilledSequence context next choose rest (endPtr width) last reached nextAt)
termination_by sizeOf fields

end

theorem directArguments {start reached : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} (args : CalleeArguments returned) (fields : List ArgumentField)
    (schema : args.types = fields.map ArgumentField.type) (input : returned.values = fields.map ArgumentField.value)
    (fits : (ABI.flattenTypes args.width args.types).length ≤ ABI.maxFlatParams)
    (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees reached args.enter := by
  apply prependPair (Transition.lowerArgsReturn (impl := host bindings) returned).steps
    (Transition.lowerArgsReturn (impl := ComponentCall.hostWithComponent bindings callees) returned).steps
  apply prependPair (Transition.calleeDirect (impl := host bindings) args fits).steps
    (Transition.calleeDirect (impl := ComponentCall.hostWithComponent bindings callees) args fits).steps
  apply directSequence args.context args.width args.enter choose fields args.direct ⟨some site.thread, site.segments, site.rest⟩
  rw [CalleeArguments.direct, schema, input]
  rfl

theorem spilledArguments {start reached state : State grow sig} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {args : CalleeArguments returned}
    (result : CalleeSpillReturn args state) (fields : List ArgumentField) {memory size}
    (schema : args.types = fields.map ArgumentField.type) (input : returned.values = fields.map ArgumentField.value)
    (aligned : result.pointer = ABI.alignTo result.pointer args.layout.alignment)
    (selected : args.context.opts.memory = some memory) (sized : (core3 grow).memSize? state.store.core memory = some size)
    (fits : result.pointer + args.layout.size ≤ size) (choose : ArgumentAllocatorSelection grow sig profile ready bindings) :
    StringPlanPair profile ready bindings callees state (fun _ : Unit => args.enter [ptrFlat args.width result.pointer]) := by
  apply prependPair (Transition.calleePlaced (impl := host bindings) result aligned selected sized fits).steps
    (Transition.calleePlaced (impl := ComponentCall.hostWithComponent bindings callees) result aligned selected sized fits).steps
  apply spilledSequence args.context _ choose fields result.pointer result.writing ⟨some site.thread, result.segments, result.rest⟩
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
