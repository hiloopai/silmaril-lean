module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
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

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.StringPlan
