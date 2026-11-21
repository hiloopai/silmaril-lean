module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open PayloadPrefix (Cursor)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- A choice at the actual installed allocator occurrence. The suspended
case can stop immediately; choosing a return supplies the reached pop, not a
liveness requirement. Closure is only required through the chosen cuts. -/
inductive ArgumentAllocatorCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) {state : State grow sig} (alloc : ArgumentStringAllocation state) where
  | suspend (last : State grow sig) (labels : Trace grow sig) (mark : ReturnFrame.Occurrence.Location)
      (path : ReturnFrame.Occurrence.Prefix profile ready (Dispatch.coreOnly ready bindings)
        (alloc.installed ready bindings) (.active 0 0) labels last mark)
      (closed : Dispatch.ClosedThrough profile ready bindings (alloc.installed ready bindings) labels last)
  | returned (last : State grow sig) (labels : Trace grow sig)
      (path : ReturnFrame.Occurrence.Prefix profile ready (Dispatch.coreOnly ready bindings)
        (alloc.installed ready bindings) (.active 0 0) labels last (.active 0 0))
      (closed : Dispatch.ClosedThrough profile ready bindings (alloc.installed ready bindings) labels last)
      (cursor : Cursor (E := core3 grow) (HostState sig)) (answer : Ret (core3 grow))
      (next : ReturnFrame.Continuation (core3 grow) (HostState sig))
      (pop : last.ctl = { cursor with frames := .prog next :: cursor.frames }.control (.pure answer))
  | trapped (last : State grow sig) (labels : Trace grow sig) (reason : TrapReason)
      (path : Steps profile ready (Dispatch.coreOnly ready bindings)
        (alloc.installed ready bindings) (labels ++ [.trap reason]) last)
      (closed : Dispatch.ClosedThrough profile ready bindings
        (alloc.installed ready bindings) (labels ++ [.trap reason]) last)

abbrev ArgumentAllocatorSelection (grow : SingleThreaded.GrowOracle) (sig : Signature) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) :=
  ∀ {state : State grow sig} (alloc : ArgumentStringAllocation state), ArgumentAllocatorCut profile ready bindings alloc

/-- A finite string-plan trace reaches the real next continuation, ends at
a trap, or leaves a tracked allocator occurrence in flight. -/
inductive StringPlanEnd (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (start : State grow sig)
    {Result : Type} (next : Result → Session grow sig (Ret (core3 grow))) : Trace grow sig → State grow sig → Prop where
  | complete {labels last} (cursor : Cursor (E := core3 grow) (HostState sig)) (value : Result)
      (focused : last.ctl = cursor.control (next value)) : StringPlanEnd profile ready bindings start next labels last
  | trap {leading last} (reason : TrapReason) : StringPlanEnd profile ready bindings start next (leading ++ [.trap reason]) last
  | suspend {state last} (alloc : ArgumentStringAllocation state) (leading labels : Trace grow sig)
      (mark : ReturnFrame.Occurrence.Location)
      (reached : Steps profile ready (Dispatch.coreOnly ready bindings) start leading state)
      (path : ReturnFrame.Occurrence.Prefix profile ready (Dispatch.coreOnly ready bindings)
        (alloc.installed ready bindings) (.active 0 0) labels last mark)
      (closed : Dispatch.ClosedThrough profile ready bindings (alloc.installed ready bindings) labels last) :
      StringPlanEnd profile ready bindings start next (leading ++ .tau :: labels) last

def StringPlanPair (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (callees : List (Callee sig)) (start : State grow sig)
    {Result : Type} (next : Result → Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ labels last, Steps profile ready (Dispatch.coreOnly ready bindings) start labels last ∧
    Steps profile ready (Dispatch.linked ready bindings callees) start labels last ∧
    StringPlanEnd profile ready bindings start next labels last

def stringArgumentValues (values : List Value.StrVal) : List Value.Val := values.map .string

def stringArgumentTypes (values : List Value.StrVal) : List Stored.TypeOf := values.map (fun _ => .prim .string)

/-- The supported canonical argument trees. The same tree names the checked
shape and supplies the actual canonical value, including tuple arity. -/
inductive ArgumentField where
  | scalar (arg : DirectArgument)
  | string (value : Value.StrVal)
  | tuple (members : List ArgumentField)
  | record (members : List (String × ArgumentField))
  | optionNone (payloadShape : ArgumentField)
  | optionSome (payload : ArgumentField)
  | list (elementShape : ArgumentField) (members : List ArgumentField)

private theorem namedArgumentSize {members : List (String × ArgumentField)} {member : String × ArgumentField}
    (present : member ∈ members) : sizeOf member.2 < sizeOf members := by
  have smaller := List.sizeOf_lt_of_mem present
  obtain ⟨name, field⟩ := member
  simp only [Prod.mk.sizeOf_spec] at smaller ⊢
  omega

def ArgumentField.type : ArgumentField → Stored.TypeOf
  | .scalar arg => arg.type
  | .string _ => .prim .string
  | .tuple members => .tuple (members.map type)
  | .record members => .record (members.map fun member => (member.1, type member.2))
  | .optionNone payloadShape => .option (type payloadShape)
  | .optionSome payload => .option (type payload)
  | .list elementShape _ => .list (type elementShape)
termination_by field => sizeOf field
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega | have := namedArgumentSize ‹_ ∈ _›; omega

def ArgumentField.value : ArgumentField → Value.Val
  | .scalar arg => arg.value
  | .string value => .string value
  | .tuple members => .record (members.map value)
  | .record members => .record (members.map fun member => value member.2)
  | .optionNone _ => .variant 0 none
  | .optionSome payload => .variant 1 (some (value payload))
  | .list _ members => .list (members.map value)
termination_by field => sizeOf field
decreasing_by
  all_goals simp_wf
  all_goals first | have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega | have := namedArgumentSize ‹_ ∈ _›; omega

/-- Structural typing of the witness for a reached argument value. Collection
members carry the same schema, including when that schema itself allocates.
An empty collection still needs a supported element shape. -/
inductive ArgumentField.Valid : ArgumentField → Prop where
  | scalar (arg : DirectArgument) : Valid (.scalar arg)
  | string (value : Value.StrVal) : Valid (.string value)
  | tuple {members : List ArgumentField} (typed : ∀ child ∈ members, Valid child) : Valid (.tuple members)
  | record {members : List (String × ArgumentField)} (typed : ∀ child ∈ members, Valid child.2) : Valid (.record members)
  | optionNone {child : ArgumentField} (typed : Valid child) : Valid (.optionNone child)
  | optionSome {child : ArgumentField} (typed : Valid child) : Valid (.optionSome child)
  | list {shape : ArgumentField} {members : List ArgumentField} (shapeTyped : Valid shape)
      (typed : ∀ child ∈ members, Valid child) (schema : ∀ child ∈ members, child.type = shape.type) : Valid (.list shape members)

/-- The actual canonical lowering of a single argument at the selected output. -/
def ArgumentField.lower (context : LiftLowerContext (core3 grow)) (width : AddrType)
    (field : ArgumentField) (output : Stored.Lower.Output) : Session grow sig output.Result :=
  match output with
  | .flat => lowerFlatAt .spec .none context width field.value field.type
  | .memory address => store .spec .none context field.value field.type address

/-- The lowering stopped before Core entry: either a trap or an actual
suspended callback with its occurrence still live. -/
abbrev StringPlanStopped (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (start : State grow sig) (labels : Trace grow sig) (last : State grow sig) : Prop :=
  StringPlanEnd profile ready bindings start (fun unreachable : Empty => nomatch unreachable) labels last

/-- Pair only the selected finite body. A Core-only body needs no hook
contract. For other closed paths we check the reached dispatch sites; an
open path must give the site-level dispatcher classification. -/
inductive StackfulBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    State grow sig → Trace grow sig → State grow sig → Prop where
  | core {entry reached count}
      (path : Steps profile ready (Dispatch.coreOnly ready bindings) entry (List.replicate count .core) reached) :
      StackfulBody profile ready bindings callees entry (List.replicate count .core) reached
  | closed {entry reached labels}
      (path : Steps profile ready (Dispatch.coreOnly ready bindings) entry labels reached)
      (sites : Dispatch.ClosedThrough profile ready bindings entry labels reached) :
      StackfulBody profile ready bindings callees entry labels reached
  | classified {entry reached labels} (sites : Dispatch.Compatible profile ready bindings callees entry labels reached) :
      StackfulBody profile ready bindings callees entry labels reached

/-- The reached registration is needed only on the successful branch.
The canonical last-thread guard runs before it reads any thread slot. -/
structure StackfulReturnSite {reached : State grow sig} (site : StackfulReturn reached) where
  record : Task (core3 grow)
  live : reached.store.task? site.taskId = some record
  implicitThread : record.implicitThread = some site.thread
  registered : ((record.threads.erase site.thread).isEmpty && !decide (record.state = .resolved)) = false →
    ∃ (registration : Thread) (slot : Nat) (inst removed : InstState),
      reached.store.thread? site.thread = some registration ∧ registration.index = some slot ∧
      reached.store.inst? record.inst = some inst ∧ inst.removeThread? slot = some (site.thread, removed)

/-- Continue an actual body selection, or stop after any finite prefix. -/
inductive StackfulBodyCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (Callee sig)) (task : TaskId) (entry : State grow sig) where
  | prefix {labels reached} (body : StackfulBody profile ready bindings callees entry labels reached)
  | returned {labels reached} (body : StackfulBody profile ready bindings callees entry labels reached)
      (site : StackfulReturn reached) (sameTask : site.taskId = task)
      (records : StackfulReturnSite site) (empty : site.segments = [])

/-- The selected body cut is either left untouched or extended by the
actual return, unregistration/exit or unresolved-task trap. -/
inductive StackfulBodyEnd (task : TaskId) : State grow sig → Trace grow sig → State grow sig → Prop where
  | prefix (state : State grow sig) : StackfulBodyEnd task state [] state
  | exited {reached} {site : StackfulReturn reached} (sameTask : site.taskId = task) (exit : StackfulExit site) :
      StackfulBodyEnd task reached (exit.labels ++ [.tau]) exit.finished
  | unresolved {reached} (site : StackfulReturn reached) (sameTask : site.taskId = task)
      (records : StackfulReturnSite site) (last : (records.record.threads.erase site.thread).isEmpty = true)
      (unresolved : records.record.state ≠ .resolved) :
      StackfulBodyEnd task reached [.tau, .tau, .tau, .trap .taskNotResolved] (StepDefs.trapCfg reached)

/-- Record the entry and body boundaries without merging a suspended
lowering with a callee that has already entered. -/
inductive StackfulWorkerEnd (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (first : State grow sig) (task : TaskId) (callee : (core3 grow).FuncAddr) : Trace grow sig → State grow sig → Prop where
  | stopped {labels last} (stop : StringPlanStopped profile ready bindings first labels last) :
      StackfulWorkerEnd profile ready bindings first task callee labels last
  | body {entry reached finish leading labels trailing} (cursor : Cursor (E := core3 grow) (HostState sig))
      (words : List FlatValue)
      (entryPath : Steps profile ready (Dispatch.coreOnly ready bindings) first leading entry)
      (entered : entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke callee words) (stackfulTail task), cursor.frames⟩ :: cursor.rest)
      (bodyPath : Steps profile ready (Dispatch.coreOnly ready bindings) entry labels reached)
      (endAt : StackfulBodyEnd task reached trailing finish) :
      StackfulWorkerEnd profile ready bindings first task callee (leading ++ (labels ++ trailing)) finish

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
