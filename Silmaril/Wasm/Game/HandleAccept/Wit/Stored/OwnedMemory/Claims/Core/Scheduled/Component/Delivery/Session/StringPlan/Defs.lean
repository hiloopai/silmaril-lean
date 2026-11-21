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

/-- The lowering stopped before Core entry: either a trap or an actual
suspended callback with its occurrence still live. -/
abbrev StringPlanStopped (profile : ProfileKind) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (start : State grow sig) (labels : Trace grow sig) (last : State grow sig) : Prop :=
  StringPlanEnd profile ready bindings start (fun unreachable : Empty => nomatch unreachable) labels last

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.ComponentCall.Delivery.FiniteSession
