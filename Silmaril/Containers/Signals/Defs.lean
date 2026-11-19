module

public import Silmaril.Containers.Posix.Defs
public import Silmaril.Containers.Behaviour.Defs

/-! # Experimental single-process signal protocol

Arrival queues a signal even while masked. Delivery, handler entry, handler return and default
termination are distinct actions. An in-flight typed request can return EINTR, return a partial
response through the normal typed return, or remain in flight under an explicit restart policy.
Invalid/unsupported transitions produce `undefined unmodeled`; ordinary default signal
termination is defined. This is an abstract one-handler-at-a-time model, not ELF verification. -/

@[expose] public section
namespace Silmaril.Containers.Signals

inductive Disposition where
  | terminate
  | ignore
  | handler (id : Nat)
  deriving DecidableEq, Repr

inductive Interruption where
  | eintr
  | restart
  deriving DecidableEq, Repr

structure State where
  pending : List Nat := []
  masked : Nat → Bool := fun _ => false
  registered : Nat → Disposition := fun _ => .terminate
  delivering : Option Nat := none
  handling : Option (Nat × Nat) := none
  policy : Interruption := .eintr
  inflight : Option Posix.Req := none
  calls : List Posix.Event := []
  effects : List Ev := []
  stop : Option Stop := none

inductive Action where
  | register (signal : Nat) (disposition : Disposition)
  | mask (signal : Nat) (blocked : Bool)
  | arrive (signal : Nat)
  | deliver (signal : Nat)
  | enter
  | returnHandler
  | defaultTerminate
  | ignore
  | call (req : Posix.Req)
  | returned (req : Posix.Req) (reply : Posix.Response req)
  | interrupted
  | restart
  | effect (e : Ev)
  | exit (code : UInt8)
  | fault (reason : UB)

/-- A response is logged separately from the coarse application effects. A descriptor-level
interpreter such as `Posix.readStep/writeStep` must validate it against its own resource state. -/
def step (s : State) (action : Action) : State :=
  if s.stop.isSome then s else
  let bad := { s with stop := some (.undefined .unmodeled) }
  match action with
  | .register sig d => { s with registered := fun n => if n = sig then d else s.registered n }
  | .mask sig b => { s with masked := fun n => if n = sig then b else s.masked n }
  | .arrive sig => { s with pending := s.pending ++ [sig] }
  | .deliver sig =>
    if sig ∈ s.pending ∧ s.masked sig = false ∧ s.handling = none ∧ s.delivering = none then
      { s with pending := s.pending.erase sig, delivering := some sig }
    else bad
  | .enter => match s.delivering with
    | some sig => match s.registered sig with
      | .handler id => { s with delivering := none, handling := some (sig, id) }
      | _ => bad
    | none => bad
  | .returnHandler => if s.handling.isSome then { s with handling := none } else bad
  | .defaultTerminate => match s.delivering with
    | some sig => if s.registered sig = .terminate then
        { s with stop := some (.signaled sig), delivering := none } else bad
    | none => bad
  | .ignore => match s.delivering with
    | some sig => if s.registered sig = .ignore then { s with delivering := none } else bad
    | none => bad
  | .call req => if s.inflight = none then
      { s with inflight := some req, calls := s.calls ++ [.call req] } else bad
  | .returned req reply => if s.inflight = some req then
      { s with inflight := none, calls := s.calls ++ [.returned req reply] } else bad
  | .interrupted => match s.inflight with
    | some req => if s.policy = .eintr ∧ s.handling.isSome then
        { s with inflight := none, calls := s.calls ++ [.returned req (Posix.interrupted req)] }
      else bad
    | none => bad
  | .restart => if s.policy = .restart ∧ s.inflight.isSome ∧ s.handling = none then s else bad
  | .effect e => { s with effects := s.effects ++ [e] }
  | .exit code => if s.inflight = none ∧ s.handling = none ∧ s.delivering = none then
      { s with stop := some (.exited code) } else bad
  | .fault reason => { s with stop := some (.undefined reason) }

def execute (s : State) (actions : List Action) : State := actions.foldl step s

/-- An unfinished script is waiting for further model/environment actions, not proven to exit. -/
def observe (s : State) : Beh Ev :=
  match s.stop with
  | some stop => .done s.effects stop
  | none => .blocked s.effects

/-- Restrict deliveries in the semantics. Erasing delivery letters is different: handler
effects do not disappear and handler-entry preconditions can become invalid. -/
def NoDelivery (actions : List Action) : Prop :=
  ∀ a ∈ actions, ∀ sig, a ≠ .deliver sig

end Silmaril.Containers.Signals
