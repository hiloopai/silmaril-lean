module

public import Silmaril.Cerberus.Core.Forced.Thms

/-! Actual call-free administrative request traces. Requests are uniform in an
external continuation, so interleave composition retains real scheduling and
memory-update behavior without assuming an operand's successful execution. -/
@[expose] public section
namespace Silmaril.Cerberus.Core.Administrative
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- These controls can be wrapped as an ordinary interleave child. -/
def unwrapped : Control → Bool
  | .halt _ | .jumping _ _ _ | .raise _ => false
  | _ => true

/-- Actual scheduling predicates on the child's own control and continuation. -/
structure Plain (state : Dynamics.State) : Prop where
  unwrapped : unwrapped state.control = true
  callfree : controlHasCCall state.control state.stack = false
  inactive : activeCall state.control state.stack = false

/-- A child has not yet reached the scheduler's value/annotations completion
case. Targets may be complete; each outgoing administrative edge records this
fact only at its source. -/
def NotDone (state : Dynamics.State) : Prop :=
  ∀ value accesses, state.control = .value value → annotationsOnly state.stack = some accesses → False

/-- Append the external continuation without changing the child state. -/
def extend (state : Dynamics.State) (outer : List Frame) : Dynamics.State :=
  {state with stack := state.stack ++ outer}

/-- A single real non-scheduled request, uniformly under any external frames.
Location updates are retained as genuine updates rather than erased. -/
inductive Edge (file : Program) (labels : Labels) : Dynamics.State → Dynamics.State → Prop where
  | next {source : Dynamics.State} {control : Control} {frames : List Frame}
      (sourcePlain : Plain source) (sourceRunning : NotDone source) (targetPlain : Plain ⟨control, frames, source.memory⟩)
      (requested : ∀ outer, requestAux file labels source.memory source.control (source.stack ++ outer) false =
        .next control (frames ++ outer)) : Edge file labels source ⟨control, frames, source.memory⟩
  | choose {source : Dynamics.State} {control : Control} {frames : List Frame}
      (sourcePlain : Plain source) (sourceRunning : NotDone source) (targetPlain : Plain ⟨control, frames, source.memory⟩)
      (requested : ∀ outer, requestAux file labels source.memory source.control (source.stack ++ outer) false =
        .choose [(control, frames ++ outer)]) : Edge file labels source ⟨control, frames, source.memory⟩
  | update {source : Dynamics.State} {control : Control} {frames : List Frame} {memory : Mem.Concrete.State}
      (sourcePlain : Plain source) (sourceRunning : NotDone source) (targetPlain : Plain ⟨control, frames, memory⟩)
      (requested : ∀ outer, requestAux file labels source.memory source.control (source.stack ++ outer) false =
        .update memory control (frames ++ outer)) : Edge file labels source ⟨control, frames, memory⟩

/-- Finite compositional actual administrative traces, including both endpoint
scheduling facts. The final source theorem derives these from syntax. -/
inductive Path (file : Program) (labels : Labels) : Dynamics.State → Dynamics.State → Prop where
  | refl {state} (plain : Plain state) : Path file labels state state
  | cons {source next target} (edge : Edge file labels source next)
      (tail : Path file labels next target) : Path file labels source target

/-- The actual right-most operand is first in administrative priority. -/
def pair (leftControl : Control) (leftFrames : List Frame) (right : Dynamics.State) : Dynamics.State :=
  ⟨.interleave [] [(0, leftControl, leftFrames), (1, right.control, right.stack)], [], right.memory⟩

/-- One active operand remains after its right sibling has completed. -/
def single (done : List (Nat × Val × List Access)) (child : Dynamics.State) : Dynamics.State :=
  ⟨.interleave done [(0, child.control, child.stack)], [], child.memory⟩

end Silmaril.Cerberus.Core.Administrative
