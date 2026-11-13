-- Word-granular memory models from an earlier Silmaril development; namespaces
-- `Silmaril.Memory{,.SC,.TSO}` kept. Re-exported by `Silmaril.X86.MemoryModel.Tso`.
module

/-! # Observable memory events and finite interleaved executions -/

@[expose] public section

namespace Silmaril.Memory

universe u v w x

/-- An observable event includes the value returned by a load. -/
inductive Event (Tid : Type u) (Addr : Type v) (Val : Type w) where
  | load (thread : Tid) (address : Addr) (value : Val)
  | store (thread : Tid) (address : Addr) (value : Val)
  | fence (thread : Tid)
  deriving DecidableEq, Repr

def Event.thread {Tid : Type u} {Addr : Type v} {Val : Type w} : Event Tid Addr Val → Tid
  | .load t _ _ => t
  | .store t _ _ => t
  | .fence t => t

/-- Finite paths of a memory system; internal propagation may be incorporated
in the supplied observable transition relation. -/
inductive Execution {State : Type u} {Label : Type v}
    (step : State → Label → State → Prop) : State → List Label → State → Prop
  | nil (s) : Execution step s [] s
  | cons {s t u e es} : step s e t → Execution step t es u → Execution step s (e :: es) u

namespace Execution

variable {State : Type u} {Label : Type v} {step : State → Label → State → Prop}

theorem append {s t u : State} {xs ys : List Label}
    (h : Execution step s xs t) (h' : Execution step t ys u) :
    Execution step s (xs ++ ys) u := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h (ih h')

/-- Pointwise simulation lifts to every finite observable trace. -/
theorem map {Target : Type w} {step' : Target → Label → Target → Prop}
    (f : State → Target)
    (sim : ∀ {s e t}, step s e t → step' (f s) e (f t))
    {s t : State} {es : List Label} (h : Execution step s es t) :
    Execution step' (f s) es (f t) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (sim h) ih

end Execution

/-- All merges of two traces, preserving each trace's program order. -/
def shuffles {α : Type u} : List α → List α → List (List α)
  | [], ys => [ys]
  | xs, [] => [xs]
  | x :: xs, y :: ys =>
      (shuffles xs (y :: ys)).map (x :: ·) ++ (shuffles (x :: xs) ys).map (y :: ·)
  termination_by xs ys => xs.length + ys.length

/-- A binary parallel outcome consists of a legal program-order-preserving
interleaving accepted by the memory system. -/
def Concurrent {State : Type u} {Label : Type v}
    (step : State → Label → State → Prop) (initial : State) (left right : List Label) : Prop :=
  ∃ trace ∈ shuffles left right, ∃ final, Execution step initial trace final

end Silmaril.Memory
