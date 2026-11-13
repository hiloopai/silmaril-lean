module

public import Silmaril.Cerberus.Core.Outcome.Defs
public import Silmaril.Semantics.CPort.Foundations.Operational.BreadthFirst.Defs

/-! Finite outcome-set exploration of the Core LTS. The FIFO explorer is the
shared operational utility. No scheduling choice is selected or discarded here.
A nonempty queue or a live state at depth zero prevents a completeness claim. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

def responseTransitions (mem : Mem.Concrete.State) (r : Request) : List (Label × State) :=
  (responses mem r).map fun p => (p.action, p.after)

/-- The executable response list contains exactly the response relation. -/
theorem responseTransitions_correct (mem : Mem.Concrete.State) (r : Request)
    (a : Label) (t : State) :
    (a, t) ∈ responseTransitions mem r ↔ Respond mem r a t := by
  constructor
  · intro h
    obtain ⟨p, _, equal⟩ := List.mem_map.mp h
    cases equal
    exact p.valid
  · intro h
    cases h <;> try (solve | simp [responseTransitions, responses])
    all_goals
      rename_i c k choices member
      cases choices with
      | nil => simp at member
      | cons x xs =>
          unfold responseTransitions
          simp only [responses, List.map_map]
          exact List.mem_map.mpr ⟨⟨(c, k), member⟩, List.mem_attach _ _, rfl⟩

def successors (file : Program) (labels : Labels) (s : State) : List (Label × State) :=
  match s.control with
  | .halt _ => []
  | _ => responseTransitions s.memory (request file labels s)

/-- The outcome explorer uses a complete enumerator of Dynamics.Step. -/
theorem successors_correct (file : Program) (labels : Labels) (s : State)
    (a : Label) (t : State) :
    (a, t) ∈ successors file labels s ↔ (lts file labels).Tr s a t := by
  cases h : s.control with
  | halt o =>
      simp only [successors, h, List.not_mem_nil, false_iff]
      intro step
      cases step with
      | respond live _ => exact live o h
  | _ =>
      simp only [successors, h]
      rw [responseTransitions_correct]
      constructor
      · intro response
        exact .respond (by intro o equal; rw [h] at equal; cases equal) response
      · intro step
        cases step with
        | respond _ response => exact response

def enumerator (file : Program) (labels : Labels) : Silmaril.Operational.Enumerator (lts file labels) :=
  ⟨successors file labels, successors_correct file labels⟩

/-- Depth is carried by queue nodes so a total state budget and a per-path
transition budget are independent. Halted nodes remain observable at depth zero. -/
def explorationChildren (file : Program) (labels : Labels) : Nat × State → List (Nat × State)
  | (0, _) => []
  | (fuel+1, s) => (enumerator file labels).next s |>.map fun (_, t) => (fuel, t)

structure OutcomeSet where
  outcomes : List Observation
  complete : Bool
  visited : Nat
  pending : Nat
  depthLimited : Bool

/-- Exhaust the finite execution tree or explicitly report which budget stopped
it. Duplicate states are retained, avoiding any approximation of memory equality. -/
def exploreOutcomes (file : Program) (labels : Labels) (fuel stateBudget : Nat)
    (start : State) : OutcomeSet :=
  let (visited, pending) := Silmaril.Operational.BreadthFirst.advance
    (explorationChildren file labels) stateBudget [(fuel, start)]
  let outcomes := visited.filterMap fun (_, s) => match s.control with
    | .halt o => some {observation (some o) with stdout := s.memory.stdout}
    | _ => none
  let depthLimited := visited.any fun (fuel, s) => match s.control with
    | .halt _ => false
    | _ => fuel == 0
  ⟨outcomes.eraseDups, pending.isEmpty && !depthLimited,
    visited.length, pending.length, depthLimited⟩

end Silmaril.Cerberus.Core.Dynamics
