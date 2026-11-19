module

public import Silmaril.Cerberus.TV.Behaviour.Defs
public import Silmaril.Cerberus.Core.Explore.Defs

/-!
# Exhaustive bounded exploration of a closed program's endings

`Closed.explore P bounds` enumerates the runs of the Core LTS from the startup state depth first,
over every successor `Core.Dynamics.successors` lists (complete and sound for the transition
relation: `Core.Dynamics.successors_correct`), and collects every ending it reaches: the halted
outcome and the stdout. It keeps no visited set.

The result says how far it can be trusted:

* every collected ending is an ending of the program (`Closed.explore_sound` in `Thms`), whatever
  the bounds;
* when `limited` is false (no path reached `bounds.depth` transitions, and `bounds.budget` stack
  entries sufficed), every ending of the program was collected (`Closed.explore_complete`) and the
  program has no infinite run (`Closed.explore_terminates`): every run has at most `bounds.depth`
  transitions;
* when moreover `stuck` is false, no reachable state is stuck (`Closed.explore_noStuck`).

So a bounded exploration decides the endings of a program only when it is exhaustive, and an
exhaustive exploration exists only for programs whose every run is finite: a program with an
infinite run is always `limited`. This is a finite enumeration of a finite execution tree, not of
C behaviours in general.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.Cerberus.Core.Dynamics

/-- Exploration bounds: `depth` transitions on one path, `budget` stack entries in all. -/
structure Bounds where
  depth : Nat := 100000
  budget : Nat := 2000000
  deriving Repr

/-- What an exploration found. -/
structure Leaves where
  /-- The endings reached (outcome and stdout), most recent first, with repetitions. -/
  ends : List (Outcome × String) := []
  /-- A path reached the depth bound, or the budget ran out with states left to visit. -/
  limited : Bool := false
  /-- A state that is not halted had no successor. -/
  stuck : Bool := false
  /-- Transitions taken. -/
  steps : Nat := 0

/-- Depth-first exploration. Stack entries carry the remaining per-path depth. -/
def explore (file : Program) (labels : Labels) :
    Nat → List (Nat × State) → Leaves → Leaves
  | 0, stack, acc => if stack.isEmpty then acc else { acc with limited := true }
  | _ + 1, [], acc => acc
  | budget + 1, (depth, s) :: rest, acc =>
      match s.control with
      | .halt o => explore file labels budget rest
          { acc with ends := (o, s.memory.stdout) :: acc.ends }
      | _ => match depth with
        | 0 => explore file labels budget rest { acc with limited := true }
        | d + 1 =>
            match successors file labels s with
            | [] => explore file labels budget rest { acc with stuck := true }
            | p :: ps => explore file labels budget
                ((p :: ps).map (fun q => (d, q.2)) ++ rest) { acc with steps := acc.steps + 1 }

/-- Explore a closed program from its startup state. A startup failure is its only ending. -/
def Closed.explore (P : Closed) (bounds : Bounds := {}) : Leaves :=
  match P.start with
  | .error o => { ends := [(o, "")] }
  | .ok (s0, labels) => TV.explore P.file labels bounds.budget [(bounds.depth, s0)] {}

/-- Whether some collected ending is a gap of the dynamics. -/
def Leaves.gap (L : Leaves) : Bool :=
  L.ends.any fun e => Outcome.isGap e.1

/-- Whether some collected ending is undefined behaviour. -/
def Leaves.ub (L : Leaves) : Bool :=
  L.ends.any fun e => Outcome.isUB e.1

end Silmaril.Cerberus.TV
