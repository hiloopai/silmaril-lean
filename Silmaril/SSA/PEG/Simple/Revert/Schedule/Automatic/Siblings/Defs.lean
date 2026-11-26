module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions.Defs

/-! # Infer cut and export anchors for sequential parentless PEG loops -/

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Siblings

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

inductive Failure where
  | invalidRank
  | noLoops
  | nestedKey (key : Nat)
  | dependencyCycle
  | coverage
  | missingExport (key : Nat)
  | iterationValue (row : Nat)
  | checkedCuts (reason : Cuts.Failure)
  deriving DecidableEq, Repr

private def fromRegions : Regions.Failure → Failure
  | .invalidRank => .invalidRank
  | .noLoops => .noLoops
  | .dependencyCycle => .dependencyCycle
  | .missingExport key => .missingExport key
  | .iterationValue row => .iterationValue row
  | .checkedCuts reason => .checkedCuts reason
  | _ => .coverage

/-- The original sibling entry retains its parentless restriction. -/
def inferBoundaries (g : Graph P params results n l) : Except Failure (List (Cuts.Boundary g)) :=
  if let some key := (Regions.activeKeys g).find? (fun key => (g.forest.parent key).isSome) then
    .error (.nestedKey key.val)
  else
    (Regions.inferBoundaries g).mapError fromRegions

/-- Infer cuts from a typed graph and use the existing leaf and schedule
checkers. Rank admission covers the original table. The search budget
is passed to the shared fixed-cut order search. -/
def discover [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : CountedRoles P) (rank : DemandRank n l) (budget : Nat) :
    Except Failure (Found g (.counted roles) rank) := do
  unless rank.check g do throw .invalidRank
  match inferBoundaries g with
  | .error reason => .error reason
  | .ok cuts => (Cuts.discover g (.counted roles) rank cuts budget).mapError Failure.checkedCuts

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Siblings
