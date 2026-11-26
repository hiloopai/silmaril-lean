module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts.Defs

/-! # Infer sequential PEG boundaries across parentless and parent/child regions -/

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions

open RVSDG (Tuple)
open PEG.Reindex.Automatic (refIds)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

inductive Failure where
  | invalidRank
  | noLoops
  | unsupportedParent (key : Nat)
  | multipleChildren (parent : Nat)
  | nestedExport (parent : Nat)
  | missingChildDependency (child : Nat)
  | dependencyCycle
  | coverage
  | missingExport (key : Nat)
  | iterationValue (row : Nat)
  | checkedCuts (reason : Cuts.Failure)
  deriving DecidableEq, Repr

private def loopRows (g : Graph P params results n l) (key : Fin l) : List (Fin n) :=
  (List.finRange n).filter fun i => (g.node i).label.loop == some key

def activeKeys (g : Graph P params results n l) : List (Fin l) :=
  (List.finRange l).filter fun key => !(loopRows g key).isEmpty

private def footprint (g : Graph P params results n l) (group : Fin l → Fin l)
    (i : Fin n) : Option (List (Fin l)) :=
  (Cuts.dependencyRows g [] [i]).map
    (List.filterMap fun j => ((g.node j).label.loop).map group)

private def order (prerequisites : Fin l → List (Fin l)) :
    Nat → List (Fin l) → Option (List (Fin l))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, pending@(_ :: _) => do
    let key ← pending.find? fun key => (prerequisites key).all fun other => other ∉ pending
    return key :: (← order prerequisites fuel (pending.erase key))

private def isParameter (g : Graph P params results n l) (row : Fin n) : Bool :=
  match g.node row with
  | ⟨_, .param _, _⟩ => true
  | _ => false

private def isSample {ins : List (Ty Data)} {t : Ty Data} : Label P params (Fin l) ins t → Bool
  | .eval _ => true
  | .pass _ => true
  | _ => false

private def isEvalOf {ins : List (Ty Data)} {t : Ty Data} (parent : Fin l) :
    Label P params (Fin l) ins t → Bool
  | .eval key => key == parent
  | _ => false

/-- Stop a readout walk at pass/eval rows, but inspect those boundary
rows too. Even a sampled child value is local to the current parent
activation. Only a pass or eval of a parentless key can stop exposure. -/
private def frameLocal (g : Graph P params results n l) (row : Fin n) : Bool :=
  let label := (g.node row).label
  label.thetaLoop.isSome || label.loop.any (fun key => (g.forest.parent key).isSome)

private def rowTuple (g : Graph P params results n l) :
    (rows : List (Fin n)) → Tuple (Ref g.sort) (rows.map g.sort)
  | [] => .nil
  | i :: tail => .cons (Ref.ofId g.sort i) (rowTuple g tail)

/-- The checked nested leaf exports exactly one outer eval. Its demand
paths behind the region's cuts must reach the child. The leaf builder
then retains every child-labelled row, including unread child evals. -/
private def checkNestedExport (g : Graph P params results n l) (parent child : Fin l)
    (frontier exports : List (Fin n)) : Except Failure PUnit.{u+1} := do
  let [row] := exports | throw (.nestedExport parent.val)
  unless isEvalOf parent (g.node row).label do throw (.nestedExport parent.val)
  let some reached := Cuts.dependencyRows g frontier exports | throw .coverage
  unless reached.any (fun row => row ∉ frontier && (g.node row).label.loop == some child) do
    throw (.missingChildDependency child.val)

/-- Plan from consumers back to producers. The group contains the child
throughout the outer region, so the frontier only crosses parentless
region boundaries and cuts function inputs. -/
private def boundaries (g : Graph P params results n l) (owner : Fin n → Option (Fin l))
    (regionRows : Fin l → List (Fin n)) (childOf : Fin l → Option (Fin l))
    (samples : List (Fin n)) :
    List (Fin l) → List (Fin n) → List (Cuts.Boundary g) → Except Failure (List (Cuts.Boundary g))
  | [], _, done => .ok done
  | key :: earlier, exports, later => do
    unless exports.any (fun row => owner row == some key) do throw (.missingExport key.val)
    let some readouts := Cuts.dependencyRows g samples exports | throw .coverage
    if let some row := readouts.find? (frameLocal g) then
      throw (.iterationValue row.val)
    else
      let frontier := (List.finRange n).filter fun row =>
        isParameter g row || (owner row).any (· != key)
      if let some child := childOf key then
        checkNestedExport g key child frontier exports
      let some seen := Cuts.dependencyRows g frontier (exports ++ regionRows key) | throw .coverage
      let inputs := seen.filter fun row => row ∈ frontier
      let b : Cuts.Boundary g := ⟨_, _, rowTuple g inputs, rowTuple g exports⟩
      boundaries g owner regionRows childOf samples earlier inputs (b :: later)
termination_by structural remaining _ _ => remaining

/-- Group each labelled child with its labelled parent before ordering
regions by their dependencies. A group may contain at most one child
and both levels stay in the same stage. -/
def inferBoundaries (g : Graph P params results n l) : Except Failure (List (Cuts.Boundary g)) := do
  let active := activeKeys g
  if active.isEmpty then throw .noLoops
  let roots := active.filter fun key => (g.forest.parent key).isNone
  if let some key := active.find? (fun key => (g.forest.parent key).any (· ∉ roots)) then
    throw (.unsupportedParent key.val)
  let children := fun root => active.filter fun key => g.forest.parent key == some root
  if let some root := roots.find? (fun root => (children root).length > 1) then
    throw (.multipleChildren root.val)
  let group := fun key => (g.forest.parent key).getD key
  let regionRows := fun key =>
    (List.finRange n).filter fun row => ((g.node row).label.loop).any (fun loop => group loop == key)
  let footprints := Vector.ofFn (footprint g group)
  if covered : ∀ i, (footprints.get i).isSome then
    let used := fun i => (footprints.get i).get (covered i)
    let prerequisites := fun key => ((regionRows key).flatMap used).filter (· != key)
    let some ordered := order prerequisites roots.length roots | throw .dependencyCycle
    let reverse := ordered.reverse
    let owner := fun row => reverse.find? fun key => key ∈ used row
    let samples := (List.finRange n).filter fun row => isSample (g.node row).label
    let rootIds := refIds g.roots
    let exports := (List.finRange n).filter fun row => row ∈ rootIds
    boundaries g owner regionRows (fun key => (children key).head?) samples reverse exports []
  else throw .coverage

/-- Infer cuts from a typed graph and use the existing leaf and schedule
checkers. Rank admission covers the original table. The search budget
is passed to the shared fixed-cut order search. -/
def discover [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l) (budget : Nat) :
    Except Failure (Found g roles rank) := do
  unless rank.check g do throw .invalidRank
  match inferBoundaries g with
  | .error reason => .error reason
  | .ok cuts => (Cuts.discover g roles rank cuts budget).mapError Failure.checkedCuts

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions
