module

public import Silmaril.Machine.Vex.CFG.Rows.Defs

@[expose] public section

namespace Silmaril.Machine.Vex.ControlFlow.Examples

open Silmaril.Semantics.Region.Tree (FlatCFG)

inductive Label where
  | start | resume | callee | imported
  deriving DecidableEq

def owner : Label → Option Bool
  | .start | .resume => some false
  | .callee => some true
  | .imported => none

def partition : Partition Label Bool := ⟨owner, (fun callee => if callee then .callee else .start), {.imported}⟩

def caller : FlatCFG Label := ⟨.start, {label | owner label = some false}, ∅, fun _ => ∅⟩

def direct (target : Label) : CallCFG Label :=
  ⟨caller, fun label => if label = .start then some ⟨target, some .resume⟩ else none⟩

def callRow (target : Label) (exits : Set (Edge Label)) : Prop :=
  (callFilling Label Bool).BB (direct target) (partition, false) .start .start exits

end Silmaril.Machine.Vex.ControlFlow.Examples
