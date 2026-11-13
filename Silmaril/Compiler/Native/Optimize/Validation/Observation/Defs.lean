module

public import Silmaril.Compiler.Native.Optimize.Validation.Total.Thms
/-! Partial denotation of actual symbolic terminators and observed reads.
Actual concrete source execution/read success supplies the domain; candidate
execution and checker acceptance are not premises or conclusions. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Observation
open Silmaril.Machine

def termExit (meaning : Interpretation) : Term → Option BlockExit
  | .jump label => some (.jump label)
  | .branch condition yes no =>
    (meaning.value condition).map (fun word => if word = 0 then .jump no else .jump yes)
  | .ret values => (values.mapM meaning.value).map .returned
  | .trap => some .trapped

def TermScoped (bound : Nat) : Term → Prop
  | .branch condition .. => condition < bound
  | .ret indices => ∀ index ∈ indices, index < bound
  | _ => True

structure ReadValues (before after : State) (frame : Lir.Frame Nat)
    (indices : List Nat) (values : List Lir.Word) (oldMeaning newMeaning : Interpretation) : Prop where
  result : Roots.OpResult before after frame oldMeaning newMeaning
  total : Total.TotalNodes after.nodes newMeaning
  bounded : ∀ index ∈ indices, index < after.nodes.size
  selected : indices.mapM newMeaning.value = some values

structure TermResult (before after : State) (frame : Lir.Frame Nat) (term : Term) (exit : BlockExit)
    (oldMeaning newMeaning : Interpretation) : Prop where
  result : Roots.OpResult before after frame oldMeaning newMeaning
  total : Total.TotalNodes after.nodes newMeaning
  wellScoped : TermScoped after.nodes.size term
  selected : termExit newMeaning term = some exit

structure BlockResult (before after : State) (frame : Lir.Frame Nat)
    (term : Term) (indices : List Nat) (exit : BlockExit) (values : List Lir.Word)
    (oldMeaning newMeaning : Interpretation) : Prop where
  term : TermResult before after frame term exit oldMeaning newMeaning
  observedBounded : ∀ index ∈ indices, index < after.nodes.size
  observed : indices.mapM newMeaning.value = some values

end Silmaril.Compiler.Native.Optimize.Validation.Observation
