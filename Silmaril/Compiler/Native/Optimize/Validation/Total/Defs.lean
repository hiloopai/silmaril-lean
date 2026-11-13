module

public import Silmaril.Compiler.Native.Optimize.Validation.Lists.Thms
/-! Total DAG values are proved from successful source execution; arbitrary
partial Rooted states do not imply this invariant. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Total
open Silmaril.Machine

def TotalNodes (nodes : Array Expr) (meaning : Interpretation) : Prop :=
  ∀ index < nodes.size, ∃ word, meaning.value index = some word

def initialMeaning (frame : Lir.Frame Nat) : Interpretation where
  input := frame.get
  slot := frame.slots
  value := fun _ => none
  address := fun _ _ => none
  load := fun _ => none
  result := fun _ _ => none

end Silmaril.Compiler.Native.Optimize.Validation.Total
