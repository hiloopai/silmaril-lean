module

public import Silmaril.Compiler.Native.Optimize.Validation.Thms
/-! A partial denotation for the actual validator DAG. References point strictly
to earlier nodes; coherence retains missing inputs and failed arithmetic as none.
No validator/block execution or generic simulation premise is introduced. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Intern
open Silmaril.Machine

def ReferencesBelow (bound : Nat) : Expr → Prop
  | .unary _ source => source < bound
  | .binary _ left right | .float _ left right => left < bound ∧ right < bound
  | _ => True

def WellScoped (nodes : Array Expr) : Prop :=
  ∀ index expression, nodes[index]? = some expression → ReferencesBelow index expression

def Coherent (nodes : Array Expr) (meaning : Interpretation) : Prop :=
  ∀ index expression, nodes[index]? = some expression → meaning.value index = expression.eval meaning

/-- Assigning a new DAG index changes no partial external interpretation. -/
def extendValue (meaning : Interpretation) (index : Nat) (value : Option Lir.Word) : Interpretation :=
  { meaning with value := fun other => if other = index then value else meaning.value other }

/-- Constructive denotation for one actual intern result. The old index values
and expression meanings, and all external partial observations, are retained. -/
structure Denotes (before after : Array Expr) (index : Nat) (raw : Expr)
    (oldMeaning newMeaning : Interpretation) : Prop where
  wellScoped : WellScoped after
  coherent : Coherent after newMeaning
  bounded : index < after.size
  selected : newMeaning.value index = raw.eval oldMeaning
  oldValues : ∀ other < before.size, newMeaning.value other = oldMeaning.value other
  oldExpressions : ∀ (other : Nat) (expression : Expr), before[other]? = some expression →
    expression.eval newMeaning = expression.eval oldMeaning
  input : newMeaning.input = oldMeaning.input
  slot : newMeaning.slot = oldMeaning.slot
  address : newMeaning.address = oldMeaning.address
  load : newMeaning.load = oldMeaning.load
  result : newMeaning.result = oldMeaning.result

end Silmaril.Compiler.Native.Optimize.Validation.Intern
