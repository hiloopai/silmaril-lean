module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Trace.Thms
/-! Load-result interpretations grow by actual event index. Existing pure/slot
Extends remains immutable; prior event meanings are preserved by a prefix. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects
open Silmaril.Machine

/-- Existing node values and external partial inputs remain fixed; only load
results at or after the current event frontier may be introduced. -/
structure PrefixExtends (nodeBound eventBound : Nat) (oldMeaning newMeaning : Interpretation) : Prop where
  values : ∀ index < nodeBound, newMeaning.value index = oldMeaning.value index
  input : newMeaning.input = oldMeaning.input
  slot : newMeaning.slot = oldMeaning.slot
  address : newMeaning.address = oldMeaning.address
  load : ∀ event < eventBound, newMeaning.load event = oldMeaning.load event
  result : newMeaning.result = oldMeaning.result

def EventReferencesBelow (bound : Nat) : Expr → Prop
  | .load event => event < bound
  | _ => True

def LoadsScoped (nodes : Array Expr) (eventBound : Nat) : Prop :=
  ∀ (index : Nat) (expression : Expr), nodes[index]? = some expression → EventReferencesBelow eventBound expression

def EffectReferencesBelow (bound : Nat) : Effect → Prop
  | .load _ _ base _ => base < bound
  | .store _ base _ source | .faulting _ base source => base < bound ∧ source < bound
  | .call _ args _ => ∀ index ∈ args, index < bound
  | .indirect target args _ => target < bound ∧ ∀ index ∈ args, index < bound

/-- Install the actual result of the next successful load, preserving every
other Option result and all current node values and partial external inputs. -/
def setLoad (meaning : Interpretation) (event : Nat) (word : Lir.Word) : Interpretation :=
  { meaning with load := fun other => if other = event then some word else meaning.load other }

end Silmaril.Compiler.Native.Optimize.Validation.Effects
