module

public import Silmaril.Languages.Python.Core.Closure.Call.Binding

/-! # Bind supplied positionals and saved trailing defaults

Default expressions have already been evaluated and their values belong to
the selected function. This interface consumes those values with the
function's declaration-ordered parameter destinations.
-/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Call

/-- One saved value for each trailing optional parameter, in declaration order. -/
structure PositionalDefaults {layout : Layout} (parameters : Parameters layout) where
  values : List Value
  fits : values.length ≤ parameters.slots.length

namespace PositionalDefaults

variable {layout : Layout} {parameters : Parameters layout}

def required (defaults : PositionalDefaults parameters) : Nat :=
  parameters.slots.length - defaults.values.length

/-- Check the supplied count before writing slots. Explicit arguments occupy
the prefix. Only the corresponding omitted suffix uses saved values. -/
def complete (defaults : PositionalDefaults parameters) (supplied : List Value) : Except Failure (List Value) :=
  if supplied.length < defaults.required then
    .error (.defined (.positionalArity defaults.required supplied.length))
  else if parameters.slots.length < supplied.length then
    .error (.defined (.positionalArity parameters.slots.length supplied.length))
  else
    .ok (supplied ++ defaults.values.drop (supplied.length - defaults.required))

def bind (defaults : PositionalDefaults parameters) (supplied : List Value)
    (before : Environment layout) : Except Failure (Environment layout) :=
  (defaults.complete supplied).bind fun arguments => bindPositional parameters arguments before

end PositionalDefaults

/-- Complete arguments using the selected descriptor. An invalid descriptor
is a machine fault, distinct from an arity error in a checked call. -/
def completeArguments {layout : Layout} (parameters : Parameters layout)
    (saved : List Core.Module.Value) (supplied : List Value) : Except Failure (List Value) :=
  if fits : saved.length ≤ parameters.slots.length then
    PositionalDefaults.complete (parameters := parameters) ⟨saved.map Value.ofScalar, by simpa using fits⟩ supplied
  else .error .invalidPositionalDefaults

end Silmaril.Languages.Python.Core.Closure.Call
