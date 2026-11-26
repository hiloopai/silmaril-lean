module

public import Silmaril.Languages.Python.Core.Closure.Defs

/-! # Ordered positional slot binding -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout}

abbrev Environment (layout : Layout) := Heap × Frame layout

/-- Write one argument for each ordered destination. -/
def writeArguments : List (ParameterSlot layout × Value) → Environment layout →
    Except Failure (Environment layout)
  | [], before => .ok before
  | (slot, value) :: rest, before =>
    (before.2.write before.1 slot.slot value).bind (writeArguments rest)

inductive Writes : List (ParameterSlot layout × Value) → Environment layout → Environment layout → Prop where
  | nil (before : Environment layout) : Writes [] before before
  | cons {slot : ParameterSlot layout} {value : Value} {rest : List (ParameterSlot layout × Value)}
      {before middle after : Environment layout} :
      before.2.write before.1 slot.slot value = .ok middle →
      Writes rest middle after → Writes ((slot, value) :: rest) before after

/-- A wrong argument count leaves the input environment as the only committed state. -/
def bindPositional (parameters : Parameters layout) (arguments : List Value)
    (before : Environment layout) : Except Failure (Environment layout) :=
  if arguments.length = parameters.slots.length then
    writeArguments (parameters.slots.zip arguments) before
  else
    .error (.defined (.positionalArity parameters.slots.length arguments.length))

end Silmaril.Languages.Python.Core.Closure.Call
