module

public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
public import Silmaril.Languages.Python.Core.Closure.Finite.Defs

/-! # Finite code tables and closure call boundaries -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Finite.Dispatch

open Semantics.Operational

variable {Body Continuation : Layout → Type} {layout : Layout}

abbrev CodeRows (Body : Layout → Type) := AList (fun _ : Nat => Closure.Dispatch.Entry Body)

def CodeRows.project (rows : CodeRows Body) : Closure.Dispatch.CodeTable Body :=
  Environment.Finite.view rows

def writeArguments : List (ParameterSlot layout × Value) → Snapshot layout →
    Except Closure.Failure (Snapshot layout)
  | [], before => .ok before
  | (slot, value) :: rest, before => (before.write slot.slot value).bind (writeArguments rest)

def bindPositional (parameters : Parameters layout) (arguments : List Value)
    (before : Snapshot layout) : Except Closure.Failure (Snapshot layout) :=
  if arguments.length = parameters.slots.length then
    writeArguments (parameters.slots.zip arguments) before
  else
    .error (.defined (.positionalArity parameters.slots.length arguments.length))

def freshFrame (fn : Function) (heap : HeapTable) : Snapshot fn.code.layout :=
  ⟨heap.reserve fn.code.layout.owned, (fn.freshFrame heap.project).2⟩

def enter (fn : Function) (parameters : Parameters fn.code.layout) (arguments : List Value)
    (heap : HeapTable) : Except Closure.Failure (Snapshot fn.code.layout) :=
  match Call.firstDangling fn heap.project with
  | some identity => .error (.danglingCell identity)
  | none => do
    let completed ← Call.completeArguments parameters fn.positionalDefaults arguments
    bindPositional parameters completed (freshFrame fn heap)

structure Active (Body Continuation : Layout → Type) where
  layout : Layout
  definition : Closure.Dispatch.Definition Body layout
  environment : Snapshot layout
  stack : List (Call.Saved Continuation)

def Active.project (active : Active Body Continuation) : Closure.Dispatch.Active Body Continuation :=
  ⟨active.layout, active.definition, ⟨active.environment.project, active.stack⟩⟩

def dispatch (rows : CodeRows Body) (callee : Value) (arguments : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    Except Closure.Dispatch.Failure (Active Body Continuation) :=
  match callee with
  | .function fn =>
    match Closure.Dispatch.resolve rows.project fn.code with
    | .error error => .error error
    | .ok definition =>
      match enter fn definition.parameters arguments heap with
      | .error error => .error (.call error)
      | .ok environment => .ok ⟨fn.code.layout, definition, environment, caller :: stack⟩
  | _ => .error (.call (.defined .notCallable))

structure Exit (Continuation : Layout → Type) where
  heap : HeapTable
  stack : List (Call.Saved Continuation)
  delivery : Call.Delivery Continuation

def Exit.project (exit : Exit Continuation) : Call.Exit Continuation :=
  ⟨exit.heap.project, exit.stack, exit.delivery⟩

/-- Keep the current finite heap while the runtime delivery selects the
original caller and continuation. -/
def finish (heap : HeapTable) (stack : List (Call.Saved Continuation)) (result : Result) :
    Exit Continuation :=
  let exit := Call.finish heap.project stack result
  ⟨heap, exit.stack, exit.delivery⟩

end Silmaril.Languages.Python.Core.Closure.Finite.Dispatch
