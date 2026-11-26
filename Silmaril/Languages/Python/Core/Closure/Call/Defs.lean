module

public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Defs

/-! # Fixed positional call entry and saved-caller delivery -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Call

/-- Each saved frame retains its own layout and typed continuation. -/
structure Saved (Continuation : Layout → Type) where
  layout : Layout
  frame : Frame layout
  continuation : Continuation layout

structure Entered (Continuation : Layout → Type) (layout : Layout) where
  environment : Environment layout
  stack : List (Saved Continuation)

variable {Continuation : Layout → Type}

/-- Check captured identities against the caller heap before allocating any callee cells. -/
def firstDangling (fn : Function) (heap : Heap) : Option CellId :=
  fn.captures.toList.find? fun identity => decide (heap.next ≤ identity.address)

/-- Expose an initialized callee and the saved caller only after binding succeeds.
Code lookup and continuation execution are supplied by the surrounding machine. -/
def enter (fn : Function) (parameters : Parameters fn.code.layout) (arguments : List Value)
    (heap : Heap) (caller : Saved Continuation) (stack : List (Saved Continuation)) :
    Except Failure (Entered Continuation fn.code.layout) :=
  match firstDangling fn heap with
  | some identity => .error (.danglingCell identity)
  | none =>
    (completeArguments parameters fn.positionalDefaults arguments).bind fun completed =>
      (bindPositional parameters completed (fn.freshFrame heap)).map fun initialized =>
        ⟨initialized, caller :: stack⟩

inductive Delivery (Continuation : Layout → Type) where
  | terminal (result : Result)
  | resume (caller : Saved Continuation) (result : Result)

structure Exit (Continuation : Layout → Type) where
  heap : Heap
  stack : List (Saved Continuation)
  delivery : Delivery Continuation

/-- Deliver either a result or a defined error with the current shared heap.
A saved frame carries the continuation's local bindings and cell identities. -/
def finish (heap : Heap) (stack : List (Saved Continuation)) (result : Result) : Exit Continuation :=
  match stack with
  | [] => ⟨heap, [], .terminal result⟩
  | caller :: rest => ⟨heap, rest, .resume caller result⟩

end Silmaril.Languages.Python.Core.Closure.Call
