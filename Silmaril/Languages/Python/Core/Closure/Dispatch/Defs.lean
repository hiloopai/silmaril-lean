module

public import Silmaril.Languages.Python.Core.Closure.Call.Defs

/-! # Checked dispatch of a resolved positional call -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Dispatch

inductive CodeNamesProfile where
  | cpython3135ExecOptimize0
  | cpython373ExecOptimize0
  deriving DecidableEq, Repr

structure ProfiledCodeNames where
  profile : CodeNamesProfile
  names : List String
  deriving DecidableEq, Repr

/-- The compiler supplies a body and positional layout for the same frame. -/
structure Definition (Body : Layout → Type) (layout : Layout) where
  parameters : Parameters layout
  body : Body layout
  /-- Exact profiled `co_freevars` tuple for this checked definition. -/
  freevars : Option (List String) := none
  /-- Exact profiled `co_cellvars` tuple for this checked definition. -/
  cellvars : Option (List String) := none
  /-- Exact `co_names` tuple for the code's stated compiler profile. -/
  codeNames : Option ProfiledCodeNames := none
  /-- Exact profiled CPython 3.13.5 fast-local tuple for a module code read. -/
  varnames : Option (List String) := none

structure Entry (Body : Layout → Type) where
  layout : Layout
  definition : Definition Body layout

abbrev CodeTable (Body : Layout → Type) := Nat → Option (Entry Body)

inductive Failure where
  | missingCode (key : Nat)
  | layoutMismatch (expected actual : Layout)
  | call (error : Closure.Failure)
  deriving DecidableEq, Repr

variable {Body Continuation : Layout → Type}

/-- Recover a body and parameter layout only when the table agrees with the
layout carried by the closure. -/
def resolve (table : CodeTable Body) (ref : CodeRef) :
    Except Failure (Definition Body ref.layout) :=
  match table ref.key with
  | none => .error (.missingCode ref.key)
  | some entry =>
    if same : entry.layout = ref.layout then .ok (same ▸ entry.definition)
    else .error (.layoutMismatch ref.layout entry.layout)

def Resolves (table : CodeTable Body) (ref : CodeRef) (definition : Definition Body ref.layout) : Prop :=
  table ref.key = some ⟨ref.layout, definition⟩

structure Active (Body Continuation : Layout → Type) where
  layout : Layout
  definition : Definition Body layout
  entered : Call.Entered Continuation layout

/-- Dispatch takes evaluated values. Body execution starts in the returned
callee environment, with the typed caller on its stack. -/
def dispatch (table : CodeTable Body) (callee : Value) (arguments : List Value)
    (heap : Heap) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    Except Failure (Active Body Continuation) :=
  match callee with
  | .none | .int _ | .bool _ => .error (.call (.defined .notCallable))
  | .function fn =>
    match resolve table fn.code with
    | .error error => .error error
    | .ok definition =>
      match Call.enter fn definition.parameters arguments heap caller stack with
      | .error error => .error (.call error)
      | .ok entered => .ok ⟨fn.code.layout, definition, entered⟩

/-- A successful dispatch reads a well-typed code entry and binds the
positional arguments by the ordered write relation. -/
inductive Dispatches (table : CodeTable Body) (arguments : List Value) (heap : Heap)
    (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    Value → Active Body Continuation → Prop where
  | function {fn : Function} {definition : Definition Body fn.code.layout}
      {environment : Call.Environment fn.code.layout}
      (code : Resolves table fn.code definition)
      {completed : List Value}
      (completion : Call.completeArguments definition.parameters fn.positionalDefaults arguments = .ok completed)
      (captures : ∀ identity ∈ fn.captures.toList, identity.address < heap.next)
      (writes : Call.Writes (definition.parameters.slots.zip completed) (fn.freshFrame heap) environment) :
      Dispatches table arguments heap caller stack (.function fn)
        ⟨fn.code.layout, definition, ⟨environment, caller :: stack⟩⟩

end Silmaril.Languages.Python.Core.Closure.Dispatch
