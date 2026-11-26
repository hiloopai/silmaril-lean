module

public import Silmaril.Languages.Python.Core.Closure.Executor.Defs

/-! # Module publication and fixed positional calls -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.Functions

open Core.Closure
open Core.Closure.Executor (CodeTable Event GlobalLookup)

abbrev GlobalName := String

/-- A single initialized namespace for scalar values and functions. The
surrounding module owns its initial lookup and the order of top-level actions. -/
structure Session where
  globals : GlobalLookup
  heap : Heap

def Session.bindGlobal (session : Session) (name : GlobalName) (value : Closure.Value) : Session :=
  { session with globals := fun query => if query = name then some value else session.globals query }

/-- A module-level function uses global names for module bindings. Only
function-nested definitions create closure cells in this profile. -/
structure TopFunction where
  ref : CodeRef
  noCaptures : ref.layout.captures = 0

def TopFunction.closure (function : TopFunction) : Function :=
  Function.ofCaptureList function.ref [] function.noCaptures.symm

def TopFunction.value (function : TopFunction) : Closure.Value :=
  .function function.closure

/-- Attach the evaluated values to the actual descriptor carried by aliases. -/
def TopFunction.withDefaults (function : TopFunction) (saved : List Core.Module.Value) : Function :=
  { function.closure with positionalDefaults := saved }

/-- Resolve the layout before publishing the binding. Body execution starts
only with an invocation. Publication preserves the heap. -/
def Session.publish (session : Session) (table : CodeTable) (name : GlobalName)
    (function : TopFunction) : Except Dispatch.Failure Session :=
  (Dispatch.resolve table function.ref).map fun _ => session.bindGlobal name function.value

/-- A completed default list is installed only with a resolved code entry. -/
def Session.publishWithDefaults (session : Session) (table : CodeTable) (name : GlobalName)
    (function : TopFunction) (saved : List Core.Module.Value) : Except Dispatch.Failure Session :=
  (Dispatch.resolve table function.ref).map fun _ => session.bindGlobal name (.function (function.withDefaults saved))

inductive Operand where
  | literal (value : Closure.Value)
  | readGlobal (name : GlobalName)

def Operand.lower {layout : Layout} : Operand → Executor.Operand layout
  | .literal value => .literal value
  | .readGlobal name => .readGlobal name

inductive Destination where
  | discard
  | bindGlobal (name : GlobalName)
  | assert

/-- A synchronous module invocation uses its module lookup throughout the
executor path, including any nested calls. -/
structure Invocation where
  globals : GlobalLookup
  destination : Destination
  state : Executor.State

/-- Use the executor's existing call, return, and error paths. The internal
caller holds only a result slot, so it does not allocate any cells. -/
def Session.prepareCall (session : Session) (destination : Destination) (callee : Operand)
    (arguments : List Operand) : Invocation :=
  let layout : Layout := ⟨1, 0, 0⟩
  let result : Slot layout := .local ⟨0, by decide⟩
  let frame : Frame layout := ⟨fun _ => none, Fin.elim0, Fin.elim0⟩
  ⟨session.globals, destination, .running session.heap frame
    (.call result callee.lower (arguments.map Operand.lower) (.ret (.read result))) []⟩

def Invocation.runPrefix (invocation : Invocation) (table : CodeTable) (fuel : Nat) : List Event × Invocation :=
  let (log, state) := Executor.runPrefixIn table invocation.globals fuel invocation.state
  (log, { invocation with state })

inductive Completion where
  | returned (value : Closure.Value)
  | raised (error : RuntimeError)
  | assertionError
  | fault (error : Executor.Fault)

structure Observation where
  completion : Completion
  residual : Session

def truth : Closure.Value → Bool := Closure.Value.truth

/-- Commit the destination only after terminal success. A raised error or
fault retains the residual heap and leaves all module bindings untouched. -/
def Invocation.finish? (invocation : Invocation) : Option Observation :=
  match invocation.state with
  | .finished heap (.ok value) =>
    let session : Session := ⟨invocation.globals, heap⟩
    match invocation.destination with
    | .discard => some ⟨.returned value, session⟩
    | .bindGlobal name => some ⟨.returned value, session.bindGlobal name value⟩
    | .assert =>
      if truth value then some ⟨.returned value, session⟩ else some ⟨.assertionError, session⟩
  | .finished heap (.error error) => some ⟨.raised error, ⟨invocation.globals, heap⟩⟩
  | .faulted heap _ error => some ⟨.fault error, ⟨invocation.globals, heap⟩⟩
  | _ => none

/-- Relational readback from an executor terminal state. The returned value
and residual heap are the ones produced by the executor. -/
inductive Settles (globals : GlobalLookup) : Destination → Executor.State → Observation → Prop where
  | discarded (heap : Heap) (value : Closure.Value) :
      Settles globals .discard (.finished heap (.ok value)) ⟨.returned value, ⟨globals, heap⟩⟩
  | assigned (heap : Heap) (name : GlobalName) (value : Closure.Value) :
      Settles globals (.bindGlobal name) (.finished heap (.ok value))
        ⟨.returned value, (Session.mk globals heap).bindGlobal name value⟩
  | assertTrue (heap : Heap) (value : Closure.Value) (holds : truth value = true) :
      Settles globals .assert (.finished heap (.ok value)) ⟨.returned value, ⟨globals, heap⟩⟩
  | assertFalse (heap : Heap) (value : Closure.Value) (fails : truth value = false) :
      Settles globals .assert (.finished heap (.ok value)) ⟨.assertionError, ⟨globals, heap⟩⟩
  | raised (destination : Destination) (heap : Heap) (error : RuntimeError) :
      Settles globals destination (.finished heap (.error error)) ⟨.raised error, ⟨globals, heap⟩⟩
  | fault (destination : Destination) (heap : Heap) (stack : Executor.Stack) (error : Executor.Fault) :
      Settles globals destination (.faulted heap stack error) ⟨.fault error, ⟨globals, heap⟩⟩

end Silmaril.Languages.Python.Core.Module.Functions
