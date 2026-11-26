module

public import Silmaril.Languages.Python.Core.Closure.Executor.Defs
public import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs

/-! # Finite presentation of the positional closure executor -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

open Closure.Executor (Event Fault GlobalLookup MetadataFailure MetadataField Stack)

abbrev CodeRows := Dispatch.CodeRows Closure.Executor.Body

/-- The stack and all typed control payloads are carried verbatim. Only
the heap and the fixed code table have association-list presentations. -/
inductive State where
  | running {layout : Layout} (environment : Snapshot layout) (body : Closure.Executor.Body layout) (stack : Stack)
  | delivering (heap : HeapTable) (stack : Stack) (result : Result)
  | receiving (heap : HeapTable) (caller : Call.Saved Closure.Executor.Continuation) (stack : Stack)
      (result : Result)
  | finished (heap : HeapTable) (result : Result)
  | faulted (heap : HeapTable) (stack : Stack) (fault : Fault)

def State.project : State → Closure.Executor.State
  | .running environment body stack => .running environment.heap.project environment.frame body stack
  | .delivering heap stack result => .delivering heap.project stack result
  | .receiving heap caller stack result => .receiving heap.project caller stack result
  | .finished heap result => .finished heap.project result
  | .faulted heap stack fault => .faulted heap.project stack fault

def State.completion? : State → Option Result
  | .finished _ result => some result
  | _ => none

abbrev Transition := Option Event × State

def Transition.project (next : Transition) : Closure.Executor.Transition := (next.1, next.2.project)

def fault (heap : HeapTable) (stack : Stack) (error : Fault) : Transition :=
  (some (.fault error), .faulted heap stack error)

def fail (heap : HeapTable) (stack : Stack) : Failure → Transition
  | .defined error => (none, .delivering heap stack (.error error))
  | .danglingCell identity => fault heap stack (.danglingCell identity)
  | .invalidPositionalDefaults => fault heap stack .invalidPositionalDefaults

def failDispatch (heap : HeapTable) (stack : Stack) : Closure.Dispatch.Failure → Transition
  | .call error => fail heap stack error
  | .missingCode key => fault heap stack (.missingCode key)
  | .layoutMismatch expected actual => fault heap stack (.layoutMismatch expected actual)

def failMetadata (field : MetadataField) (heap : HeapTable) (stack : Stack) : MetadataFailure → Transition
  | .read failure => fail heap stack failure
  | .code failure => failDispatch heap stack failure
  | .unprofiled ref => fault heap stack (field.unprofiledFault ref)
  | .wrongCodeNamesProfile ref actual => fault heap stack (.wrongCodeNamesProfile ref actual)
  | .nonFunction => fault heap stack field.nonFunctionFault

abbrev failFreevars := failMetadata .freevars

def resumeStore {layout : Layout} (source : Snapshot layout) (destination : Slot layout)
    (value : Value) (body : Closure.Executor.Body layout) (stack : Stack) : Transition :=
  match source.write destination value with
  | .ok updated => (none, .running updated body stack)
  | .error error => fail source.heap stack error

def enter (active : Dispatch.Active Closure.Executor.Body Closure.Executor.Continuation) : State :=
  .running active.environment active.definition.body active.stack

/-- The operand selectors run on the projected lookup. Store updates and
call entry use the finite heap operations and code table. -/
def advanceIn (rows : CodeRows) (globals : GlobalLookup) : State → Option Transition
  | .running source (.ret operand) stack =>
    some <| match operand.evalIn globals source.heap.project source.frame with
    | .ok value => (none, .delivering source.heap stack (.ok value))
    | .error error => fail source.heap stack error
  | .running source (.store destination operand next) stack =>
    some <| match operand.evalIn globals source.heap.project source.frame with
    | .ok value => resumeStore source destination value next stack
    | .error error => fail source.heap stack error
  | .running source (.assert test next) stack =>
    some <| match test.evalIn globals source.heap.project source.frame with
    | .ok value =>
      if value.truth then (none, .running source next stack)
      else (none, .delivering source.heap stack (.error .assertionError))
    | .error error => fail source.heap stack error
  | .running source (.assertFreevars test next) stack =>
    some <| match test.evalIn rows.project globals source.heap.project source.frame with
    | .ok true => (none, .running source next stack)
    | .ok false => (none, .delivering source.heap stack (.error .assertionError))
    | .error error => failFreevars source.heap stack error
  | .running source (.assertCellvars test next) stack =>
    some <| match test.evalIn rows.project globals source.heap.project source.frame with
    | .ok true => (none, .running source next stack)
    | .ok false => (none, .delivering source.heap stack (.error .assertionError))
    | .error error => failMetadata .cellvars source.heap stack error
  | .running source (.assertCodeNames test next) stack =>
    some <| match test.evalIn rows.project globals source.heap.project source.frame with
    | .ok true => (none, .running source next stack)
    | .ok false => (none, .delivering source.heap stack (.error .assertionError))
    | .error error => failMetadata .codeNames source.heap stack error
  | .running source (.invoke callee arguments continuation) stack =>
    some <| match Closure.Executor.evalCallIn globals source.heap.project source.frame callee arguments with
    | .error error => fail source.heap stack error
    | .ok (value, values) =>
      match Dispatch.dispatch rows value values source.heap ⟨_, source.frame, continuation⟩ stack with
      | .ok active => (some (.enter value), enter active)
      | .error error => failDispatch source.heap stack error
  | .delivering heap stack result =>
    let exit := Dispatch.finish heap stack result
    some <| match exit.delivery with
    | .terminal observed => (some (.complete observed), .finished exit.heap observed)
    | .resume caller observed => (some (.resume observed), .receiving exit.heap caller exit.stack observed)
  | .receiving heap caller stack (.ok value) =>
    some <| match caller.continuation with
    | some (.store slot, body) => resumeStore ⟨heap, caller.frame⟩ slot value body stack
    | some (.discard, body) => (none, .running ⟨heap, caller.frame⟩ body stack)
    | none => (none, .delivering heap stack (.ok value))
  | .receiving heap _ stack (.error error) => some (none, .delivering heap stack (.error error))
  | .finished .. | .faulted .. => none

def runPrefixIn (rows : CodeRows) (globals : GlobalLookup) : Nat → State → List Event × State
  | 0, source => ([], source)
  | fuel + 1, source =>
    match advanceIn rows globals source with
    | none => ([], source)
    | some (label, target) =>
      let (log, residual) := runPrefixIn rows globals fuel target
      (label.toList ++ log, residual)

def presentedIn (rows : CodeRows) (globals : GlobalLookup) : Cslib.LTS State (Option Event) :=
  ⟨fun source label target => advanceIn rows globals source = some (label, target)⟩

def semanticIn (table : Closure.Executor.CodeTable) (globals : GlobalLookup) :
    Cslib.LTS Closure.Executor.State (Option Event) :=
  ⟨Closure.Executor.StepIn table globals⟩

abbrev advance (rows : CodeRows) := advanceIn rows Closure.Executor.emptyGlobals
abbrev runPrefix (rows : CodeRows) := runPrefixIn rows Closure.Executor.emptyGlobals
abbrev presented (rows : CodeRows) := presentedIn rows Closure.Executor.emptyGlobals
abbrev semantic (table : Closure.Executor.CodeTable) := semanticIn table Closure.Executor.emptyGlobals

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
