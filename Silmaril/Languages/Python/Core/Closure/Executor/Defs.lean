module

public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs

/-! # Stepping fixed positional Python closure bodies -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Executor

/-- The surrounding module provides a global lookup for each step. A closure
retains its code and cell identities. -/
abbrev GlobalLookup := String → Option Value

def emptyGlobals : GlobalLookup := fun _ => none

inductive NameRead (layout : Layout) where
  | slot (slot : Slot layout)
  | global (name : String)

structure FreevarsTest (layout : Layout) where
  receiver : NameRead layout
  needle : List UInt32
  expected : Bool

/-- Check that a literal is absent from the receiver's profiled cell tuple. -/
structure CellvarsTest (layout : Layout) where
  receiver : NameRead layout
  needle : List UInt32

/-- Check membership in the CPython 3.13.5 exec, optimize=0 name tuple. -/
structure CodeNamesTest (layout : Layout) where
  receiver : NameRead layout
  needle : List UInt32

inductive Operand (layout : Layout) where
  | literal (value : Value)
  | read (slot : Slot layout)
  | readGlobal (name : String)
  | eqInt (left : NameRead layout) (right : Int)
  | binaryInt (op : IntegerOp) (left right : Operand layout)
  | closure (code : CodeRef) (select : Fin code.layout.captures → CaptureSlot layout)

abbrev Operand.addInt {layout : Layout} := @Operand.binaryInt layout .add

inductive Destination (layout : Layout) where
  | store (slot : Slot layout)
  | discard

/-- A body ends in a return or a final call. Continuing calls can store
or discard their returned value. -/
inductive Body (layout : Layout) where
  | ret (value : Operand layout)
  | store (destination : Slot layout) (value : Operand layout) (next : Body layout)
  | assert (test : Operand layout) (next : Body layout)
  | assertFreevars (test : FreevarsTest layout) (next : Body layout)
  | assertCellvars (test : CellvarsTest layout) (next : Body layout)
  | assertCodeNames (test : CodeNamesTest layout) (next : Body layout)
  | invoke (callee : Operand layout) (arguments : List (Operand layout))
      (continuation : Option (Destination layout × Body layout))

/-- A call continues in the current body after storing or discarding its
result. A final call delivers its result to this frame's caller. -/
abbrev Continuation (layout : Layout) := Option (Destination layout × Body layout)

@[match_pattern] abbrev Body.callTo {layout : Layout} (destination : Destination layout) (callee : Operand layout)
    (arguments : List (Operand layout)) (next : Body layout) : Body layout :=
  .invoke callee arguments (some (destination, next))

abbrev Body.returnCall {layout : Layout} (callee : Operand layout) (arguments : List (Operand layout)) :
    Body layout :=
  .invoke callee arguments none

/-- Store a call's successful result in an existing slot. -/
abbrev Body.call {layout : Layout} (destination : Slot layout) (callee : Operand layout)
    (arguments : List (Operand layout)) (next : Body layout) : Body layout :=
  .callTo (.store destination) callee arguments next

abbrev Stack := List (Call.Saved Continuation)
abbrev CodeTable := Dispatch.CodeTable Body

inductive Fault where
  | danglingCell (identity : CellId)
  | invalidPositionalDefaults
  | missingCode (key : Nat)
  | layoutMismatch (expected actual : Layout)
  | unprofiledFreevars (ref : CodeRef)
  | unsupportedFreevarsReceiver
  | unprofiledCellvars (ref : CodeRef)
  | unsupportedCellvarsReceiver
  | unprofiledCodeNames (ref : CodeRef)
  | wrongCodeNamesProfile (ref : CodeRef) (actual : Dispatch.CodeNamesProfile)
  | unsupportedCodeNamesReceiver
  deriving DecidableEq, Repr

inductive FreevarsFailure where
  | read (failure : Failure)
  | code (failure : Dispatch.Failure)
  | unprofiled (ref : CodeRef)
  | wrongCodeNamesProfile (ref : CodeRef) (actual : Dispatch.CodeNamesProfile)
  | nonFunction
  deriving DecidableEq, Repr

/-- Tuple reads share failure categories. The selected field determines the
unsupported fault reported by the assertion. -/
abbrev MetadataFailure := FreevarsFailure

inductive MetadataField where
  | freevars
  | cellvars
  | codeNames

def MetadataField.select {layout : Layout} (field : MetadataField)
    (definition : Dispatch.Definition Body layout) : Option (List String) :=
  match field with
  | .freevars => definition.freevars
  | .cellvars => definition.cellvars
  | .codeNames =>
    match definition.codeNames with
    | some ⟨.cpython3135ExecOptimize0, names⟩ => some names
    | _ => none

def MetadataField.unavailable {layout : Layout} (field : MetadataField) (ref : CodeRef)
    (definition : Dispatch.Definition Body layout) : MetadataFailure :=
  match field, definition.codeNames with
  | .codeNames, some metadata => .wrongCodeNamesProfile ref metadata.profile
  | _, _ => .unprofiled ref

def MetadataField.unprofiledFault (field : MetadataField) (ref : CodeRef) : Fault :=
  match field with
  | .freevars => .unprofiledFreevars ref
  | .cellvars => .unprofiledCellvars ref
  | .codeNames => .unprofiledCodeNames ref

def MetadataField.nonFunctionFault : MetadataField → Fault
  | .freevars => .unsupportedFreevarsReceiver
  | .cellvars => .unsupportedCellvarsReceiver
  | .codeNames => .unsupportedCodeNamesReceiver

inductive State where
  | running (heap : Heap) {layout : Layout} (frame : Frame layout) (body : Body layout) (stack : Stack)
  | delivering (heap : Heap) (stack : Stack) (result : Result)
  | receiving (heap : Heap) (caller : Call.Saved Continuation) (stack : Stack) (result : Result)
  | finished (heap : Heap) (result : Result)
  | faulted (heap : Heap) (stack : Stack) (fault : Fault)

inductive Event where
  | enter (callee : Value)
  | resume (result : Result)
  | complete (result : Result)
  | fault (error : Fault)

abbrev Transition := Option Event × State

variable {layout : Layout}

def NameRead.operand : NameRead layout → Operand layout
  | .slot location => .read location
  | .global name => .readGlobal name

def NameRead.evalIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) :
    NameRead layout → Except Failure Value
  | .slot location => frame.read heap location
  | .global name =>
    match globals name with
    | some value => .ok value
    | none => .error (.defined (.nameError name))

/-- Resolve the current function's checked definition. Its captured cells
do not participate in this read. -/
def readMetadata (field : MetadataField) (table : CodeTable) : Value → Except MetadataFailure (List String)
  | .function fn =>
    match Dispatch.resolve table fn.code with
    | .error failure => .error (.code failure)
    | .ok definition =>
      match field.select definition with
      | some names => .ok names
      | none => .error (field.unavailable fn.code definition)
  | .int _ | .bool _ | .none => .error .nonFunction

abbrev readFreevars := readMetadata .freevars
abbrev readCellvars := readMetadata .cellvars
abbrev readCodeNames := readMetadata .codeNames

def MetadataField.evalIn (field : MetadataField) (receiver : NameRead layout) (needle : List UInt32)
    (expected : Bool) (table : CodeTable) (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) :
    Except MetadataFailure Bool := do
  let value ← (receiver.evalIn globals heap frame).mapError FreevarsFailure.read
  let names ← readMetadata field table value
  let found := names.any fun name => name.toList.map Char.val == needle
  return found == expected

def FreevarsTest.evalIn (test : FreevarsTest layout) (table : CodeTable) (globals : GlobalLookup)
    (heap : Heap) (frame : Frame layout) : Except FreevarsFailure Bool :=
  MetadataField.freevars.evalIn test.receiver test.needle test.expected table globals heap frame

def CellvarsTest.evalIn (test : CellvarsTest layout) (table : CodeTable) (globals : GlobalLookup)
    (heap : Heap) (frame : Frame layout) : Except MetadataFailure Bool :=
  MetadataField.cellvars.evalIn test.receiver test.needle false table globals heap frame

def CodeNamesTest.evalIn (test : CodeNamesTest layout) (table : CodeTable) (globals : GlobalLookup)
    (heap : Heap) (frame : Frame layout) : Except MetadataFailure Bool :=
  MetadataField.codeNames.evalIn test.receiver test.needle true table globals heap frame

def Operand.evalIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) : Operand layout → Except Failure Value
  | .literal value => .ok value
  | .read slot => frame.read heap slot
  | .readGlobal name => (NameRead.global name).evalIn globals heap frame
  | .eqInt left right => (left.evalIn globals heap frame).map fun value => .bool (value.equalInt right)
  | .binaryInt op left right =>
    (left.evalIn globals heap frame).bind fun lhs =>
      (right.evalIn globals heap frame).bind (Value.binaryInt op lhs)
  | .closure code select => .ok (.function (frame.closure code select))

def evalArgumentsIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) :
    List (Operand layout) → Except Failure (List Value)
  | [] => .ok []
  | head :: tail =>
    (head.evalIn globals heap frame).bind fun value => (evalArgumentsIn globals heap frame tail).map (value :: ·)

def evalCallIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) (callee : Operand layout)
    (arguments : List (Operand layout)) : Except Failure (Value × List Value) :=
  (callee.evalIn globals heap frame).bind fun value => (evalArgumentsIn globals heap frame arguments).map (value, ·)

def fault (heap : Heap) (stack : Stack) (error : Fault) : Transition :=
  (some (.fault error), .faulted heap stack error)

def fail (heap : Heap) (stack : Stack) : Failure → Transition
  | .defined error => (none, .delivering heap stack (.error error))
  | .danglingCell identity => fault heap stack (.danglingCell identity)
  | .invalidPositionalDefaults => fault heap stack .invalidPositionalDefaults

def failDispatch (heap : Heap) (stack : Stack) : Dispatch.Failure → Transition
  | .call error => fail heap stack error
  | .missingCode key => fault heap stack (.missingCode key)
  | .layoutMismatch expected actual => fault heap stack (.layoutMismatch expected actual)

def failMetadata (field : MetadataField) (heap : Heap) (stack : Stack) : MetadataFailure → Transition
  | .read failure => fail heap stack failure
  | .code failure => failDispatch heap stack failure
  | .unprofiled ref => fault heap stack (field.unprofiledFault ref)
  | .wrongCodeNamesProfile ref actual => fault heap stack (.wrongCodeNamesProfile ref actual)
  | .nonFunction => fault heap stack field.nonFunctionFault

abbrev failFreevars := failMetadata .freevars
abbrev failCellvars := failMetadata .cellvars
abbrev failCodeNames := failMetadata .codeNames

def resumeStore (heap : Heap) (frame : Frame layout) (destination : Slot layout)
    (value : Value) (body : Body layout) (stack : Stack) : Transition :=
  match frame.write heap destination value with
  | .ok (updated, frame') => (none, .running updated frame' body stack)
  | .error error => fail heap stack error

def enter (active : Dispatch.Active Body Continuation) : State :=
  .running active.entered.environment.1 active.entered.environment.2 active.definition.body active.entered.stack

/-- Execute one transition, preserving the heap in terminal states. -/
def advanceIn (table : CodeTable) (globals : GlobalLookup) : State → Option Transition
  | .running heap frame (.ret operand) stack =>
    some <| match operand.evalIn globals heap frame with
    | .ok value => (none, .delivering heap stack (.ok value))
    | .error error => fail heap stack error
  | .running heap frame (.store destination operand next) stack =>
    some <| match operand.evalIn globals heap frame with
    | .ok value => resumeStore heap frame destination value next stack
    | .error error => fail heap stack error
  | .running heap frame (.assert test next) stack =>
    some <| match test.evalIn globals heap frame with
    | .ok value =>
      if value.truth then (none, .running heap frame next stack)
      else (none, .delivering heap stack (.error .assertionError))
    | .error error => fail heap stack error
  | .running heap frame (.assertFreevars test next) stack =>
    some <| match test.evalIn table globals heap frame with
    | .ok true => (none, .running heap frame next stack)
    | .ok false => (none, .delivering heap stack (.error .assertionError))
    | .error error => failFreevars heap stack error
  | .running heap frame (.assertCellvars test next) stack =>
    some <| match test.evalIn table globals heap frame with
    | .ok true => (none, .running heap frame next stack)
    | .ok false => (none, .delivering heap stack (.error .assertionError))
    | .error error => failCellvars heap stack error
  | .running heap frame (.assertCodeNames test next) stack =>
    some <| match test.evalIn table globals heap frame with
    | .ok true => (none, .running heap frame next stack)
    | .ok false => (none, .delivering heap stack (.error .assertionError))
    | .error error => failCodeNames heap stack error
  | .running heap frame (.invoke callee arguments continuation) stack =>
    some <| match evalCallIn globals heap frame callee arguments with
    | .error error => fail heap stack error
    | .ok (value, values) =>
      match Dispatch.dispatch table value values heap ⟨_, frame, continuation⟩ stack with
      | .ok active => (some (.enter value), enter active)
      | .error error => failDispatch heap stack error
  | .delivering heap stack result =>
    let exit := Call.finish heap stack result
    some <| match exit.delivery with
    | .terminal observed => (some (.complete observed), .finished exit.heap observed)
    | .resume caller observed => (some (.resume observed), .receiving exit.heap caller exit.stack observed)
  | .receiving heap caller stack (.ok value) =>
    some <| match caller.continuation with
    | some (.store slot, body) => resumeStore heap caller.frame slot value body stack
    | some (.discard, body) => (none, .running heap caller.frame body stack)
    | none => (none, .delivering heap stack (.ok value))
  | .receiving heap _ stack (.error error) => some (none, .delivering heap stack (.error error))
  | .finished .. | .faulted .. => none

/-- Execute at most the requested number of transitions and keep the residual
state. A prefix that ends in a live state makes no termination claim. -/
def runPrefixIn (table : CodeTable) (globals : GlobalLookup) : Nat → State → List Event × State
  | 0, source => ([], source)
  | fuel + 1, source =>
    match advanceIn table globals source with
    | none => ([], source)
    | some (label, target) =>
      let (log, residual) := runPrefixIn table globals fuel target
      (label.toList ++ log, residual)

/-- Slot reads are the primitive operations shared with the frame interface. -/
inductive EvaluatesIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) :
    Operand layout → Except Failure Value → Prop where
  | literal (value : Value) : EvaluatesIn globals heap frame (.literal value) (.ok value)
  | read (slot : Slot layout) : EvaluatesIn globals heap frame (.read slot) (frame.read heap slot)
  | globalFound {name value} : globals name = some value →
      EvaluatesIn globals heap frame (.readGlobal name) (.ok value)
  | globalMissing {name} : globals name = none →
      EvaluatesIn globals heap frame (.readGlobal name) (.error (.defined (.nameError name)))
  | eqInt {left : NameRead layout} {right result} :
      EvaluatesIn globals heap frame left.operand result →
      EvaluatesIn globals heap frame (.eqInt left right) (result.map fun value => .bool (value.equalInt right))
  | binaryLeftError {op left right error} :
      EvaluatesIn globals heap frame left (.error error) →
      EvaluatesIn globals heap frame (.binaryInt op left right) (.error error)
  | binaryRightError {op left right value error} :
      EvaluatesIn globals heap frame left (.ok value) →
      EvaluatesIn globals heap frame right (.error error) →
      EvaluatesIn globals heap frame (.binaryInt op left right) (.error error)
  | binaryValues {op left right lhs rhs} :
      EvaluatesIn globals heap frame left (.ok lhs) →
      EvaluatesIn globals heap frame right (.ok rhs) →
      EvaluatesIn globals heap frame (.binaryInt op left right) (Value.binaryInt op lhs rhs)
  | closure (code : CodeRef) (select : Fin code.layout.captures → CaptureSlot layout) :
      EvaluatesIn globals heap frame (.closure code select) (.ok (.function (frame.closure code select)))

inductive ArgumentsIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) :
    List (Operand layout) → Except Failure (List Value) → Prop where
  | nil : ArgumentsIn globals heap frame [] (.ok [])
  | headError {head tail error} : EvaluatesIn globals heap frame head (.error error) →
      ArgumentsIn globals heap frame (head :: tail) (.error error)
  | tailError {head tail value error} : EvaluatesIn globals heap frame head (.ok value) →
      ArgumentsIn globals heap frame tail (.error error) → ArgumentsIn globals heap frame (head :: tail) (.error error)
  | cons {head tail value values} : EvaluatesIn globals heap frame head (.ok value) →
      ArgumentsIn globals heap frame tail (.ok values) → ArgumentsIn globals heap frame (head :: tail) (.ok (value :: values))

inductive InputsIn (globals : GlobalLookup) (heap : Heap) (frame : Frame layout) :
    Operand layout → List (Operand layout) → Except Failure (Value × List Value) → Prop where
  | calleeError {callee arguments error} : EvaluatesIn globals heap frame callee (.error error) →
      InputsIn globals heap frame callee arguments (.error error)
  | argumentError {callee arguments value error} : EvaluatesIn globals heap frame callee (.ok value) →
      ArgumentsIn globals heap frame arguments (.error error) → InputsIn globals heap frame callee arguments (.error error)
  | ok {callee arguments value values} : EvaluatesIn globals heap frame callee (.ok value) →
      ArgumentsIn globals heap frame arguments (.ok values) → InputsIn globals heap frame callee arguments (.ok (value, values))

/-- Failure premises inspect the code table, captures and arity. -/
inductive Rejects (table : CodeTable) (arguments : List Value) (heap : Heap) :
    Value → Dispatch.Failure → Prop where
  | nonCallableNone : Rejects table arguments heap .none (.call (.defined .notCallable))
  | nonCallable (value : Int) : Rejects table arguments heap (.int value) (.call (.defined .notCallable))
  | nonCallableBool (value : Bool) : Rejects table arguments heap (.bool value) (.call (.defined .notCallable))
  | missing (fn : Function) (absent : table fn.code.key = none) :
      Rejects table arguments heap (.function fn) (.missingCode fn.code.key)
  | mismatch (fn : Function) (entry : Dispatch.Entry Body)
      (found : table fn.code.key = some entry) (different : entry.layout ≠ fn.code.layout) :
      Rejects table arguments heap (.function fn) (.layoutMismatch fn.code.layout entry.layout)
  | dangling {fn : Function} {definition : Dispatch.Definition Body fn.code.layout} {identity : CellId}
      (found : Dispatch.Resolves table fn.code definition) (first : Call.firstDangling fn heap = some identity) :
      Rejects table arguments heap (.function fn) (.call (.danglingCell identity))
  | arguments {fn : Function} {definition : Dispatch.Definition Body fn.code.layout} {error : Failure}
      (found : Dispatch.Resolves table fn.code definition) (live : Call.firstDangling fn heap = none)
      (rejected : Call.completeArguments definition.parameters fn.positionalDefaults arguments = .error error) :
      Rejects table arguments heap (.function fn) (.call error)

/-- Assignment and successful return delivery use the same frame-write relation. -/
inductive Stores (heap : Heap) (frame : Frame layout) (destination : Slot layout) (value : Value)
    (body : Body layout) (stack : Stack) : Transition → Prop where
  | ok {updated frame'} : frame.write heap destination value = .ok (updated, frame') →
      Stores heap frame destination value body stack (none, .running updated frame' body stack)
  | error {failure} : frame.write heap destination value = .error failure →
      Stores heap frame destination value body stack (fail heap stack failure)

/-- The body and delivery rules do not refer to the machine's selector. -/
inductive StepIn (table : CodeTable) (globals : GlobalLookup) : State → Option Event → State → Prop where
  | ret {heap stack layout} {frame : Frame layout} {operand value} :
      EvaluatesIn globals heap frame operand (.ok value) →
      StepIn table globals (.running heap frame (.ret operand) stack) none (.delivering heap stack (.ok value))
  | retError {heap stack layout} {frame : Frame layout} {operand error} :
      EvaluatesIn globals heap frame operand (.error error) →
      StepIn table globals (.running heap frame (.ret operand) stack) (fail heap stack error).1 (fail heap stack error).2
  | store {heap stack layout} {frame : Frame layout} {destination operand next value transition} :
      EvaluatesIn globals heap frame operand (.ok value) → Stores heap frame destination value next stack transition →
      StepIn table globals (.running heap frame (.store destination operand next) stack) transition.1 transition.2
  | storeError {heap stack layout} {frame : Frame layout} {destination operand next error} :
      EvaluatesIn globals heap frame operand (.error error) →
      StepIn table globals (.running heap frame (.store destination operand next) stack)
        (fail heap stack error).1 (fail heap stack error).2
  | assertTrue {heap stack layout} {frame : Frame layout} {test next value} :
      EvaluatesIn globals heap frame test (.ok value) → value.truth = true →
      StepIn table globals (.running heap frame (.assert test next) stack) none (.running heap frame next stack)
  | assertFalse {heap stack layout} {frame : Frame layout} {test next value} :
      EvaluatesIn globals heap frame test (.ok value) → value.truth = false →
      StepIn table globals (.running heap frame (.assert test next) stack) none
        (.delivering heap stack (.error .assertionError))
  | assertError {heap stack layout} {frame : Frame layout} {test next error} :
      EvaluatesIn globals heap frame test (.error error) →
      StepIn table globals (.running heap frame (.assert test next) stack)
        (fail heap stack error).1 (fail heap stack error).2
  | assertFreevarsTrue {heap stack layout} {frame : Frame layout} {test next} :
      test.evalIn table globals heap frame = .ok true →
      StepIn table globals (.running heap frame (.assertFreevars test next) stack)
        none (.running heap frame next stack)
  | assertFreevarsFalse {heap stack layout} {frame : Frame layout} {test next} :
      test.evalIn table globals heap frame = .ok false →
      StepIn table globals (.running heap frame (.assertFreevars test next) stack)
        none (.delivering heap stack (.error .assertionError))
  | assertFreevarsError {heap stack layout} {frame : Frame layout} {test next error} :
      test.evalIn table globals heap frame = .error error →
      StepIn table globals (.running heap frame (.assertFreevars test next) stack)
        (failFreevars heap stack error).1 (failFreevars heap stack error).2
  | assertCellvarsTrue {heap stack layout} {frame : Frame layout} {test next} :
      test.evalIn table globals heap frame = .ok true →
      StepIn table globals (.running heap frame (.assertCellvars test next) stack)
        none (.running heap frame next stack)
  | assertCellvarsFalse {heap stack layout} {frame : Frame layout} {test next} :
      test.evalIn table globals heap frame = .ok false →
      StepIn table globals (.running heap frame (.assertCellvars test next) stack)
        none (.delivering heap stack (.error .assertionError))
  | assertCellvarsError {heap stack layout} {frame : Frame layout} {test next error} :
      test.evalIn table globals heap frame = .error error →
      StepIn table globals (.running heap frame (.assertCellvars test next) stack)
        (failCellvars heap stack error).1 (failCellvars heap stack error).2
  | assertCodeNamesTrue {heap stack layout} {frame : Frame layout} {test next} :
      test.evalIn table globals heap frame = .ok true →
      StepIn table globals (.running heap frame (.assertCodeNames test next) stack)
        none (.running heap frame next stack)
  | assertCodeNamesFalse {heap stack layout} {frame : Frame layout} {test next} :
      test.evalIn table globals heap frame = .ok false →
      StepIn table globals (.running heap frame (.assertCodeNames test next) stack)
        none (.delivering heap stack (.error .assertionError))
  | assertCodeNamesError {heap stack layout} {frame : Frame layout} {test next error} :
      test.evalIn table globals heap frame = .error error →
      StepIn table globals (.running heap frame (.assertCodeNames test next) stack)
        (failCodeNames heap stack error).1 (failCodeNames heap stack error).2
  | call {heap stack layout} {frame : Frame layout} {callee arguments continuation value values active} :
      InputsIn globals heap frame callee arguments (.ok (value, values)) →
      Dispatch.Dispatches table values heap ⟨layout, frame, continuation⟩ stack value active →
      StepIn table globals (.running heap frame (.invoke callee arguments continuation) stack)
        (some (.enter value)) (enter active)
  | callError {heap stack layout} {frame : Frame layout} {callee arguments continuation error} :
      InputsIn globals heap frame callee arguments (.error error) →
      StepIn table globals (.running heap frame (.invoke callee arguments continuation) stack)
        (fail heap stack error).1 (fail heap stack error).2
  | rejected {heap stack layout} {frame : Frame layout} {callee arguments continuation value values error} :
      InputsIn globals heap frame callee arguments (.ok (value, values)) → Rejects table values heap value error →
      StepIn table globals (.running heap frame (.invoke callee arguments continuation) stack)
        (failDispatch heap stack error).1 (failDispatch heap stack error).2
  | complete (heap : Heap) (result : Result) :
      StepIn table globals (.delivering heap [] result) (some (.complete result)) (.finished heap result)
  | resume (heap : Heap) (caller : Call.Saved Continuation) (stack : Stack) (result : Result) :
      StepIn table globals (.delivering heap (caller :: stack) result) (some (.resume result))
        (.receiving heap caller stack result)
  | receive {heap caller stack value slot body transition} :
      caller.continuation = some (.store slot, body) →
      Stores heap caller.frame slot value body stack transition →
      StepIn table globals (.receiving heap caller stack (.ok value)) transition.1 transition.2
  | receiveDiscard {heap caller stack value body} :
      caller.continuation = some (.discard, body) →
      StepIn table globals (.receiving heap caller stack (.ok value)) none
        (.running heap caller.frame body stack)
  | receiveReturn {heap caller stack value} :
      caller.continuation = none →
      StepIn table globals (.receiving heap caller stack (.ok value)) none (.delivering heap stack (.ok value))
  | receiveError (heap : Heap) (caller : Call.Saved Continuation) (stack : Stack) (error : RuntimeError) :
      StepIn table globals (.receiving heap caller stack (.error error)) none (.delivering heap stack (.error error))

def observes : State → Result → Prop
  | .finished _ result, observed => result = observed
  | _, _ => False

def labelledIn (table : CodeTable) (globals : GlobalLookup) : Semantics.Operational.Labelled State Event Result where
  step := StepIn table globals
  observe source outcome := ∃ result, observes source result ∧ outcome = .returned result

abbrev Operand.eval := @Operand.evalIn layout emptyGlobals
abbrev evalArguments := @evalArgumentsIn layout emptyGlobals
abbrev evalCall := @evalCallIn layout emptyGlobals
abbrev Evaluates := @EvaluatesIn layout emptyGlobals
abbrev Arguments := @ArgumentsIn layout emptyGlobals
abbrev Inputs := @InputsIn layout emptyGlobals
abbrev Step (table : CodeTable) := StepIn table emptyGlobals
abbrev advance (table : CodeTable) := advanceIn table emptyGlobals
abbrev runPrefix (table : CodeTable) := runPrefixIn table emptyGlobals
abbrev labelled (table : CodeTable) := labelledIn table emptyGlobals

end Silmaril.Languages.Python.Core.Closure.Executor
