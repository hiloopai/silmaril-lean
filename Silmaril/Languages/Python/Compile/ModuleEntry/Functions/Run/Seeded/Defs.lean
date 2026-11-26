module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs

/-! # Run checked module-call instructions with an explicit closed seed -/

@[expose] public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Source (Name Scope)
open Core.Closure (CodeRef Function Heap)
open Core.Closure.Executor (CodeTable Fault)
open Core.Module (ListHeap ListObject)
open Core.Module.SeededCall (AssertionArgument Bindings CallObservation Expectation Failure Namespace Raised Result Value)

inductive SeedPlacement where
  | builtin
  | preamble

/-- The exception-helper projection uses the selected namespace for harness
entries and builtin fallback for the class token. -/
def legacySeed (placement : SeedPlacement) : Namespace :=
  let classes : Bindings := [("AssertionError", .exceptionClass .assertionError)]
  let helpers (diagnostic : AssertionArgument) : Bindings :=
    [("___assertEqual", .helper .assertEqual), ("___assertRaises", .helper (.assertRaises diagnostic))]
  match placement with
  | .builtin => ⟨[], classes ++ helpers .empty⟩
  | .preamble => ⟨helpers (.text "did not raise exception"), classes⟩

/-- Extend the legacy projection with the typed Boolean-to-integer call
and the mixed integer/Boolean identity assertion. The stock builtin uses
builtin fallback in either harness placement. -/
def legacyBoolIntSeed (placement : SeedPlacement) : Namespace :=
  let seed := legacySeed placement
  let comparison := ("___assertIsNot", Value.helper .assertIsNot)
  let builtins := ("int", Value.builtin .int) :: seed.builtins
  match placement with
  | .builtin => { seed with builtins := comparison :: builtins }
  | .preamble => { seed with moduleGlobals := comparison :: seed.moduleGlobals, builtins := builtins }

/-- Opt into the Boolean identity helper and the restricted `callable`
probe. Stock builtins use fallback in both harness placements. -/
def legacyBoolCallableSeed (placement : SeedPlacement) : Namespace :=
  let seed := legacySeed placement
  let identity := ("___assertIs", Value.helper .assertIs)
  let builtins := [("callable", Value.builtin .callable), ("len", Value.builtin .len)] ++ seed.builtins
  match placement with
  | .builtin => { seed with builtins := identity :: builtins }
  | .preamble => { seed with moduleGlobals := identity :: seed.moduleGlobals, builtins := builtins }

/-- Opt into the Boolean identity helper and the three stock
`isinstance` cases. The existing `int` descriptor also names the type. -/
def legacyBoolIsinstanceSeed (placement : SeedPlacement) : Namespace :=
  let seed := legacySeed placement
  let identity := ("___assertIs", Value.helper .assertIs)
  let stock : Bindings := [("isinstance", .builtin .isinstance), ("bool", .builtin .bool), ("int", .builtin .int)]
  let builtins := stock ++ seed.builtins
  match placement with
  | .builtin => { seed with builtins := identity :: builtins }
  | .preamble => { seed with moduleGlobals := identity :: seed.moduleGlobals, builtins := builtins }

/-- Stock list construction is a separate opt-in profile. -/
def legacyListSeed (placement : SeedPlacement) : Namespace :=
  let seed := legacySeed placement
  { seed with builtins := ("list", .builtin .list) :: seed.builtins }

def lowerCallOperand : Core.Module.Functions.Operand → Core.Module.SeededCall.Operand 0
  | .readGlobal name => .global name
  | .literal (.int value) => .literal (.int value)
  | .literal (.bool value) => .literal (.bool value)
  | .literal _ => .unsupported

def lowerScalarOperand {scope : Scope} : ModuleEntry.Operand scope → Core.Module.SeededCall.Operand 0
  | .read name _ => .global name
  | .integer value => .literal (.int value)
  | .none_ => .literal .none
  | .boolean _ | .binary .. | .identityChain .. => .unsupported

def scalar? : Value → Option Core.Module.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .none => some .none
  | .exceptionClass _ | .helper _ | .builtin _ | .function _ | .listObject _ => none

/-- Observation map for the shared scalar comparison profile. -/
def scalarFailure : Completion → Failure
  | .raised error => .raised (.runtime error)
  | _ => .unsupported

/-- Boolean literals are admitted inside equality and inequality. The resulting Boolean
can be bound as a value. Other compound operands use the existing boundary. -/
def evaluateScalar {scope : Scope} (space : Namespace) (equalityOperand : Bool) :
    ModuleEntry.Operand scope → Result
  | .binary operator left right =>
    match operator with
    | .equal | .notEqual => do
      let first ← evaluateScalar space true left
      let second ← evaluateScalar space true right
      let some first := scalar? first | throw .unsupported
      let some second := scalar? second | throw .unsupported
      let same := first.equal second
      return .bool (match operator with | .notEqual => !same | _ => same)
    | _ => .error .unsupported
  | .identityChain left links =>
    let singleton value := (scalar? value).bind Core.Module.Value.singleton?
    (Core.Module.Identity.project singleton .unsupported (evaluateScalar space true left)).bind fun first =>
      (Core.Module.Identity.scan first (links.attach.map fun link =>
        (link.val.1, fun _ => Core.Module.Identity.project singleton .unsupported (evaluateScalar space true link.val.2)))).map .bool
  | .boolean value =>
    if equalityOperand then .ok (.bool value) else .error .unsupported
  | operand => (lowerScalarOperand operand).eval space #v[]
termination_by operand => sizeOf operand
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := Core.Module.Identity.sizeOf_operand_lt link.property
      omega

def truth : Value → Bool
  | .int value => decide (value ≠ 0)
  | .bool value => value
  | .none => false
  | .listObject object => !object.contents.isEmpty
  | .exceptionClass _ | .helper _ | .builtin _ => true
  | .function closure => (Core.Closure.Value.function closure).truth

def assertTruthAs (expected : Bool) (value : Value) : Except Failure Unit :=
  if truth value = expected then .ok () else .error (.raised (.assertionError .empty))

def assertTruth : Value → Except Failure Unit := assertTruthAs true

def acceptCall (destination : Core.Module.Functions.Destination) (value : Value) :
    Except Failure (Option (String × Value)) :=
  match destination with
  | .discard => .ok none
  | .bindGlobal name => .ok (some (name, value))
  | .assert => (assertTruth value).map fun _ => none

structure CallEvent where
  callee : String
  observation : CallObservation

/-- Executor faults and live prefixes are outside Python exception delivery. -/
inductive ModuleFailure where
  | raised (error : Raised)
  | unsupported
  | publicationFault (error : Core.Closure.Dispatch.Failure)
  | varNamesFault (error : Core.Closure.Dispatch.Failure)
  | callbackFault (fault : Fault)
  | callbackFuelExhausted
  | directCallFault (fault : Fault)
  | directCallFuelExhausted
  deriving DecidableEq, Repr

def ModuleFailure.ofCall : Failure → ModuleFailure
  | .raised error => .raised error
  | .unsupported => .unsupported

structure Effect where
  binding : Except ModuleFailure (Option (String × Value))
  calls : List CallEvent

def ordinaryValue? : Value → Option Core.Closure.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .none => some .none
  | .function closure => some (.function closure)
  | .exceptionClass _ | .helper _ | .builtin _ | .listObject _ => none

def seededValue : Core.Closure.Value → Value
  | .int value => .int value
  | .bool value => .bool value
  | .none => .none
  | .function closure => .function closure

def callbackSession (space : Namespace) (heap : Heap) : Core.Module.Functions.Session :=
  ⟨fun name => (space.lookupGlobal name).bind ordinaryValue?, heap⟩

def callbackInvocation (space : Namespace) (heap : Heap) (closure : Function) :
    Core.Module.Functions.Invocation :=
  (callbackSession space heap).prepareCall .discard (.literal (.function closure)) []

/-- The ordinary executor delivers an ambient lookup miss as a terminal
`nameError name`. Check the same namespace when observing the error,
since projection also drops seed-only values. -/
def callbackError (space : Namespace) (error : Core.Closure.RuntimeError) : Failure :=
  match error with
  | .nameError name =>
    match space.lookupGlobal name with
    | none => .raised (.runtime error)
    | some value =>
      if (ordinaryValue? value).isNone then .unsupported else .raised (.runtime error)
  | .assertionError => .raised (.assertionError .empty)
  | _ => .raised (.runtime error)

/-- Deliver only a completed ordinary callback to the existing expectation.
All ordinary states carry the exact heap at that point in execution. -/
def observeCallback (space : Namespace) (expectation : Expectation) :
    Core.Closure.Executor.State → Except ModuleFailure CallObservation × Heap
  | .finished heap result =>
    let inner := (result.map seededValue).mapError (callbackError space)
    (.ok ⟨expectation.deliver inner, expectation.caught? inner⟩, heap)
  | .faulted heap _ fault => (.error (.callbackFault fault), heap)
  | .running heap .. | .delivering heap .. | .receiving heap .. =>
    (.error .callbackFuelExhausted, heap)

structure CallContext where
  table : CodeTable
  heap : Heap
  fuel : Nat
  published : List Function := []
  escaped : List Function := []

/-- A bad reference is left to the ordinary executor after the descriptor
has passed the same-run ledger check. -/
def CallContext.acceptsCallFrom (context : CallContext) (ledger : List Function)
    (closure : Function) (arity : Nat) : Bool :=
  if closure ∈ ledger then
    match Core.Closure.Dispatch.resolve context.table closure.code with
    | .ok definition => definition.parameters.slots.length == arity
    | .error _ => true
  else false

def CallContext.acceptsPublishedCall (context : CallContext) (closure : Function) (arity : Nat := 0) : Bool :=
  context.acceptsCallFrom context.published closure arity

/-- Recognize returned closures and follow final calls to lexical children.
Track child code references through private locals assigned fresh closures. -/
def returnsClosure {layout : Core.Closure.Layout} (forwards : CodeRef → Bool) :
    Core.Closure.Executor.Body layout → (Fin layout.locals → Option CodeRef) → Bool
  | .ret (.closure ..), _ => true
  | .ret (.read (.local slot)), locals => (locals slot).isSome
  | .store (.local slot) value rest, locals =>
    let ref := match value with
      | .closure ref _ => some ref
      | _ => none
    returnsClosure forwards rest (fun key => if key = slot then ref else locals key)
  | .store _ _ rest, locals | .assert _ rest, locals | .callTo .discard _ _ rest, locals =>
    returnsClosure forwards rest locals
  | .callTo (.store (.local destination)) (.read (.local callee)) arguments (.ret (.read (.local result))), locals =>
    decide (destination = result ∧ arguments.length ≤ 1) && (locals callee).any forwards
  | .invoke (.closure ref _) arguments none, _ =>
    decide (arguments.length ≤ 1) && forwards ref
  | _, _ => false

/-- The pinned factory profile forwards through at most two lexical
wrappers. Dispatch faults on this path belong to ordinary execution. -/
def factoryCode (table : CodeTable) (ref : CodeRef) : Nat → Bool
  | 0 =>
    match Core.Closure.Dispatch.resolve table ref with
    | .ok definition => returnsClosure (fun _ => false) definition.body (fun _ => none)
    | .error _ => true
  | depth + 1 =>
    match Core.Closure.Dispatch.resolve table ref with
    | .ok definition => returnsClosure (fun child => factoryCode table child depth) definition.body (fun _ => none)
    | .error _ => true

/-- Both a successful entry publication and a stored factory result can
supply the live factory descriptor. The returned function must still
pass the same independent factory-body check. -/
def CallContext.acceptsFactory (context : CallContext) (closure : Function) (arity : Nat) : Bool :=
  context.acceptsCallFrom (context.published ++ context.escaped) closure arity &&
    factoryCode context.table closure.code 2

def CallContext.acceptsEscapedArgument (context : CallContext) (closure : Function) (arity : Nat := 1) : Bool :=
  context.acceptsCallFrom context.escaped closure arity

def invokeCallback (space : Namespace) (context : CallContext)
    (expectation : Expectation) (closure : Function) : Except ModuleFailure CallObservation × Heap :=
  let invocation := callbackInvocation space context.heap closure
  observeCallback space expectation (invocation.runPrefix context.table context.fuel).2.state

def invokeCall (space : Namespace) (context : CallContext) (callee : Value) (arguments : List Value) :
    Except ModuleFailure CallObservation × Heap :=
  match Core.Module.SeededCall.Request.decode callee arguments with
  | .expect expectation (.function closure) [] _ =>
    if context.acceptsPublishedCall closure then invokeCallback space context expectation closure
    else (.ok ⟨.error .unsupported, none⟩, context.heap)
  | _ => (.ok (Core.Module.SeededCall.invokeObserved callee arguments), context.heap)

/-- Only a finished invocation issues a receipt. Faults and live prefixes
carry the exact heap reached by ordinary execution. -/
def observeDirectCall (space : Namespace) :
    Core.Closure.Executor.State → Except ModuleFailure CallObservation × Heap
  | .finished heap result =>
    (.ok ⟨(result.map seededValue).mapError (callbackError space), none⟩, heap)
  | .faulted heap _ fault => (.error (.directCallFault fault), heap)
  | .running heap .. | .delivering heap .. | .receiving heap .. =>
    (.error .directCallFuelExhausted, heap)

def ordinaryCall (space : Namespace) (context : CallContext) (closure : Function)
    (arguments : List Core.Module.Functions.Operand) : Core.Closure.Executor.State :=
  let invocation := (callbackSession space context.heap).prepareCall .discard (.literal (.function closure)) arguments
  (invocation.runPrefix context.table context.fuel).2.state

def factoryOperand : Value → Option Core.Module.Functions.Operand
  | .int value => some (.literal (.int value))
  | _ => none

/-- The fixed factory slice supplies at most three exact integers. The
ordinary binder checks the slot count and initializes destinations in order. -/
def factoryOperands (values : List Value) : Option (List Core.Module.Functions.Operand) :=
  if values.length ≤ 3 then values.mapM factoryOperand else none

/-- Only a successful closure result can write the factory destination. -/
def observeFactory (space : Namespace) (state : Core.Closure.Executor.State) :
    Except ModuleFailure CallObservation × Heap :=
  match state with
  | .finished heap (.ok (.int _)) | .finished heap (.ok (.bool _)) | .finished heap (.ok .none) =>
    (.ok ⟨.error .unsupported, none⟩, heap)
  | _ => observeDirectCall space state

/-- Dispatch an already resolved flat call. Factory binding uses the current
run's recorded descriptors and the bounded fixed integer argument profile. -/
def invokeFlatCall (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) (callee : Value) (arguments : List Value) :
    Except ModuleFailure CallObservation × Heap :=
  match destination, callee, arguments with
  | .discard, .function closure, [] =>
    if context.acceptsPublishedCall closure then
      let invocation := callbackInvocation space context.heap closure
      observeDirectCall space (invocation.runPrefix context.table context.fuel).2.state
    else (.ok ⟨.error .unsupported, none⟩, context.heap)
  | .bindGlobal _, .function closure, values =>
    match factoryOperands values with
    | some operands =>
      if context.acceptsFactory closure operands.length then
        observeFactory space (ordinaryCall space context closure operands)
      else (.ok ⟨.error .unsupported, none⟩, context.heap)
    | none => (.ok ⟨.error .unsupported, none⟩, context.heap)
  | _, _, _ => invokeCall space context callee arguments

/-- Direct calls of checked defaulted bindings use the already evaluated
scalar arguments. The ordinary binder handles both missing and extra arguments. -/
def invokeNamedFlatCall (space : Namespace) (context : CallContext) (defaultedNames : List Name)
    (destination : Core.Module.Functions.Destination) (name : Name) (callee : Value) (arguments : List Value) :
    Except ModuleFailure CallObservation × Heap :=
  if defaultedNames.contains name then
    match callee, arguments.mapM scalar? with
    | .function closure, some values =>
      let operands := values.map fun value => Core.Module.Functions.Operand.literal (.ofScalar value)
      observeDirectCall space (ordinaryCall space context closure operands)
    | _, _ => (.ok ⟨.error .unsupported, none⟩, context.heap)
  else invokeFlatCall space context destination callee arguments

/-- The adjacent source guard establishes the name-to-slot mapping. Read the
live module-first binding once and enter only a published one-slot function. -/
def invokeAdjacentKeywordDiscard (space : Namespace) (context : CallContext)
    (name : String) (value : Int) : Except ModuleFailure CallObservation × Heap :=
  match space.lookupGlobal name with
  | none => (.ok ⟨.error (.raised (.runtime (.nameError name))), none⟩, context.heap)
  | some (.function closure) =>
    if context.acceptsPublishedCall closure 1 then
      let invocation := (callbackSession space context.heap).prepareCall .discard
        (.literal (.function closure)) [.literal (.int value)]
      observeDirectCall space (invocation.runPrefix context.table context.fuel).2.state
    else (.ok ⟨.error .unsupported, none⟩, context.heap)
  | some _ => (.ok ⟨.error .unsupported, none⟩, context.heap)

def acceptObservation (destination : Core.Module.Functions.Destination)
    (name : String) (observed : CallObservation) : Effect :=
  ⟨(observed.result.bind (acceptCall destination)).mapError ModuleFailure.ofCall, [⟨name, observed⟩]⟩

def observeNamedCall (space : Namespace) (name : String)
    (arguments : List Core.Module.Functions.Operand) : CallEvent :=
  ⟨name, Core.Module.SeededCall.runObserved space #v[] (.global name) (arguments.map lowerCallOperand)⟩

def observeArgument (space : Namespace) : Argument → Result × List CallEvent
  | .scalar operand => ((lowerCallOperand operand).eval space #v[], [])
  | .call name arguments =>
    let event := observeNamedCall space name arguments
    (event.observation.result, [event])

def observeArguments (space : Namespace) :
    List Argument → Except Failure (List Value) × List CallEvent
  | [] => (.ok [], [])
  | argument :: rest =>
    let (result, calls) := observeArgument space argument
    match result with
    | .error error => (.error error, calls)
    | .ok value =>
      let (values, later) := observeArguments space rest
      (values.map (value :: ·), calls ++ later)

/-- A nested call resolves the outer name before visiting its arguments.
Only after those arguments return does it invoke the saved value. -/
def observeNestedCall (space : Namespace) (destination : Core.Module.Functions.Destination)
    (name : String) (arguments : List Argument) : Effect :=
  match space.lookupGlobal name with
  | none => ⟨.error (.raised (.runtime (.nameError name))), []⟩
  | some callee =>
    let (values, calls) := observeArguments space arguments
    match values with
    | .error error => ⟨.error (.ofCall error), calls⟩
    | .ok values =>
      let observed := Core.Module.SeededCall.invokeObserved callee values
      ⟨(observed.result.bind (acceptCall destination)).mapError ModuleFailure.ofCall,
        calls ++ [⟨name, observed⟩]⟩

/-- The published zero-argument path and the checked escaped zero/one
argument paths carry their result and reached heap to the next argument. -/
def observeArgumentIn (space : Namespace) (context : CallContext) (argument : Argument)
    (allowEscaped : Bool := false) : Except ModuleFailure Value × List CallEvent × Heap :=
  match argument with
  | .scalar operand =>
    (((lowerCallOperand operand).eval space #v[]).mapError .ofCall, [], context.heap)
  | .call name arguments =>
    let outcome : Except ModuleFailure CallObservation × Heap :=
      match Core.Module.SeededCall.resolveCall space #v[] (.global name) (arguments.map lowerCallOperand) with
      | .error error => (.ok ⟨.error error, none⟩, context.heap)
      | .ok (callee, values) =>
        match callee, values with
        | .function closure, [] =>
          if allowEscaped && context.acceptsEscapedArgument closure 0 then
            observeDirectCall space (ordinaryCall space context closure [])
          else invokeFlatCall space context .discard callee values
        | .function closure, [.int value] =>
          if allowEscaped && context.acceptsEscapedArgument closure then
            observeDirectCall space (ordinaryCall space context closure [.literal (.int value)])
          else (.ok ⟨.error .unsupported, none⟩, context.heap)
        | _, _ => (.ok (Core.Module.SeededCall.invokeObserved callee values), context.heap)
    match outcome with
    | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
    | (.error error, heap) => (.error error, [], heap)

def observeArgumentsIn (space : Namespace) (context : CallContext) (arguments : List Argument)
    (allowEscaped : Bool := false) : Except ModuleFailure (List Value) × List CallEvent × Heap :=
  match arguments with
  | [] => (.ok [], [], context.heap)
  | argument :: rest =>
    let (result, calls, heap) := observeArgumentIn space context argument allowEscaped
    match result with
    | .error error => (.error error, calls, heap)
    | .ok value =>
      let (values, later, residual) := observeArgumentsIn space { context with heap } rest allowEscaped
      (values.map (value :: ·), calls ++ later, residual)

def allowsEscapedArgument : Core.Module.Functions.Destination → Value → Bool
  | .discard, .helper .assertEqual => true
  | _, _ => false

/-- Read the outer callee before the arguments and retain the heap reached
even when an ordinary argument faults or has yet to settle. -/
def observeNestedCallIn (space : Namespace) (context : CallContext)
    (destination : Core.Module.Functions.Destination) (name : String)
    (arguments : List Argument) : Effect × Heap :=
  match space.lookupGlobal name with
  | none => (⟨.error (.raised (.runtime (.nameError name))), []⟩, context.heap)
  | some callee =>
    let (values, calls, heap) := observeArgumentsIn space context arguments (allowsEscapedArgument destination callee)
    match values with
    | .error error => (⟨.error error, calls⟩, heap)
    | .ok values =>
      let observed := acceptObservation destination name (Core.Module.SeededCall.invokeObserved callee values)
      ({ observed with calls := calls ++ observed.calls }, heap)

inductive EvaluatesArguments (space : Namespace) :
    List Argument → Except Failure (List Value) → List CallEvent → Prop where
  | nil : EvaluatesArguments space [] (.ok []) []
  | stop {argument rest error calls}
      (failed : observeArgument space argument = (.error error, calls)) :
      EvaluatesArguments space (argument :: rest) (.error error) calls
  | next {argument rest value calls values later}
      (evaluated : observeArgument space argument = (.ok value, calls))
      (tail : EvaluatesArguments space rest values later) :
      EvaluatesArguments space (argument :: rest) (values.map (value :: ·)) (calls ++ later)

def assertOperand {scope : Scope} (space : Namespace) (operand : ModuleEntry.Operand scope)
    (expected : Bool) : Effect :=
  let checked := (evaluateScalar space false operand).bind (assertTruthAs expected)
  ⟨(checked.map fun _ => none).mapError ModuleFailure.ofCall, []⟩

/-- The checked argument cannot escape this call. Only the exact stock
descriptor consumes its certified length. -/
def readSequenceLength (space : Namespace) (length : Nat) : Except Failure Int :=
  match space.lookupGlobal "len" with
  | none => .error (.raised (.runtime (.nameError "len")))
  | some (.builtin .len) => .ok (Int.ofNat length)
  | some (.int _) | some (.bool _) | some .none => .error (.raised (.runtime .notCallable))
  | some _ => .error .unsupported

def checkSequenceLengthResult {scope : Scope} (space : Namespace) (test : SequenceLengthTest scope)
    (length : Int) : Except Failure Unit := do
  let actual ← evaluateScalar space true test.right
  let some right := scalar? actual | throw .unsupported
  assertTruthAs test.expectedEqual (.bool ((.int length : Core.Module.Value).equal right))

def assertSequenceLength {scope : Scope} (space : Namespace) (test : SequenceLengthTest scope) : Effect :=
  let result := readSequenceLength space test.length
  let checked := result.bind (checkSequenceLengthResult space test)
  ⟨(checked.map fun _ => none).mapError ModuleFailure.ofCall, [⟨"len", ⟨result.map .int, none⟩⟩]⟩

/-- Only a checked list argument allocates a list before constructor dispatch. -/
def prepareListArgument (heap : ListHeap) : ListConstructorArgument → List Core.Module.Value × ListHeap
  | .omitted => ([], heap)
  | .literal sequence =>
    match sequence.kind with
    | .tuple => (sequence.values, heap)
    | .list => (sequence.values, (heap.allocate sequence.values).2)

def constructList (space : Namespace) (heap : ListHeap) (argument : ListConstructorArgument) :
    Except Failure ListObject × ListHeap :=
  match space.lookupGlobal "list" with
  | none => (.error (.raised (.runtime (.nameError "list"))), heap)
  | some callee =>
    let (contents, reached) := prepareListArgument heap argument
    match callee with
    | .builtin .list =>
      let (object, updated) := reached.allocate contents
      (.ok object, updated)
    | .int _ | .bool _ | .none | .listObject _ => (.error (.raised (.runtime .notCallable)), reached)
    | _ => (.error .unsupported, reached)

def listEquality (left right : ListObject) : Bool :=
  ClosedSequence.equal ⟨.list, left.contents⟩ ⟨.list, right.contents⟩

structure ListConstructionOutcome where
  result : Except Failure ListObject
  comparison : Except Failure Bool
  lists : ListHeap

def evaluateListConstruction {scope : Scope} (space : Namespace) (heap : ListHeap)
    (test : ListConstructionTest scope) : ListConstructionOutcome :=
  match test.order with
  | .constructorFirst =>
    let (result, reached) := constructList space heap test.argument
    match result with
    | .error error => ⟨result, .error error, reached⟩
    | .ok left =>
      let (right, updated) := reached.allocate test.literal
      ⟨result, .ok (listEquality left right), updated⟩
  | .literalFirst =>
    let (left, updated) := heap.allocate test.literal
    let (result, reached) := constructList space updated test.argument
    ⟨result, result.map (listEquality left), reached⟩

def ListConstructionOutcome.checked (outcome : ListConstructionOutcome) : Except Failure Unit :=
  outcome.comparison.bind fun value => assertTruth (.bool value)

def ListConstructionOutcome.receipt (outcome : ListConstructionOutcome) : CallEvent :=
  ⟨"list", ⟨outcome.result.map .listObject, none⟩⟩

def ListConstructionOutcome.effect (outcome : ListConstructionOutcome) : Effect :=
  ⟨(outcome.checked.map fun _ => none).mapError ModuleFailure.ofCall, [outcome.receipt]⟩

/-- Resolve once in the live seeded namespace. A masking module value
remains the receiver even when its type is outside the ordinary profile. -/
def checkVarNames (space : Namespace) (table : CodeTable) (receiver : String)
    (needle : List UInt32) : Except ModuleFailure Unit := do
  let some value := space.lookupGlobal receiver | throw (.raised (.runtime (.nameError receiver)))
  let some ordinary := ordinaryValue? value | throw .unsupported
  let member ← (Run.varNamesMembership table ordinary needle).mapError fun
    | .unsupportedReceiver | .unprofiled _ => .unsupported
    | .code error => .varNamesFault error
  (assertTruth (.bool member)).mapError ModuleFailure.ofCall

def readDefault (space : Namespace) (name : Name) : Except ModuleFailure Core.Module.Value := do
  let some value := space.lookupGlobal name | throw (.raised (.runtime (.nameError name)))
  let some scalar := scalar? value | throw .unsupported
  return scalar

def defaultPublication {scope : Scope} (space : Namespace) (table : CodeTable) (name : Name)
    (function : Core.Module.Functions.TopFunction) (operands : List (DefaultOperand scope)) :
    Except ModuleFailure (Option (Name × Value)) := do
  let saved ← Run.captureDefaults (readDefault space) operands
  let _ ← (Core.Closure.Dispatch.resolve table function.ref).mapError .publicationFault
  return some (name, .function (function.withDefaults saved))

/-- Propagate same-run authorization through actual assignments, and drop it
on overwrite. Each initial seed starts with an empty authorization list. -/
def updateDefaultedNames {scope : Scope} (instruction : Instruction scope)
    (names : List Name) : Option (Name × Value) → List Name
  | some (name, .function _) =>
    match instruction with
    | .publishDefaults .. => name :: names.erase name
    | .scalar (.assign _ _ (.read source _)) =>
      if names.contains source then name :: names.erase name else names.erase name
    | _ => names.erase name
  | some (name, _) => names.erase name
  | none => names

def effect {scope : Scope} (space : Namespace) (context : CallContext) (instruction : Instruction scope)
    (lists : ListHeap := .empty) (defaultedNames : List Name := []) : Effect × Heap :=
  match instruction with
  | .scalar (.assign name _ operand) =>
    (⟨((evaluateScalar space false operand).map fun value => some (name, value)).mapError ModuleFailure.ofCall,
      []⟩, context.heap)
  | .scalar (.assertion operand) => (assertOperand space operand true, context.heap)
  | .assertNot operand => (assertOperand space operand false, context.heap)
  | .assertSequenceLength test => (assertSequenceLength space test, context.heap)
  | .assertListConstruction test => ((evaluateListConstruction space lists test).effect, context.heap)
  | .assertVarNames receiver needle =>
    (⟨(checkVarNames space context.table receiver needle).map fun _ => none, []⟩, context.heap)
  | .publish name function =>
    let resolved := Core.Closure.Dispatch.resolve context.table function.ref
    (⟨(resolved.map fun _ => some (name, .function function.closure)).mapError .publicationFault, []⟩, context.heap)
  | .publishDefaults name function operands =>
    (⟨defaultPublication space context.table name function operands, []⟩, context.heap)
  | .call destination name arguments =>
    match Core.Module.SeededCall.resolveCall space #v[] (.global name) (arguments.map lowerCallOperand) with
    | .error error => (acceptObservation destination name ⟨.error error, none⟩, context.heap)
    | .ok (callee, values) =>
      let (observed, heap) := invokeNamedFlatCall space context defaultedNames destination name callee values
      match observed with
      | .ok result => (acceptObservation destination name result, heap)
      | .error error => (⟨.error error, []⟩, heap)
  | .adjacentKeywordDiscard name value =>
    match invokeAdjacentKeywordDiscard space context name value with
    | (.ok observed, heap) => (acceptObservation .discard name observed, heap)
    | (.error error, heap) => (⟨.error error, []⟩, heap)
  | .nestedCall destination name arguments => observeNestedCallIn space context destination name arguments

structure Observation where
  residual : Namespace
  completion : Except ModuleFailure Unit
  calls : List CallEvent
  heap : Heap
  lists : ListHeap

def effectWithLists {scope : Scope} (space : Namespace) (context : CallContext)
    (instruction : Instruction scope) (lists : ListHeap) (defaultedNames : List Name := []) : (Effect × Heap) × ListHeap :=
  match instruction with
  | .assertListConstruction test =>
    let outcome := evaluateListConstruction space lists test
    ((outcome.effect, context.heap), outcome.lists)
  | instruction => (effect space context instruction lists defaultedNames, lists)

/-- A failed instruction keeps its incoming namespace and the heap reached
by its effects. Successful publications authorize checked ordinary calls. -/
def runInstructionsIn {scope : Scope} (space : Namespace) (context : CallContext)
    (instructions : List (Instruction scope)) (lists : ListHeap := .empty) (defaultedNames : List Name := []) : Observation :=
  match instructions with
  | [] => ⟨space, .ok (), [], context.heap, lists⟩
  | instruction :: rest =>
    let ((item, heap), updatedLists) := effectWithLists space context instruction lists defaultedNames
    match item.binding with
    | .error error => ⟨space, .error error, item.calls, heap, updatedLists⟩
    | .ok binding =>
      let updated := binding.elim space fun (name, value) => space.bindGlobal name value
      let published := match instruction with
        | .publish _ function => function.closure :: context.published
        | _ => context.published
      let escaped := match instruction, binding with
        | .call (.bindGlobal _) callee _, some (_, .function closure) =>
          if defaultedNames.contains callee then context.escaped else closure :: context.escaped
        | _, _ => context.escaped
      let names := updateDefaultedNames instruction defaultedNames binding
      let tail := runInstructionsIn updated { context with heap, published, escaped } rest updatedLists names
      { tail with calls := item.calls ++ tail.calls }

def runInstructions {scope : Scope} (space : Namespace) (instructions : List (Instruction scope))
    (table : CodeTable := fun _ => none) (heap : Heap := .empty) (callbackFuel : Nat := 1000)
    (lists : ListHeap := .empty) : Observation :=
  runInstructionsIn space { table, heap, fuel := callbackFuel } instructions lists

/-- Seeded execution starts from the same compiled instruction stream as
ordinary module execution. The caller supplies the namespace explicitly. -/
def run {source : Source.Module} (space : Namespace) (compiled : Compiled source)
    (heap : Heap := .empty) (callbackFuel : Nat := 1000) (lists : ListHeap := .empty) : Observation :=
  runInstructions space compiled.instructions compiled.table heap callbackFuel lists

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
