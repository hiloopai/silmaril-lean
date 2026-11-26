module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
import Silmaril.Languages.Python.Compile.ModuleEntry.Thms
public import Silmaril.Languages.Python.Core.Module.Functions.Thms
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (CallObservation Delivers Expectation Failure Namespace Raised Value)
open Core.Module.Functions (TopFunction)
open Core.Closure (Function Heap)
open Core.Closure.Executor (Fault labelledIn)

theorem observeArguments_iff {space : Namespace} {arguments : List Argument}
    {values : Except Failure (List Value)} {calls : List CallEvent} :
    observeArguments space arguments = (values, calls) ↔ EvaluatesArguments space arguments values calls :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.observeArguments_iff

theorem observeNestedCall_missing {space : Namespace} {destination : Core.Module.Functions.Destination}
    {name : String} {arguments : List Argument} (missing : space.lookupGlobal name = none) :
    observeNestedCall space destination name arguments = ⟨.error (.raised (.runtime (.nameError name))), []⟩ :=
  by simp [observeNestedCall, missing]

theorem observeNestedCall_failedArguments {space : Namespace} {destination : Core.Module.Functions.Destination}
    {name : String} {callee : Value} {arguments : List Argument} {error : Failure} {calls : List CallEvent}
    (found : space.lookupGlobal name = some callee)
    (failed : EvaluatesArguments space arguments (.error error) calls) :
    observeNestedCall space destination name arguments = ⟨.error (.ofCall error), calls⟩ :=
  by simp [observeNestedCall, found, observeArguments_iff.mpr failed]

theorem run_preserves_builtins {source : Source.Module} (space : Namespace) (compiled : Compiled source)
    (heap : Heap := .empty) (fuel : Nat := 1000) :
    (run space compiled heap fuel).residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_builtins
    space compiled.instructions { table := compiled.table, heap, fuel }

/-- The comparison profile gives identical values and defined failures when
both runners observe the same globals. -/
theorem evaluateScalar_comparable {scope : Source.Scope} (space : Namespace)
    (session : Core.Module.Functions.Session)
    (reads : ∀ name, space.lookupGlobal name = (session.globals name).map seededValue)
    (operand : Operand scope) (admitted : operand.comparable = true) :
    evaluateScalar space true operand = ((Run.evaluate session operand).map seededValue).mapError scalarFailure :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity.evaluateScalar_agrees
    space session reads operand admitted

theorem evaluate_singletonResult {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (operand : Operand scope) (certified : operand.singletonResult = true) (value : Core.Closure.Value)
    (evaluated : Run.evaluate session operand = .ok value) :
    ∃ exact, (Run.scalar? value).bind Core.Module.Value.singleton? = some exact :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity.evaluate_singletonResult
    session operand certified value evaluated

theorem evaluateScalar_identityContext {scope : Source.Scope} (space : Namespace)
    (left : Operand scope) (links : List (Core.Module.IdentityOperator × Operand scope)) :
    evaluateScalar space false (.identityChain left links) = evaluateScalar space true (.identityChain left links) := by
  rw [evaluateScalar, evaluateScalar]

theorem run_identityAssertion {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (left : Operand scope) (links : List (Core.Module.IdentityOperator × Operand scope)) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (.assertion (.identityChain left links)) :: rest) =
      match (assertOperand space (.identityChain left links) true).binding with
      | .ok _ => runInstructionsIn space context rest
      | .error error => ⟨space, .error error, [], context.heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity.run_identityAssertion space context left links rest

theorem evaluateScalar_conditionalResult {scope : Source.Scope} (space : Namespace)
    (equalityOperand : Bool) (operand : ModuleEntry.Operand scope) :
    evaluateScalar space equalityOperand operand.conditionalResult =
      match operand with
      | .boolean value => .ok (.bool value)
      | other => evaluateScalar space equalityOperand other := by
  cases operand with
  | boolean value => cases value <;> simp [Operand.conditionalResult, Operand.booleanResult, evaluateScalar] <;> rfl
  | _ => rfl

theorem evaluateScalar_booleanResult {scope : Source.Scope} (space : Namespace)
    (equalityOperand value : Bool) :
    evaluateScalar space equalityOperand (ModuleEntry.Operand.booleanResult (scope := scope) value) =
      .ok (.bool value) :=
  evaluateScalar_conditionalResult space equalityOperand (.boolean value)

theorem evaluateScalar_scalarResult {scope : Source.Scope} (space : Namespace) (equalityOperand : Bool)
    (value : Core.Module.Value) :
    evaluateScalar space equalityOperand (ModuleEntry.Operand.scalarResult (scope := scope) value) =
      .ok (seededValue (Run.embed value)) := by
  cases value with
  | int value => simp [Operand.scalarResult, evaluateScalar, lowerScalarOperand]; rfl
  | bool value => exact evaluateScalar_booleanResult space equalityOperand value
  | none => simp [Operand.scalarResult, evaluateScalar, lowerScalarOperand]; rfl

/-- A certified Boolean selection evaluates to the same tagged scalar in
both runners, independently of their incoming namespaces. -/
theorem evaluate_checkedBooleanOp {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (space : Namespace) (context : Bool) {operator : Source.BooleanOperator} {operands : List Source.Expr}
    {value : Core.Module.Value} (checked : checkedBooleanOp? operator operands = some value) :
    (lowerOperand scope (.booleanOp operator operands)).map
        (fun operand => Run.evaluate session operand.val) = .ok (.ok (Run.embed value)) ∧
      (lowerOperand scope (.booleanOp operator operands)).map
        (fun operand => evaluateScalar space context operand.val) = .ok (.ok (seededValue (Run.embed value))) := by
  rw [lower_checkedBooleanOp checked]
  simp [Except.map, Run.evaluate_scalarResult, evaluateScalar_scalarResult]

theorem evaluate_closedSequenceComparison {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (space : Namespace) (context : Bool) {left right : Source.Expr} {operator : Source.Comparison}
    {value : Bool} (checked : closedSequenceComparison? left operator right = some value) :
    (lowerOperand scope (.comparison left [(operator, right)])).map
        (fun operand => Run.evaluate session operand.val) = .ok (.ok (.bool value)) ∧
      (lowerOperand scope (.comparison left [(operator, right)])).map
        (fun operand => evaluateScalar space context operand.val) = .ok (.ok (.bool value)) := by
  rw [lower_closedSequenceComparison checked]
  simp only [Except.map, Except.ok.injEq]
  exact ⟨Run.evaluate_scalarResult session (.bool value), evaluateScalar_booleanResult space context value⟩

theorem evaluateScalar_notEqual {scope : Source.Scope} (space : Namespace) (context : Bool)
    (left right : ModuleEntry.Operand scope) :
    evaluateScalar space context (.binary .notEqual left right) = (do
      let first ← evaluateScalar space true left
      let second ← evaluateScalar space true right
      let some first := scalar? first | throw .unsupported
      let some second := scalar? second | throw .unsupported
      return .bool (!first.equal second)) := by rw [evaluateScalar]; rfl

theorem effect_scalarResultAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (reference : ModuleEntry.GlobalReference scope name) (value : Core.Module.Value) :
    effect space context (.scalar (.assign name reference (.scalarResult value))) =
      (⟨.ok (some (name, seededValue (Run.embed value))), []⟩, context.heap) := by
  simp only [effect, evaluateScalar_scalarResult]
  rfl

theorem truth_scalar {value : Core.Module.Value} : truth (seededValue (Run.embed value)) = value.truth := by
  cases value <;> rfl

theorem assertOperand_scalarResult {scope : Source.Scope} (space : Namespace) (value : Core.Module.Value)
    (expected : Bool) :
    assertOperand space (ModuleEntry.Operand.scalarResult (scope := scope) value) expected =
      ⟨if value.truth = expected then .ok none else .error (.raised (.assertionError .empty)), []⟩ := by
  simp only [assertOperand, evaluateScalar_scalarResult, Except.bind, assertTruthAs, truth_scalar]
  split <;> rfl

theorem run_scalarResultAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (reference : ModuleEntry.GlobalReference scope name) (value : Core.Module.Value)
    (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (.assign name reference (.scalarResult value)) :: rest) =
      runInstructionsIn (space.bindGlobal name (seededValue (Run.embed value))) context rest := by
  simp [runInstructionsIn, effect_scalarResultAssign]

theorem run_scalarResultAssert {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (value : Core.Module.Value) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (.assertion (.scalarResult value)) :: rest) =
      if value.truth then runInstructionsIn space context rest
      else ⟨space, .error (.raised (.assertionError .empty)), [], context.heap⟩ := by
  by_cases h : value.truth <;> simp [runInstructionsIn, effect, assertOperand_scalarResult, h]

theorem effect_conditionalAssign {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (name : Source.Name) (reference : ModuleEntry.GlobalReference scope name) (selected : ModuleEntry.Operand scope) :
    effect space context (.scalar (.assign name reference selected.conditionalResult)) =
      let result : Core.Module.SeededCall.Result := match selected with
        | .boolean value => .ok (.bool value)
        | other => evaluateScalar space false other
      (⟨(result.map fun value => some (name, value)).mapError ModuleFailure.ofCall, []⟩, context.heap) := by
  simp only [effect, evaluateScalar_conditionalResult]

theorem effect_conditionalAssert {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (selected : ModuleEntry.Operand scope) :
    effect space context (.scalar (.assertion selected.conditionalResult)) =
      let result : Core.Module.SeededCall.Result := match selected with
        | .boolean value => .ok (.bool value)
        | other => evaluateScalar space false other
      let checked := result.bind (assertTruthAs true)
      (⟨(checked.map fun _ => none).mapError ModuleFailure.ofCall, []⟩, context.heap) := by
  simp only [effect, assertOperand, evaluateScalar_conditionalResult]

theorem callback_path (space : Namespace) (context : CallContext) (closure : Function) :
    let invocation := callbackInvocation space context.heap closure
    let (events, residual) := invocation.runPrefix context.table context.fuel
    (labelledIn context.table (callbackSession space context.heap).globals).Path
      invocation.state events residual.state :=
  (callbackInvocation space context.heap closure).run_path context.table context.fuel

theorem callback_delivers {space : Namespace} {expectation : Expectation}
    {heap residual : Heap} {result : Core.Closure.Result} {observation : CallObservation} :
    observeCallback space expectation (.finished heap result) = (.ok observation, residual) ↔
      let inner := (result.map seededValue).mapError (callbackError space)
      Delivers expectation inner observation.result ∧
        observation.caught = expectation.caught? inner ∧ residual = heap := by
  cases observation
  simp [observeCallback, Expectation.delivers_iff.symm, eq_comm, and_assoc]

theorem invokeCall_published {space : Namespace} {context : CallContext} {closure : Function}
    (expectation : Expectation)
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    (published : closure ∈ context.published)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (noParameters : definition.parameters.slots = []) :
    invokeCall space context (.helper (.assertRaises expectation.onReturn))
        [.exceptionClass expectation.expected, .function closure] =
      invokeCallback space context expectation closure := by
  cases expectation
  simp [invokeCall, CallContext.acceptsPublishedCall, CallContext.acceptsCallFrom, Core.Module.SeededCall.Request.decode, published, resolved,
    noParameters]

theorem callback_fault (space : Namespace) (expectation : Expectation) (heap : Heap)
    (stack : Core.Closure.Executor.Stack) (fault : Fault) :
    observeCallback space expectation (.faulted heap stack fault) = (.error (.callbackFault fault), heap) := rfl

theorem callback_seedOnlyGlobal {space : Namespace} {heap : Heap} {name : String} {value : Value}
    (found : space.lookupGlobal name = some value) (unsupported : ordinaryValue? value = none) :
    (callbackSession space heap).globals name = none ∧
      callbackError space (.nameError name) = .unsupported := by
  simp [callbackSession, callbackError, found, unsupported]

theorem failing_instruction {scope : Source.Scope} {space : Namespace} {instruction : Instruction scope}
    {rest : List (Instruction scope)} {error : ModuleFailure}
    {context : CallContext} (failed : (effect space context instruction).1.binding = .error error) :
    runInstructionsIn space context (instruction :: rest) =
      ⟨space, .error error, (effect space context instruction).1.calls, (effect space context instruction).2⟩ :=
  by simp [runInstructionsIn, failed]

theorem run_literalArmBoolean {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (value : Bool) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (ModuleEntry.Action.assertion (.boolean value)).inLiteralArm :: rest) =
      if value then runInstructionsIn space context rest
      else ⟨space, .error (.raised (.assertionError .empty)), [], context.heap⟩ := by
  cases value <;> simp [Action.inLiteralArm, runInstructionsIn, effect, assertOperand,
    evaluateScalar, lowerScalarOperand, Core.Module.SeededCall.Operand.eval] <;> rfl

/-- Settle one direct discard call from the actual executor state. A
finished call emits one receipt before its tail, and a failed call skips the tail. -/
theorem run_directDiscard {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure = true) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      let invocation := callbackInvocation space context.heap closure
      match (invocation.runPrefix context.table context.fuel).2.state with
      | .finished heap (.ok value) =>
        let tail := runInstructionsIn space { context with heap } rest
        { tail with calls := ⟨name, ⟨.ok (seededValue value), none⟩⟩ :: tail.calls }
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard found admitted

theorem run_directDiscard_unsupported {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (rejected : context.acceptsPublishedCall closure = false) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard_unsupported found rejected

theorem run_publication {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body function.ref.layout}
    (resolved : Core.Closure.Dispatch.resolve context.table function.ref = .ok definition) :
    runInstructionsIn space context (.publish name function :: rest) =
      runInstructionsIn (space.bindGlobal name (.function function.closure))
        { context with published := function.closure :: context.published } rest :=
  by simp [runInstructionsIn, effect, resolved, Except.map, Except.mapError]

theorem run_publication_fault {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)} {error : Core.Closure.Dispatch.Failure}
    (failed : Core.Closure.Dispatch.resolve context.table function.ref = .error error) :
    runInstructionsIn space context (.publish name function :: rest) =
      ⟨space, .error (.publicationFault error), [], context.heap⟩ :=
  by simp [runInstructionsIn, effect, failed, Except.map, Except.mapError]

theorem assertNot_operand_failure {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {operand : ModuleEntry.Operand scope} {error : Failure}
    (failed : evaluateScalar space false operand = .error error) :
    effect space context (.assertNot operand) = (⟨.error (.ofCall error), []⟩, context.heap) :=
  by simp [effect, assertOperand, failed, Except.bind, Except.map, Except.mapError]

theorem effect_assertVarNames {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (receiver : String) (needle : List UInt32) :
    effect space context (.assertVarNames receiver needle : Instruction scope) =
      (⟨(checkVarNames space context.table receiver needle).map fun _ => none, []⟩, context.heap) := rfl

theorem lowerCallOperand_none : lowerCallOperand (.literal .none) = .literal .none := rfl

/-- Lookup precedes the singleton operand and its remaining operands. The
singleton is a successful value and carries no namespace or heap effect. -/
theorem resolveCall_none (space : Namespace) (name : String) (rest : List Core.Module.Functions.Operand) :
    Core.Module.SeededCall.resolveCall space #v[] (.global name)
      ((.literal .none :: rest).map lowerCallOperand) =
      ((Core.Module.SeededCall.Operand.global name).eval space #v[]).bind fun callee =>
        (Core.Module.SeededCall.Operand.evalList space #v[] (rest.map lowerCallOperand)).map fun values =>
          (callee, .none :: values) := by
  simp only [Core.Module.SeededCall.resolveCall, List.map_cons, lowerCallOperand_none,
    Core.Module.SeededCall.Operand.evalList]
  cases (Core.Module.SeededCall.Operand.global name).eval space #v[] <;>
    cases Core.Module.SeededCall.Operand.evalList space #v[] (rest.map lowerCallOperand) <;> rfl

theorem factoryOperands_iff {values : List Value} {operands : List Core.Module.Functions.Operand} :
    factoryOperands values = some operands ↔
      ∃ literals : List Core.Closure.Value, literals.length ≤ 3 ∧
        (∀ literal ∈ literals, literal = .none ∨ ∃ n, literal = .int n) ∧
        values = literals.map seededValue ∧ operands = literals.map .literal :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.factoryOperands_iff

/-- Checked operands evaluate to the exact supplied tags in order. Successful
ordinary entry initializes each corresponding parameter slot to that value. -/
theorem factoryOperands_enter_read
    {values : List Value} {operands : List Core.Module.Functions.Operand}
    {layout : Core.Closure.Layout} {frame : Core.Closure.Frame layout}
    {globals : Core.Closure.Executor.GlobalLookup} {heap : Core.Closure.Heap}
    {fn : Function} {parameters : Core.Closure.Parameters fn.code.layout} {arguments : List Core.Closure.Value}
    {caller : Core.Closure.Call.Saved Core.Closure.Executor.Continuation}
    {stack : Core.Closure.Executor.Stack} {callee : Core.Closure.Call.Entered
      Core.Closure.Executor.Continuation fn.code.layout}
    (profile : factoryOperands values = some operands)
    (evaluated : Core.Closure.Executor.evalArgumentsIn globals heap frame (operands.map (·.lower)) = .ok arguments)
    (entered : Core.Closure.Call.enter fn parameters arguments heap caller stack = .ok callee) :
    arguments.map seededValue = values ∧
      ∀ {slot value}, (slot, value) ∈ parameters.slots.zip arguments →
        callee.environment.2.read callee.environment.1 slot.slot = .ok value :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.factoryOperands_enter_read profile evaluated entered

theorem acceptsFactory_escaped {context : CallContext} {closure : Function} {arity : Nat}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    (recorded : closure ∈ context.escaped)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (slots : definition.parameters.slots.length = arity)
    (shape : factoryCode context.table closure.code 2 = true) :
    context.acceptsFactory closure arity = true := by
  have known : closure ∈ context.published ++ context.escaped := List.mem_append_right _ recorded
  simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, known, resolved, slots, shape]

theorem acceptsFactory_returnClosure {context : CallContext} {closure : Function} {arity : Nat}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    {ref : Core.Closure.CodeRef} {captures : Fin ref.layout.captures → Core.Closure.CaptureSlot closure.code.layout}
    (recorded : closure ∈ context.published ++ context.escaped)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (slots : definition.parameters.slots.length = arity)
    (body : definition.body = .ret (.closure ref captures)) :
    context.acceptsFactory closure arity = true := by
  simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, recorded, resolved, slots,
    factoryCode, body, returnsClosure]

theorem acceptsFactory_returnClosureCall {context : CallContext} {closure : Function} {arity : Nat}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    {ref : Core.Closure.CodeRef} {captures : Fin ref.layout.captures → Core.Closure.CaptureSlot closure.code.layout}
    {arguments : List (Core.Closure.Executor.Operand closure.code.layout)}
    (recorded : closure ∈ context.published ++ context.escaped)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (slots : definition.parameters.slots.length = arity)
    (body : definition.body = .returnCall (.closure ref captures) arguments)
    (bounded : arguments.length ≤ 1) (child : factoryCode context.table ref 1 = true) :
    context.acceptsFactory closure arity = true := by
  simpa [CallContext.acceptsFactory, CallContext.acceptsCallFrom, recorded, resolved, slots,
    factoryCode, body, returnsClosure, bounded] using child

theorem run_factory_unrecorded {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (unpublished : closure ∉ context.published) (unescaped : closure ∉ context.escaped) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_factory_unrecorded resolved unpublished unescaped

theorem run_factory {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments operands : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (profile : factoryOperands values = some operands)
    (admitted : context.acceptsFactory closure operands.length = true) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      match ordinaryCall space context closure operands with
      | .finished heap (.ok (.function result)) =>
        let tail := runInstructionsIn (space.bindGlobal target (.function result))
          { context with heap, escaped := result :: context.escaped } rest
        { tail with calls := ⟨name, ⟨.ok (.function result), none⟩⟩ :: tail.calls }
      | .finished heap (.ok _) =>
        ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], heap⟩
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_factory resolved profile admitted

theorem run_adjacentKeywordDiscard {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {value : Int} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure 1 = true) :
    runInstructionsIn space context (.adjacentKeywordDiscard name value :: rest) =
      let invocation := (callbackSession space context.heap).prepareCall .discard
        (.literal (.function closure)) [.literal (.int value)]
      match (invocation.runPrefix context.table context.fuel).2.state with
      | .finished heap (.ok result) =>
        let tail := runInstructionsIn space { context with heap } rest
        { tail with calls := ⟨name, ⟨.ok (seededValue result), none⟩⟩ :: tail.calls }
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_adjacentKeywordDiscard found admitted

theorem observeArgumentIn_published {space : Namespace} {context : CallContext}
    {name : String} {closure : Function}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure = true) :
    observeArgumentIn space context (.call name []) =
      let invocation := callbackInvocation space context.heap closure
      match observeDirectCall space (invocation.runPrefix context.table context.fuel).2.state with
      | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
      | (.error error, heap) => (.error error, [], heap) := by
  simp [observeArgumentIn, Core.Module.SeededCall.resolveCall, Core.Module.SeededCall.Operand.eval,
    Core.Module.SeededCall.Operand.evalList, Except.bind, Except.map, found, invokeFlatCall, admitted]
  rfl

theorem observeArgumentIn_escaped {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {value : Int} {arguments : List Core.Module.Functions.Operand}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, [.int value]))
    (admitted : context.acceptsEscapedArgument closure = true) :
    observeArgumentIn space context (.call name arguments) true =
      match observeDirectCall space (ordinaryCall space context closure [.literal (.int value)]) with
      | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
      | (.error error, heap) => (.error error, [], heap) := by
  simp only [observeArgumentIn, resolved, admitted, Bool.and_self, ite_true]
  cases observeDirectCall space (ordinaryCall space context closure [.literal (.int value)]); rfl

theorem observeArgumentIn_escapedZero {space : Namespace} {context : CallContext}
    {name : String} {closure : Function}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsEscapedArgument closure 0 = true) :
    observeArgumentIn space context (.call name []) true =
      match observeDirectCall space (ordinaryCall space context closure []) with
      | (.ok observed, heap) => (observed.result.mapError .ofCall, [⟨name, observed⟩], heap)
      | (.error error, heap) => (.error error, [], heap) := by
  simp [observeArgumentIn, Core.Module.SeededCall.resolveCall, Core.Module.SeededCall.Operand.eval,
    Core.Module.SeededCall.Operand.evalList, Except.bind, Except.map, found, admitted]
  cases observeDirectCall space (ordinaryCall space context closure []); rfl

theorem observeArgumentsIn_stop {space : Namespace} {context : CallContext} {allowEscaped : Bool}
    {argument : Argument} {rest : List Argument} {error : ModuleFailure} {calls : List CallEvent} {heap : Heap}
    (failed : observeArgumentIn space context argument allowEscaped = (.error error, calls, heap)) :
    observeArgumentsIn space context (argument :: rest) allowEscaped = (.error error, calls, heap) := by
  simp [observeArgumentsIn, failed]

theorem observeArgumentsIn_next {space : Namespace} {context : CallContext} {allowEscaped : Bool}
    {argument : Argument} {rest : List Argument} {value : Value} {calls : List CallEvent} {heap : Heap}
    (first : observeArgumentIn space context argument allowEscaped = (.ok value, calls, heap)) :
    observeArgumentsIn space context (argument :: rest) allowEscaped =
      let (values, later, residual) := observeArgumentsIn space { context with heap } rest allowEscaped
      (values.map (value :: ·), calls ++ later, residual) := by
  simp [observeArgumentsIn, first]

theorem observeNestedCallIn_missing {space : Namespace} {context : CallContext}
    {destination : Core.Module.Functions.Destination} {name : String} {arguments : List Argument}
    (missing : space.lookupGlobal name = none) :
    observeNestedCallIn space context destination name arguments =
      (⟨.error (.raised (.runtime (.nameError name))), []⟩, context.heap) := by
  simp [observeNestedCallIn, missing]

theorem observeNestedCallIn_failedArguments {space : Namespace} {context : CallContext}
    {destination : Core.Module.Functions.Destination} {name : String} {callee : Value}
    {arguments : List Argument} {error : ModuleFailure} {calls : List CallEvent} {heap : Heap}
    (found : space.lookupGlobal name = some callee)
    (failed : observeArgumentsIn space context arguments (allowsEscapedArgument destination callee) =
      (.error error, calls, heap)) :
    observeNestedCallIn space context destination name arguments = (⟨.error error, calls⟩, heap) := by
  simp [observeNestedCallIn, found, failed]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
