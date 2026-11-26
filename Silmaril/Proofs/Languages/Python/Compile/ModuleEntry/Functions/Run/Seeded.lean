module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms
import Silmaril.Languages.Python.Core.Closure.Call.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Silmaril.Languages.Python.Core.Module.SeededCall (Failure Namespace Value)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run (Argument Instruction)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Core.Closure (Function)

theorem observeArguments_iff {space : Namespace} {arguments : List Argument}
    {values : Except Failure (List Value)} {calls : List CallEvent} :
    observeArguments space arguments = (values, calls) ↔ EvaluatesArguments space arguments values calls := by
  constructor
  · induction arguments generalizing values calls with
    | nil =>
      intro observed
      cases observed
      exact .nil
    | cons argument rest ih =>
      intro observed
      cases first : observeArgument space argument with
      | mk result firstCalls =>
        cases result with
        | error error =>
          rw [observeArguments, first] at observed
          cases observed
          exact .stop first
        | ok value =>
          cases tail : observeArguments space rest with
          | mk tailValues tailCalls =>
            rw [observeArguments, first, tail] at observed
            cases observed
            exact .next first (ih tail)
  · intro evaluated
    induction evaluated with
    | nil => rfl
    | stop failed => simp [observeArguments, failed]
    | next first _ ih => simp [observeArguments, first, ih]

theorem preserves_builtins {scope : Languages.Python.Source.Scope} (space : Namespace)
    (instructions : List (Instruction scope)) (context : CallContext) :
    (runInstructionsIn space context instructions).residual.builtins = space.builtins := by
  induction instructions generalizing space context with
  | nil => rfl
  | cons instruction rest ih =>
    cases selected : (effect space context instruction).1.binding with
    | error error => simp [runInstructionsIn, selected]
    | ok binding =>
      cases binding with
      | none => simp [runInstructionsIn, selected, ih]
      | some assignment =>
        obtain ⟨name, value⟩ := assignment
        simp [runInstructionsIn, selected, ih, Namespace.bind_preserves_builtins]


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
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ := by
  simp [runInstructionsIn, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, invokeFlatCall, admitted]
  generalize (callbackInvocation space context.heap closure |>.runPrefix context.table context.fuel).2.state =
    state
  cases state with
  | finished heap result => cases result <;> rfl
  | _ => rfl

theorem run_directDiscard_unsupported {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (rejected : context.acceptsPublishedCall closure = false) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap⟩ := by
  simp [runInstructionsIn, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, Except.mapError, invokeFlatCall, rejected, acceptObservation, ModuleFailure.ofCall]

private theorem factoryOperand_iff {value : Value} {operand : Core.Module.Functions.Operand} :
    factoryOperand value = some operand ↔
      ∃ literal : Core.Closure.Value, (literal = .none ∨ ∃ n, literal = .int n) ∧
        value = seededValue literal ∧ operand = .literal literal := by
  constructor
  · intro accepted
    cases value with
    | none => exact ⟨.none, .inl rfl, rfl, (Option.some.inj accepted).symm⟩
    | int n => exact ⟨.int n, .inr ⟨n, rfl⟩, rfl, (Option.some.inj accepted).symm⟩
    | _ => simp [factoryOperand] at accepted
  · rintro ⟨_, rfl | ⟨_, rfl⟩, rfl, rfl⟩ <;> rfl

private theorem factoryMap_iff {values : List Value} {operands : List Core.Module.Functions.Operand} :
    values.mapM factoryOperand = some operands ↔
      ∃ literals : List Core.Closure.Value, (∀ literal ∈ literals, literal = .none ∨ ∃ n, literal = .int n) ∧
        values = literals.map seededValue ∧ operands = literals.map .literal := by
  induction values generalizing operands with
  | nil =>
    constructor
    · intro equal
      exact ⟨[], by simp, rfl, (Option.some.inj equal).symm⟩
    · rintro ⟨literals, _, empty, rfl⟩
      cases literals <;> simp_all
  | cons value values ih =>
    constructor
    · intro equal
      cases head : factoryOperand value with
      | none => simp [List.mapM_cons, head] at equal
      | some operand =>
        cases tail : values.mapM factoryOperand with
        | none => simp [List.mapM_cons, head, tail] at equal
        | some rest =>
          obtain ⟨literal, valid, rfl, rfl⟩ := factoryOperand_iff.mp head
          obtain ⟨literals, supported, input, output⟩ := ih.mp tail
          exact ⟨literal :: literals, by simpa using ⟨valid, supported⟩, by simp [input], by
            simpa [List.mapM_cons, head, tail, output] using equal.symm⟩
    · rintro ⟨literals, supported, source, rfl⟩
      cases literals with
      | nil => simp at source
      | cons literal literals =>
        simp only [List.mem_cons, forall_eq_or_imp] at supported
        simp only [List.map_cons, List.cons.injEq] at source
        obtain ⟨rfl, remaining⟩ := source
        have head := factoryOperand_iff.mpr ⟨literal, supported.1, rfl, rfl⟩
        have tail := ih.mpr ⟨literals, supported.2, remaining, rfl⟩
        simp [List.mapM_cons, head, tail]

theorem factoryOperands_iff {values : List Value} {operands : List Core.Module.Functions.Operand} :
    factoryOperands values = some operands ↔
      ∃ literals : List Core.Closure.Value, literals.length ≤ 3 ∧
        (∀ literal ∈ literals, literal = .none ∨ ∃ n, literal = .int n) ∧
        values = literals.map seededValue ∧ operands = literals.map .literal := by
  by_cases length : values.length ≤ 3
  · simp only [factoryOperands, length, ite_true, factoryMap_iff]
    constructor
    · rintro ⟨literals, supported, source, target⟩
      exact ⟨literals, by simpa [source] using length, supported, source, target⟩
    · rintro ⟨literals, _, supported, source, target⟩
      exact ⟨literals, supported, source, target⟩
  · simp only [factoryOperands, length, ite_false, reduceCtorEq, false_iff]
    rintro ⟨literals, size, _, source, _⟩
    exact length (by simpa [source] using size)

private theorem evalFactoryLiterals {layout : Core.Closure.Layout} (frame : Core.Closure.Frame layout)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap)
    (literals : List Core.Closure.Value) :
    Core.Closure.Executor.evalArgumentsIn globals heap frame
      ((literals.map Core.Module.Functions.Operand.literal).map (·.lower)) = .ok literals := by
  induction literals with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, List.map_cons, Core.Closure.Executor.evalArgumentsIn, ih]
    rfl

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
        callee.environment.2.read callee.environment.1 slot.slot = .ok value := by
  obtain ⟨literals, _, _, rfl, rfl⟩ := factoryOperands_iff.mp profile
  rw [evalFactoryLiterals frame globals heap literals] at evaluated
  have equal := Except.ok.inj evaluated
  subst arguments
  exact ⟨rfl, fun member => Core.Closure.Call.enter_read entered member⟩

theorem run_factory_unrecorded {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (unpublished : closure ∉ context.published) (unescaped : closure ∉ context.escaped) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap⟩ := by
  have denied (arity : Nat) : context.acceptsFactory closure arity = false := by
    simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, unpublished, unescaped]
  cases operands : factoryOperands values <;>
    simp [runInstructionsIn, effect, resolved, invokeFlatCall, operands, denied,
      acceptObservation, ModuleFailure.ofCall, Except.bind, Except.mapError]

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
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ := by
  simp only [runInstructionsIn, effect, resolved, invokeFlatCall, profile, admitted, ite_true]
  generalize ordinaryCall space context closure operands = state
  cases state with
  | finished heap result =>
    cases result with
    | ok value => cases value <;> rfl
    | error error => rfl
  | _ => rfl

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
  by
    simp [runInstructionsIn, effect, invokeAdjacentKeywordDiscard, found, admitted]
    generalize (((callbackSession space context.heap).prepareCall .discard
      (.literal (.function closure)) [.literal (.int value)]).runPrefix context.table context.fuel).2.state =
      state
    cases state with
    | finished heap result => cases result <;> rfl
    | _ => rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
