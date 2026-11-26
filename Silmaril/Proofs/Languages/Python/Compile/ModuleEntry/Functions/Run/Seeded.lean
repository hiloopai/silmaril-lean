module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

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
    (instructions : List (Instruction scope)) (context : CallContext) (lists : Core.Module.ListHeap)
    (defaultedNames : List String := []) :
    (runInstructionsIn space context instructions lists defaultedNames).residual.builtins = space.builtins := by
  induction instructions generalizing space context lists defaultedNames with
  | nil => rfl
  | cons instruction rest ih =>
    cases selected : (effectWithLists space context instruction lists defaultedNames).1.1.binding with
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
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, Core.Module.ListHeap.empty⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ := by
  simp [runInstructionsIn, effectWithLists, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, invokeNamedFlatCall, invokeFlatCall, admitted]
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
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap, Core.Module.ListHeap.empty⟩ := by
  simp [runInstructionsIn, effectWithLists, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, Except.mapError, invokeNamedFlatCall, invokeFlatCall, rejected, acceptObservation, ModuleFailure.ofCall]

theorem factoryOperands_iff {values : List Value} {operands : List Core.Module.Functions.Operand} :
    factoryOperands values = some operands ↔
      ∃ integers : List Int, integers.length ≤ 3 ∧ values = integers.map .int ∧
        operands = integers.map (fun value => .literal (.int value)) := by
  have mapped (values : List Value) (operands : List Core.Module.Functions.Operand) :
      values.mapM factoryOperand = some operands ↔
        ∃ integers : List Int, values = integers.map .int ∧
          operands = integers.map (fun value => .literal (.int value)) := by
    induction values generalizing operands with
    | nil =>
      constructor
      · intro equal
        exact ⟨[], rfl, by simpa using equal.symm⟩
      · rintro ⟨integers, empty, rfl⟩
        cases integers <;> simp_all
    | cons value values ih =>
      constructor
      · intro equal
        cases value with
        | int value =>
          cases tail : values.mapM factoryOperand with
          | none => simp [factoryOperand, tail] at equal
          | some tailOperands =>
            obtain ⟨integers, source, target⟩ := (ih tailOperands).mp tail
            exact ⟨value :: integers, by simp [source], by
              simpa [factoryOperand, tail, target] using equal.symm⟩
        | _ => simp [factoryOperand] at equal
      · rintro ⟨integers, source, rfl⟩
        cases integers with
        | nil => simp at source
        | cons first rest =>
          simp only [List.map_cons, List.cons.injEq] at source
          obtain ⟨rfl, remaining⟩ := source
          have tail := (ih _).mpr ⟨rest, remaining, rfl⟩
          simp [factoryOperand, tail]
  constructor
  · intro accepted
    by_cases length : values.length ≤ 3
    · simp only [factoryOperands, length, ite_true, mapped] at accepted
      obtain ⟨integers, source, target⟩ := accepted
      exact ⟨integers, by simpa [source] using length, source, target⟩
    · simp [factoryOperands, length] at accepted
  · rintro ⟨integers, length, rfl, rfl⟩
    have size : (integers.map Value.int).length ≤ 3 := by simpa using length
    simp only [factoryOperands, size, ite_true, mapped]
    exact ⟨integers, rfl, rfl⟩

theorem run_factory_unrecorded {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Function} {arguments : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)}
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (unpublished : closure ∉ context.published) (unescaped : closure ∉ context.escaped) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap, Core.Module.ListHeap.empty⟩ := by
  have denied (arity : Nat) : context.acceptsFactory closure arity = false := by
    simp [CallContext.acceptsFactory, CallContext.acceptsCallFrom, unpublished, unescaped]
  cases operands : factoryOperands values <;>
    simp [runInstructionsIn, effectWithLists, effect, resolved, invokeNamedFlatCall, invokeFlatCall, operands, denied,
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
        ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, Core.Module.ListHeap.empty⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ := by
  simp only [runInstructionsIn, effectWithLists, effect, resolved, invokeNamedFlatCall, List.contains_nil, Bool.false_eq_true, ite_false, invokeFlatCall, profile, admitted, ite_true]
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
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, Core.Module.ListHeap.empty⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, Core.Module.ListHeap.empty⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, Core.Module.ListHeap.empty⟩ :=
  by
    simp [runInstructionsIn, effectWithLists, effect, invokeAdjacentKeywordDiscard, found, admitted]
    generalize (((callbackSession space context.heap).prepareCall .discard
      (.literal (.function closure)) [.literal (.int value)]).runPrefix context.table context.fuel).2.state =
      state
    cases state with
    | finished heap result => cases result <;> rfl
    | _ => rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
