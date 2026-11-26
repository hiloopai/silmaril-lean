module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.TupleReturn

open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run (Instruction)
open Compile.ModuleEntry.Functions.Run.Seeded
open Core.Module.SeededCall (Namespace Value)

theorem run_result {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name target : String} {closure : Core.Closure.Function}
    {arguments operands : List Core.Module.Functions.Operand}
    {values : List Value} {rest : List (Instruction scope)} {lists : Core.Module.ListHeap}
    (fixed : context.isVariadic (.function closure) = false)
    (resolved : Core.Module.SeededCall.resolveCall space #v[] (.global name)
      (arguments.map lowerCallOperand) = .ok (.function closure, values))
    (profile : factoryOperands values = some operands)
    (notFactory : context.acceptsFactory closure operands.length = false)
    (admitted : context.acceptsTupleResult closure operands.length = true) :
    runInstructionsIn space context (.call (.bindGlobal target) name arguments :: rest) lists =
      match ordinaryCall space context closure operands with
      | .finished heap (.ok (.tuple items)) =>
        let tail := runInstructionsIn (space.bindGlobal target (.returnedTuple items)) { context with heap } rest lists
        { tail with calls := ⟨name, ⟨.ok (.returnedTuple items), none⟩⟩ :: tail.calls }
      | .finished heap (.ok _) =>
        ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], heap, lists⟩
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap, lists⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap, lists⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap, lists⟩ := by
  simp only [runInstructionsIn, effectWithLists, effect, resolved, invokeModuleCall, fixed, Bool.false_eq_true, ite_false, invokeFlatCall, profile, notFactory,
    admitted, Bool.false_eq_true, ite_false, ite_true]
  generalize ordinaryCall space context closure operands = state
  cases state with
  | finished heap result =>
    cases result with
    | ok value => cases value <;> rfl
    | error error => rfl
  | _ => rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.TupleReturn
