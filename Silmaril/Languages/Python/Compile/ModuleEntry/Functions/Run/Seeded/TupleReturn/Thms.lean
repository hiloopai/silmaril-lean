module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.TupleReturn.Settlement

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded


/-- A settled tuple binds the exact payload and emits one receipt with the reached heap. -/
theorem run_tuple_result {scope : Source.Scope} {space : Core.Module.SeededCall.Namespace} {context : CallContext}
    {name target : String} {closure : Core.Closure.Function}
    {arguments operands : List Core.Module.Functions.Operand}
    {values : List Core.Module.SeededCall.Value} {rest : List (Run.Instruction scope)} {lists : Core.Module.ListHeap}
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
        ⟨space, .error .directCallFuelExhausted, [], heap, lists⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.TupleReturn.run_result
    fixed resolved profile notFactory admitted

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
