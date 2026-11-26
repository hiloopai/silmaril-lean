module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_scalar_trace {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (ModuleEntry.Action scope)) :
    ∃ reached completion,
      runPrefix table (actions.length + 1) (.ready session (actions.map .scalar)) =
        ([], .finished reached completion) ∧ reached.heap = session.heap ∧ reached.lists = session.lists :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.ordinary_scalar_trace table session actions

theorem seeded_scalar_carriers {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (actions : List (ModuleEntry.Action scope)) (lists : ListHeap) :
    let outcome := Seeded.runInstructionsIn space context (actions.map .scalar) lists
    outcome.heap = context.heap ∧ outcome.lists = lists ∧ outcome.calls = [] ∧
      outcome.residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_scalar_carriers space context actions lists

theorem seededSuite_carriers {scope : Source.Scope} (context : Seeded.CallContext)
    (incoming : Seeded.Observation) (actions : List (ModuleEntry.Action scope)) :
    let reached := (seededSuite context incoming actions).reached
    reached.heap = incoming.heap ∧ reached.lists = incoming.lists ∧ reached.calls = incoming.calls ∧
      reached.residual.builtins = incoming.residual.builtins := by
  have ⟨heap, lists, calls, builtins⟩ := seeded_scalar_carriers incoming.residual
    { context with heap := incoming.heap } actions incoming.lists
  exact ⟨heap, lists, by simp [seededSuite, calls], builtins⟩

open Functions.ExceptionalTry (Plan RaiseArguments RaiseCall RaiseName Step runSuite)

theorem runSuite_append {state failure action : Type}
    (step : state → action → Except failure state) (initial : state) (earlier later : List action) :
    runSuite step initial (earlier ++ later) =
      let first := runSuite step initial earlier
      match first.completion with
      | .ok () => runSuite step first.reached later
      | .error _ => first :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.runSuite_append step initial earlier later

theorem ordinary_reached_carriers {scope : Source.Scope} (session : Session)
    (plan : Plan (Step scope)) :
    let outcome := Compile.ModuleEntry.Functions.Run.runExceptionalTry session plan
    outcome.reached.heap = session.heap ∧ outcome.reached.lists = session.lists :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.ordinary_reached_carriers session plan

theorem ordinary_settlement {scope : Source.Scope} (table : CodeTable) (session : Session)
    (plan : Plan (Step scope)) (rest : List (Instruction scope)) :
    advance table (.ready session (.exceptionalTry plan :: rest)) =
      let outcome := Compile.ModuleEntry.Functions.Run.runExceptionalTry session plan
      ([], match outcome.completion with
        | .ok () => .ready outcome.reached rest
        | .error error => .finished outcome.reached error) := rfl

theorem seeded_reached_builtins {scope : Source.Scope} (space : Namespace) (plan : Plan (Step scope))
    (heap : Core.Closure.Heap := .empty) : (Seeded.runExceptionalTry space plan heap).reached.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_reached_builtins space plan heap

theorem seeded_settlement {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (plan : Plan (Step scope)) (rest : List (Instruction scope)) (lists : ListHeap) :
    Seeded.runInstructionsIn space context (.exceptionalTry plan :: rest) lists =
      let outcome := Seeded.runExceptionalTry space plan context.heap
      match outcome.completion with
      | .ok () => Seeded.runInstructionsIn outcome.reached context rest lists
      | .error error => ⟨outcome.reached, .error error, [], context.heap, lists⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_settlement space context plan rest lists

theorem stockException_descriptor_agrees :
    Seeded.ordinaryValue? (.exceptionClass .exception) = some .stockException ∧
      Seeded.seededValue .stockException = .exceptionClass .exception := ⟨rfl, rfl⟩

theorem ordinary_raise_stock {scope : Source.Scope} (session : Session) (call : RaiseCall scope)
    {message : Core.Text}
    (found : session.globals call.name = some .stockException)
    (read : call.evalArguments session.globals raiseText? = .ok (.one (some message))) :
    exceptionalStep session (.raiseCall call) = .error (.raised (.explicitException message)) := by
  simp [exceptionalStep, call.error_construct _ _ _ found read, raiseValue, Functions.ExceptionalTry.RaiseValue.construct]

theorem seeded_raise_stock {scope : Source.Scope} (space : Namespace) (call : RaiseCall scope)
    {message : Core.Text}
    (found : space.lookupGlobal call.name = some (.exceptionClass .exception))
    (read : call.evalArguments space.lookupGlobal Seeded.raiseText? = .ok (.one (some message))) :
    Seeded.exceptionalStep .empty space (.raiseCall call) = .error (.raised (.runtime (.explicitException message))) := by
  simp [Seeded.exceptionalStep, call.error_construct _ _ _ found read, Seeded.raiseValue,
    Functions.ExceptionalTry.RaiseValue.construct]

theorem seeded_raise_builtin {scope : Source.Scope} (space : Namespace) (call : RaiseCall scope)
    {message : Core.Text}
    (absent : Core.Module.SeededCall.lookupBinding space.moduleGlobals call.name = none)
    (stock : Core.Module.SeededCall.lookupBinding space.builtins call.name = some (.exceptionClass .exception))
    (read : call.evalArguments space.lookupGlobal Seeded.raiseText? = .ok (.one (some message))) :
    Seeded.exceptionalStep .empty space (.raiseCall call) = .error (.raised (.runtime (.explicitException message))) :=
  seeded_raise_stock space call ((Namespace.builtin_fallback space absent).trans stock) read

theorem seeded_raise_masked {scope : Source.Scope} (space : Namespace) (call : RaiseCall scope)
    {arguments : RaiseArguments}
    (mask : Core.Module.SeededCall.lookupBinding space.moduleGlobals call.name = some .none)
    (read : call.evalArguments space.lookupGlobal Seeded.raiseText? = .ok arguments) :
    Seeded.exceptionalStep .empty space (.raiseCall call) = .error (.raised (.runtime .notCallable)) := by
  simp [Seeded.exceptionalStep, call.error_construct _ _ _ (Namespace.module_precedes space mask) read,
    Seeded.raiseValue, Functions.ExceptionalTry.RaiseValue.construct]

theorem ordinary_raise_class {scope : Source.Scope} (session : Session) (operand : RaiseName scope)
    {kind : Core.Closure.ExceptionClass} (found : session.globals operand.name = some (.exceptionClass kind)) :
    exceptionalStep session (.raiseName operand) = .error (.raised (.raisedInstance (.empty kind))) := by
  simp [exceptionalStep, operand.error_found _ _ found, raiseValue, Functions.ExceptionalTry.RaiseValue.normalize]

theorem seeded_raise_class {scope : Source.Scope} (space : Namespace) (operand : RaiseName scope)
    {kind : Core.Closure.ExceptionClass}
    (found : space.lookupGlobal operand.name = some (.exceptionClass kind)) :
    Seeded.exceptionalStep .empty space (.raiseName operand) = .error (.raised (.runtime (.raisedInstance (.empty kind)))) := by
  simp [Seeded.exceptionalStep, operand.error_found _ _ found, Seeded.raiseValue,
    Functions.ExceptionalTry.RaiseValue.normalize]

theorem exceptionInstance_transport (value : Core.Closure.ExceptionInstance) :
    Seeded.ordinaryValue? (.exceptionInstance value) = some (.exceptionInstance value) ∧
      Seeded.seededValue (.exceptionInstance value) = .exceptionInstance value := ⟨rfl, rfl⟩

theorem ordinary_module_raise {scope : Source.Scope} (table : CodeTable) (session : Session)
    (operand : RaiseName scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.exceptionalTry operand.plan :: rest)) =
      ([], .finished session (.raised (operand.error session.globals raiseValue))) := rfl

theorem seeded_module_raise {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (operand : RaiseName scope) (rest : List (Instruction scope)) (lists : ListHeap) :
    Seeded.runInstructionsIn space context (.exceptionalTry operand.plan :: rest) lists =
      ⟨space, .error (.raised (.runtime (operand.error space.lookupGlobal Seeded.raiseValue))),
        [], context.heap, lists⟩ := seeded_settlement space context operand.plan rest lists

theorem ordinary_handler_stock (session : Session) (name : String) (error : Core.Closure.RuntimeError)
    (kind : Core.Closure.ExceptionClass) (found : session.globals name = some (.exceptionClass kind)) :
    matchHandler session (.raised error) name = .ok (decide (kind.catches error.classify)) := by
  simp [matchHandler, Functions.ExceptionalTry.matchClass, found, handlerClass, Except.mapError]

theorem seeded_handler_stock (space : Namespace) (name : String) (error : Core.Module.SeededCall.Raised)
    (kind : Core.Closure.ExceptionClass)
    (found : space.lookupGlobal name = some (.exceptionClass kind)) :
    Seeded.matchHandler space (.raised error) name = .ok (decide (kind.catches error.classify)) := by
  simp [Seeded.matchHandler, Functions.ExceptionalTry.matchClass, found, Seeded.handlerClass, Except.mapError]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry
