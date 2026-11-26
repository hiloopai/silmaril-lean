module

import Batteries.Data.Except
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry.Thms
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Thms
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
meta import Silmaril.Languages.Python.Core.Module.Functions.Defs
meta import Silmaril.Languages.Python.Core.Module.SeededCall.Defs
meta import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Namespace Result)

private def lengthSource (right : Source.Expr) : Source.Module :=
  ⟨[.assign "before" (.integer 7),
    .assert_ (.comparison (.callWith (.name "len")
      [(.positional, .list_ [.integer 4, .boolean false])]) [(.eq, right)]) none,
    .assign "after" (.integer 9)]⟩

private def lengthRun (space : Namespace) (right : Source.Expr)
    (completion : Except ModuleFailure Unit) (receipt : Result) : Bool :=
  match Run.compile (lengthSource right) with
  | .error _ => false
  | .ok compiled =>
    let heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
    let result := run space compiled heap
    let before := space.bindGlobal "before" (.int 7)
    let expected := if completion.isOk then before.bindGlobal "after" (.int 9) else before
    result.completion == completion && result.residual.moduleGlobals == expected.moduleGlobals &&
      result.residual.builtins == space.builtins && result.heap.next == 1 &&
      (result.heap.contents 0).map seededValue == some (.int 23) &&
      (result.calls.map (fun call => (call.callee, call.observation.result))) == [("len", receipt)] &&
      result.calls.all (fun call => call.observation.caught.isNone)

private def stock : Namespace := legacyBoolCallableSeed .builtin

#guard lengthRun stock (.integer 2) (.ok ()) (.ok (.int 2))

#guard lengthRun (stock.bindGlobal "len" .none) (.name "missing_right")
  (.error (.raised (.runtime .notCallable))) (.error (.raised (.runtime .notCallable)))

#guard lengthRun stock (.name "missing_right")
  (.error (.raised (.runtime (.nameError "missing_right")))) (.ok (.int 2))

#guard lengthRun .empty (.name "missing_right")
  (.error (.raised (.runtime (.nameError "len")))) (.error (.raised (.runtime (.nameError "len"))))

private def moduleTextEvidence (placement : SeedPlacement) : Bool := Id.run do
  let source : Source.Module := ⟨[
    .assign "text" (.text [233, 128512, 55296]),
    .assign "saved" (.name "text"),
    .assign "text" (.text [122]),
    .expression (.call (.name "___assertEqual") [.name "saved", .text [233, 128512, 55296]]),
    .assign "saved" (.name "missing")]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacySeed placement
  let result := run space compiled
  return result.completion == .error (.raised (.runtime (.nameError "missing"))) &&
    result.residual.moduleGlobals ==
      [("text", .text ⟨[122], by decide⟩), ("saved", .text ⟨[233, 128512, 55296], by decide⟩)] ++ space.moduleGlobals &&
    result.residual.builtins == space.builtins &&
    result.heap.next == 0 && result.lists.objects.isEmpty &&
    result.calls.map (fun call => (call.callee, call.observation.result, call.observation.caught)) ==
      [("___assertEqual", .ok .none, none)]

#guard moduleTextEvidence .builtin
#guard moduleTextEvidence .preamble

private def textSliceEvidence (placement : SeedPlacement) (zero : Bool) : Bool := Id.run do
  let points := [65, 233, 128512, 769, 55296]
  let step := if zero then Source.Expr.integer 0 else .unary .negative (.integer 2)
  let left := Source.Expr.slice (.name "a") (some (.integer 100)) none (some step)
  let right := if zero then Source.Expr.name "missing" else .text [55296, 128512, 65]
  let guard := Source.Expr.unary .not_ (.comparison left [(.eq, right)])
  let raiseArm := Source.Stmt.raise_ (some (.call (.name "Exception") [.text []])) none
  let source : Source.Module := ⟨[.assign "a" (.text points), .if_ guard [raiseArm] [], .assign "tail" (.name "a")]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacySeed placement
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := run space compiled (lists := lists)
  let text := Core.Text.mk [65, 233, 128512, 769, 55296] (by decide)
  let bound := space.bindGlobal "a" (.text text)
  let reached := if zero then bound else bound.bindGlobal "tail" (.text text)
  let completion := if zero then .error (.raised (.runtime .zeroSliceStep)) else .ok ()
  return result.completion == completion && result.residual.moduleGlobals == reached.moduleGlobals &&
    result.residual.builtins == space.builtins && result.heap.next == 0 && result.lists == lists &&
    result.calls.isEmpty

#guard textSliceEvidence .builtin false
#guard textSliceEvidence .preamble true
#guard (Core.Module.SeededCall.Raised.runtime .zeroSliceStep).classify == .valueError

private def textSliceOperandEvidence (placement : SeedPlacement) (zero : Bool) : Bool := Id.run do
  let points := [65, 233, 128512, 769, 55296]
  let step := if zero then Source.Expr.integer 0 else .unary .negative (.integer 2)
  let first := Source.Expr.slice (.text points) none none (some step)
  let second := if zero then Source.Expr.name "missing" else .text [55296, 128512, 65]
  let call := Source.Stmt.expression (.call (.name "___assertEqual") [first, second])
  let source : Source.Module := ⟨[call]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacySeed placement
  let result := run space compiled
  let completion := if zero then .error (.raised (.runtime .zeroSliceStep)) else .ok ()
  let receipts := if zero then [] else [("___assertEqual", .ok .none, none)]
  return result.completion == completion && result.residual.moduleGlobals == space.moduleGlobals &&
    result.residual.builtins == space.builtins && result.heap.next == 0 && result.lists.objects.isEmpty &&
    result.calls.map (fun call => (call.callee, call.observation.result, call.observation.caught)) == receipts

#guard textSliceOperandEvidence .builtin false
#guard textSliceOperandEvidence .preamble true

private def normalTryEvidence : Bool := Id.run do
  let source : Source.Module := ⟨[.assign "flag" (.boolean false),
    .try_ [.assign "flag" (.boolean true), .pass]
      [⟨none, none, [.assign "unreachedHandler" (.integer 9)]⟩]
      [.assign "phase" (.integer 2)]
      [.assign "copied" (.name "phase"), .assign "stopped" (.name "missing")],
    .assign "unreachedTail" (.integer 11)]⟩
  let .ok compiled := Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun x => if x = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := run .empty compiled heap (lists := lists)
  let start := { Run.seed .empty heap with lists }
  let (events, state) := Run.runPrefix compiled.table 1000 (.ready start compiled.instructions)
  let .finished residual completion := state | return false
  return result.completion == .error (.raised (.runtime (.nameError "missing"))) &&
    result.residual.moduleGlobals == [("copied", .int 2), ("phase", .int 2), ("flag", .bool true)] &&
    result.residual.builtins.isEmpty && result.calls.isEmpty &&
    result.lists == lists && result.heap.next == heap.next && (result.heap.contents 0).map seededValue == some (.int 23) &&
    events.isEmpty && completion == .raised (.nameError "missing") && residual.lists == lists &&
    residual.heap.next == heap.next && (residual.heap.contents 0).map seededValue == some (.int 23) &&
    (residual.globals "flag").map seededValue == some (.bool true) &&
    (residual.globals "copied").map seededValue == some (.int 2) &&
    (residual.globals "unreachedHandler").isNone && (residual.globals "unreachedTail").isNone

#guard normalTryEvidence

private def exceptionalCleanupEvidence : Bool := Id.run do
  let statement := Source.Stmt.try_
    [.assign "body" (.integer 7), .assign "afterFailure" (.name "bodyMissing")]
    [] [] [.assign "copied" (.name "body")]
  let .ok compiled := Run.compile ⟨[statement, .assign "tail" (.integer 9)]⟩ | return false
  let heap : Core.Closure.Heap := ⟨1, fun slot => if slot = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let (events, state) := Run.runPrefix compiled.table 10
    (.ready { Run.seed .empty heap with lists } compiled.instructions)
  let .finished ordinary completion := state | return false
  let seeded := run .empty compiled heap (lists := lists)
  return events.isEmpty && completion == .raised (.nameError "bodyMissing") &&
    (ordinary.globals "copied").map seededValue == some (.int 7) &&
    (ordinary.globals "afterFailure").isNone && (ordinary.globals "tail").isNone &&
    ordinary.lists == lists && ordinary.heap.next == heap.next &&
    (ordinary.heap.contents 0).map seededValue == some (.int 23) &&
    seeded.completion == .error (.raised (.runtime (.nameError "bodyMissing"))) &&
    seeded.residual.moduleGlobals == [("copied", .int 7), ("body", .int 7)] &&
    seeded.residual.builtins.isEmpty && seeded.calls.isEmpty && seeded.lists == lists &&
    seeded.heap.next == heap.next && (seeded.heap.contents 0).map seededValue == some (.int 23)

#guard exceptionalCleanupEvidence

private def exceptionalProfileFailureEvidence : Bool := Id.run do
  let .ok tree := Source.analyze ⟨[.pass]⟩ | return false
  let outsideProfile := ModuleEntry.Action.assertion (scope := tree.scope) (.binary .add (.integer 1) .none_)
  let failIfReached := ModuleEntry.Action.assertion (scope := tree.scope) .none_
  let plan : Functions.ExceptionalTry.Plan (Functions.ExceptionalTry.Step tree.scope) :=
    ⟨[.scalar outsideProfile], [.bare [.scalar failIfReached]], [], [.scalar failIfReached]⟩
  let ordinary := Run.runPrefix (fun _ => none) 2
    (.ready (Run.seed .empty) [.exceptionalTry plan, .scalar failIfReached])
  let .finished _ .scalarProfile := ordinary.2 | return false
  let seeded := runInstructions .empty [.exceptionalTry plan, .scalar failIfReached]
  return ordinary.1.isEmpty && seeded.completion == .error .unsupported && seeded.calls.isEmpty &&
    seeded.residual.moduleGlobals.isEmpty

#guard exceptionalProfileFailureEvidence

private def stockRaiseEvidence : Bool := Id.run do
  let points := [233, 128512, 55296]
  let message : Core.Text := ⟨points, by decide⟩
  let statement := Source.Stmt.try_
    [.assign "kept" (.integer 7),
     .raise_ (some (.callWith (.name "saved") [(.positional, .text points)])) none]
    [] [] [.assign "cleanup" (.name "kept")]
  let source : Source.Module := ⟨[
    .assign "saved" (.name "Exception"), .assign "Exception" .none_, statement, .assign "tail" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let initial := (Run.seed .empty).bindGlobal "Exception" .stockException
  let (events, state) := Run.runPrefix compiled.table 10 (.ready initial compiled.instructions)
  let .finished ordinary completion := state | return false
  let space : Namespace := ⟨[], [("Exception", .exceptionClass .exception)]⟩
  let seeded := run space compiled
  return completion == .raised (.explicitException message) && events.isEmpty &&
    (ordinary.globals "saved").map seededValue == some (.exceptionClass .exception) &&
    (ordinary.globals "Exception").map seededValue == some .none &&
    (ordinary.globals "cleanup").map seededValue == some (.int 7) &&
    (ordinary.globals "tail").isNone &&
    seeded.completion == .error (.raised (.runtime (.explicitException message))) &&
    seeded.residual.builtins == space.builtins && seeded.calls.isEmpty &&
    seeded.residual.moduleGlobals == [("cleanup", .int 7), ("kept", .int 7),
      ("Exception", .none), ("saved", .exceptionClass .exception)]

#guard stockRaiseEvidence

private def typedHandlerEvidence : Bool := Id.run do
  let equal name number := Source.Stmt.assert_ (.comparison (.name name) [(.eq, .integer number)]) none
  let statement := Source.Stmt.try_ [.raise_ none none, .assert_ (.boolean false) none]
    [⟨some (.name "RuntimeError"), none, [.assign "x" (.integer 6)]⟩]
    [] [.assign "y" (.integer 7), equal "x" 6]
  let source : Source.Module := ⟨[statement, equal "y" 7]⟩
  let .ok compiled := Run.compile source | return false
  let seed := Run.seed .empty
  let (events, missingState) := Run.runPrefix compiled.table 10 (.ready seed compiled.instructions)
  let .finished missing (.raised (.nameError "x")) := missingState | return false
  let available := seed.bindGlobal "RuntimeError" (.exceptionClass .runtimeError)
  let (_, stockState) := Run.runPrefix compiled.table 10 (.ready available compiled.instructions)
  let .finished caught .normal := stockState | return false
  let space : Namespace := ⟨[], [("RuntimeError", .exceptionClass .runtimeError)]⟩
  let seeded := run space compiled
  let unseeded := run .empty compiled
  return events.isEmpty && (missing.globals "y").map seededValue == some (.int 7) &&
    (caught.globals "x").map seededValue == some (.int 6) &&
    unseeded.completion == .error (.raised (.runtime (.nameError "x"))) &&
    unseeded.residual.moduleGlobals == [("y", .int 7)] && unseeded.calls.isEmpty &&
    seeded.completion.isOk && seeded.residual.moduleGlobals == [("y", .int 7), ("x", .int 6)] &&
    seeded.residual.builtins == space.builtins && seeded.calls.isEmpty

#guard typedHandlerEvidence

private def namedRaiseEvidence (explicit : Bool) : Bool := Id.run do
  let operand := if explicit then Source.Expr.callWith (.name "saved") [] else .name "saved"
  let statement := Source.Stmt.try_ [.assign "before" (.integer 7), .raise_ (some operand) none]
    [] [] [.assign "after" (.name "before")]
  let source : Source.Module := ⟨[
    .assign "saved" (.name "TypeError"), .assign "TypeError" .none_, statement]⟩
  let .ok compiled := Run.compile source | return false
  let initial := (Run.seed .empty).bindGlobal "TypeError" (.exceptionClass .typeError)
  let (events, state) := Run.runPrefix compiled.table 10 (.ready initial compiled.instructions)
  let .finished ordinary completion := state | return false
  let space : Namespace := ⟨[], [("TypeError", .exceptionClass .typeError)]⟩
  let seeded := run space compiled
  let raised : Core.Closure.RuntimeError := .raisedInstance (.empty .typeError)
  return completion == .raised raised && events.isEmpty &&
    (ordinary.globals "saved").map seededValue == some (.exceptionClass .typeError) &&
    (ordinary.globals "after").map seededValue == some (.int 7) &&
    seeded.completion == .error (.raised (.runtime raised)) &&
    seeded.residual.moduleGlobals == [("after", .int 7), ("before", .int 7), ("TypeError", .none),
      ("saved", .exceptionClass .typeError)] && seeded.residual.builtins == space.builtins &&
    seeded.calls.isEmpty

#guard namedRaiseEvidence false
#guard namedRaiseEvidence true

private def handlerTargetEvidence (abrupt : Bool) : Bool := Id.run do
  let handler := [.assign "saved" (.name "caught")] ++
    if abrupt then [.assign "stopped" (.name "missing")] else [.assign "caught" (.integer 9)]
  let source : Source.Module := ⟨[
    .assign "caught" (.integer 5),
    .try_ [.raise_ (some (.name "TypeError")) none]
      [⟨some (.name "TypeError"), some "caught", handler⟩] []
      [.assign "cleaned" (.name "saved")]]⟩
  let .ok compiled := Run.compile source | return false
  let space : Namespace := ⟨[], [("TypeError", .exceptionClass .typeError)]⟩
  let instanceValue : Core.Module.SeededCall.Value := .exceptionInstance (.empty .typeError)
  let initial := (Run.seed .empty).bindGlobal "TypeError" (.exceptionClass .typeError)
  let (events, state) := Run.runPrefix compiled.table 10 (.ready initial compiled.instructions)
  let .finished ordinary completion := state | return false
  let seeded := run space compiled
  return events.isEmpty && completion == (if abrupt then .raised (.nameError "missing") else .normal) &&
    (ordinary.globals "caught").isNone && (ordinary.globals "cleaned").map seededValue == some instanceValue &&
    seeded.completion == (if abrupt then .error (.raised (.runtime (.nameError "missing"))) else .ok ()) &&
    seeded.residual.moduleGlobals == [("cleaned", instanceValue), ("saved", instanceValue)] &&
    seeded.residual.builtins == space.builtins && seeded.calls.isEmpty

#guard handlerTargetEvidence false
#guard handlerTargetEvidence true

private def moduleRaiseEvidence : Bool := Id.run do
  let source : Source.Module := ⟨[
    .assign "s" (.integer 1),
    .raise_ (some (.name "TypeError")) none,
    .assign "late" (.integer 2)]⟩
  let .ok compiled := Run.compile source | return false
  let error : Core.Closure.RuntimeError := .raisedInstance (.empty .typeError)
  let ordinarySeed := (Run.seed .empty).bindGlobal "TypeError" (.exceptionClass .typeError)
  let (events, state) := Run.runPrefix compiled.table 10 (.ready ordinarySeed compiled.instructions)
  let .finished ordinary completion := state | return false
  let space : Namespace := ⟨[], [("TypeError", .exceptionClass .typeError)]⟩
  let seeded := run space compiled
  let missing := run .empty compiled
  return events.isEmpty && completion == .raised error &&
    (ordinary.globals "s").map seededValue == some (.int 1) && (ordinary.globals "late").isNone &&
    seeded.completion == .error (.raised (.runtime error)) &&
    seeded.residual.moduleGlobals == [("s", .int 1)] && seeded.residual.builtins == space.builtins &&
    seeded.calls.isEmpty && missing.residual.moduleGlobals == [("s", .int 1)] &&
    missing.completion == .error (.raised (.runtime (.nameError "TypeError"))) && missing.calls.isEmpty

#guard moduleRaiseEvidence

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
