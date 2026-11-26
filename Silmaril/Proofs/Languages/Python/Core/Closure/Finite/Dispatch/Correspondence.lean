module

public import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs
import Silmaril.Languages.Python.Core.Closure.Finite.Thms
import Silmaril.Semantics.Operational.Environment.Finite.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Dispatch

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Finite
open Silmaril.Languages.Python.Core.Closure.Finite.Dispatch
open Silmaril.Semantics.Operational

variable {Body Continuation : Layout → Type} {layout : Layout}

theorem exists_codeRows_project_iff (table : Silmaril.Languages.Python.Core.Closure.Dispatch.CodeTable Body) :
    (∃ rows : CodeRows Body, rows.project = table) ↔ ∃ keys, Environment.SupportedBy table keys := by
  constructor
  · rintro ⟨rows, rfl⟩
    exact ⟨rows.keys, Environment.Finite.view_supported rows⟩
  · rintro ⟨keys, supported⟩
    exact ⟨Environment.Finite.encode table keys, Environment.Finite.view_encode supported⟩

theorem freshFrame_project (fn : Function) (heap : HeapTable) :
    (freshFrame fn heap).project = fn.freshFrame heap.project := by
  change ((heap.reserve fn.code.layout.owned).project, (fn.freshFrame heap.project).2) = _
  rw [heap.reserve_project]
  rfl

theorem writeArguments_project (writes : List (ParameterSlot layout × Value)) (before : Snapshot layout) :
    (writeArguments writes before).map Snapshot.project = Call.writeArguments writes before.project := by
  induction writes generalizing before with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨slot, value⟩ := pair
    have agrees := before.write_project slot.slot value
    change ((before.write slot.slot value).bind (writeArguments rest)).map Snapshot.project =
      (before.frame.write before.heap.project slot.slot value).bind (Call.writeArguments rest)
    rw [← agrees]
    cases before.write slot.slot value with
    | error failure => rfl
    | ok next => exact ih next

theorem bindPositional_project (parameters : Parameters layout) (arguments : List Value)
    (before : Snapshot layout) :
    (bindPositional parameters arguments before).map Snapshot.project =
      Call.bindPositional parameters arguments before.project := by
  by_cases arity : arguments.length = parameters.slots.length
  · simp [bindPositional, Call.bindPositional, arity, writeArguments_project]
  · simp [bindPositional, Call.bindPositional, arity, Except.map]

theorem enter_project (fn : Function) (parameters : Parameters fn.code.layout) (arguments : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    (enter fn parameters arguments heap).map
      (fun environment => ⟨environment.project, caller :: stack⟩) =
      Call.enter fn parameters arguments heap.project caller stack := by
  unfold enter Call.enter
  cases Call.firstDangling fn heap.project with
  | some identity => rfl
  | none =>
    cases Call.completeArguments parameters fn.positionalDefaults arguments with
    | error error => rfl
    | ok completed =>
      simp only [bind, Except.bind]
      rw [← freshFrame_project fn heap, ← bindPositional_project]
      cases bindPositional parameters completed (freshFrame fn heap) <;> rfl

theorem dispatch_project (rows : CodeRows Body) (callee : Value) (arguments : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    (dispatch rows callee arguments heap caller stack).map Active.project =
      Silmaril.Languages.Python.Core.Closure.Dispatch.dispatch rows.project callee arguments heap.project caller stack := by
  cases callee with
  | function fn =>
    simp only [dispatch, Silmaril.Languages.Python.Core.Closure.Dispatch.dispatch]
    cases Silmaril.Languages.Python.Core.Closure.Dispatch.resolve rows.project fn.code with
    | error failure => rfl
    | ok definition =>
      simp only
      rw [← enter_project fn definition.parameters arguments heap caller stack]
      cases enter fn definition.parameters arguments heap <;> rfl
  | _ => rfl

theorem finish_project (heap : HeapTable) (stack : List (Call.Saved Continuation)) (result : Result) :
    (finish heap stack result).project = Call.finish heap.project stack result := by
  cases stack <;> rfl

end Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Dispatch
