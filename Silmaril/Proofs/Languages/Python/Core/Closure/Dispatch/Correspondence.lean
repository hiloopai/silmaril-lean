module

public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Dispatch

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Dispatch

variable {Body Continuation : Layout → Type} {table : CodeTable Body}

theorem resolve_iff {ref : CodeRef} {definition : Definition Body ref.layout} :
    resolve table ref = .ok definition ↔ Resolves table ref definition := by
  constructor
  · intro resolved
    cases found : table ref.key with
    | none => simp [resolve, found] at resolved
    | some entry =>
      have layout : entry.layout = ref.layout := by
        by_contra different
        simp [resolve, found, different] at resolved
      obtain ⟨actual, body⟩ := entry
      change actual = ref.layout at layout
      subst actual
      simp [resolve, found] at resolved
      subst body
      exact found
  · intro found
    change table ref.key = some ⟨ref.layout, definition⟩ at found
    simp [resolve, found]

theorem prepare_length {layout : Layout} {definition : Definition Body layout}
    {arguments bound : List Value} (prepared : definition.prepare arguments = .ok bound) :
    bound.length = definition.parameters.slots.length := by
  cases profile : definition.variadic with
  | none =>
    simp only [Definition.prepare, profile] at prepared
    split at prepared
    · cases prepared
      assumption
    · contradiction
  | some signature =>
    have selected : signature.val.complete arguments = .ok bound := by
      simpa [Definition.prepare, profile] using prepared
    rw [← signature.property]
    exact Call.VariadicParameters.complete_length selected

variable {callee : Value} {arguments : List Value} {heap : Heap}
  {caller : Call.Saved Continuation} {stack : List (Call.Saved Continuation)}
  {active : Active Body Continuation}

theorem dispatch_sound (launched : dispatch table callee arguments heap caller stack = .ok active) :
    Dispatches table arguments heap caller stack callee active := by
  cases callee with
  | none => simp [dispatch] at launched
  | int value => simp [dispatch] at launched
  | bool value => simp [dispatch] at launched
  | tuple items => simp [dispatch] at launched
  | function fn =>
    cases resolved : resolve table fn.code with
    | error error => simp [dispatch, resolved] at launched
    | ok definition =>
      cases live : Call.firstDangling fn heap with
      | some identity => simp [dispatch, resolved, live] at launched
      | none =>
        cases prepared : definition.prepare arguments with
        | error error => simp [dispatch, resolved, live, prepared] at launched
        | ok bound =>
          cases entered : Call.enter fn definition.parameters bound heap caller stack with
          | error error =>
            simp [dispatch, resolved, live, prepared, entered] at launched
          | ok entry =>
            simp [dispatch, resolved, live, prepared, entered] at launched
            subst active
            obtain ⟨binding, saved⟩ := Call.enter_spec entered
            have exactEntry : entry = ⟨entry.environment, caller :: stack⟩ := by
              cases entry
              simp_all
            rw [exactEntry]
            exact .function (resolve_iff.mp resolved) prepared
              (fun _ captured => Call.enter_captures_live entered captured) (Call.bind_iff.mp binding).2

theorem dispatch_complete (launched : Dispatches table arguments heap caller stack callee active) :
    dispatch table callee arguments heap caller stack = .ok active := by
  cases launched with
  | @function fn definition environment bound code prepared captures writes =>
    have arity := prepare_length prepared
    obtain ⟨entered, success⟩ := Call.enter_complete (caller := caller) (stack := stack) arity captures
    obtain ⟨binding, saved⟩ := Call.enter_spec success
    have expected : Call.bindPositional definition.parameters bound (fn.freshFrame heap) =
        .ok environment := Call.bind_iff.mpr ⟨arity, writes⟩
    have same : entered.environment = environment := Except.ok.inj (binding.symm.trans expected)
    have exactEntry : entered = ⟨environment, caller :: stack⟩ := by
      cases entered
      simp_all
    have live : Call.firstDangling fn heap = none :=
      List.find?_eq_none.mpr (fun identity member => by simpa using captures identity member)
    simp [dispatch, resolve_iff.mpr code, live, prepared, success, exactEntry]

end Silmaril.Proofs.Languages.Python.Core.Closure.Dispatch
