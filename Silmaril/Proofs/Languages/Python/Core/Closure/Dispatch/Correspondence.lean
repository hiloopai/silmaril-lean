module

public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Thms

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

variable {callee : Value} {arguments : List Value} {heap : Heap}
  {caller : Call.Saved Continuation} {stack : List (Call.Saved Continuation)}
  {active : Active Body Continuation}

theorem dispatch_sound (launched : dispatch table callee arguments heap caller stack = .ok active) :
    Dispatches table arguments heap caller stack callee active := by
  cases callee with
  | none => simp [dispatch] at launched
  | int value => simp [dispatch] at launched
  | bool value => simp [dispatch] at launched
  | function fn =>
    cases resolved : resolve table fn.code with
    | error error => simp [dispatch, resolved] at launched
    | ok definition =>
      cases entered : Call.enter fn definition.parameters arguments heap caller stack with
      | error error => simp [dispatch, resolved, entered] at launched
      | ok entry =>
        simp [dispatch, resolved, entered] at launched
        subst active
        obtain ⟨⟨_, completion, binding⟩, saved⟩ := Call.enter_spec entered
        have writes := (Call.bind_iff.mp binding).2
        have exactEntry : entry = ⟨entry.environment, caller :: stack⟩ := by
          cases entry
          simp_all
        rw [exactEntry]
        exact .function (resolve_iff.mp resolved) completion
          (fun _ captured => Call.enter_captures_live entered captured) writes

theorem dispatch_complete (launched : Dispatches table arguments heap caller stack callee active) :
    dispatch table callee arguments heap caller stack = .ok active := by
  cases launched with
  | @function fn definition environment code completed completion captures writes =>
    obtain ⟨entered, success⟩ := Call.enter_complete (caller := caller) (stack := stack) completion captures
    obtain ⟨⟨actual, checked, binding⟩, saved⟩ := Call.enter_spec success
    have sameArgs := Except.ok.inj (checked.symm.trans completion)
    subst actual
    have expected : Call.bindPositional definition.parameters completed (fn.freshFrame heap) =
        .ok environment := Call.bind_iff.mpr ⟨Call.completeArguments_length completion, writes⟩
    have same : entered.environment = environment := Except.ok.inj (binding.symm.trans expected)
    have exactEntry : entered = ⟨environment, caller :: stack⟩ := by
      cases entered
      simp_all
    simp [dispatch, resolve_iff.mpr code, success, exactEntry]

end Silmaril.Proofs.Languages.Python.Core.Closure.Dispatch
