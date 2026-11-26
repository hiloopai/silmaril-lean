module

public import Silmaril.Languages.Python.Core.Closure.Executor.Defs
public import Silmaril.Languages.Python.Core.Closure.Dispatch.Thms
public import Silmaril.Languages.Python.Core.Closure.Call.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Executor

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Executor

variable {globals : GlobalLookup} {layout : Layout} {heap : Heap} {frame : Frame layout}

private theorem readMetadata_iff {field : MetadataField} {table : CodeTable} {fn : Function}
    {names : List String} : readMetadata field table (.function fn) = .ok names ↔
      ∃ definition, Dispatch.Resolves table fn.code definition ∧ field.select definition = some names := by
  simp only [← Dispatch.resolve_iff]
  cases resolved : Dispatch.resolve table fn.code with
  | error error => simp [readMetadata, resolved]
  | ok definition =>
    cases tuple : field.select definition <;> simp [readMetadata, resolved, tuple]

theorem readFreevars_iff {table : CodeTable} {fn : Function} {names : List String} :
    readFreevars table (.function fn) = .ok names ↔
      ∃ definition, Dispatch.Resolves table fn.code definition ∧ definition.freevars = some names :=
  readMetadata_iff (field := .freevars)

theorem readCellvars_iff {table : CodeTable} {fn : Function} {names : List String} :
    readCellvars table (.function fn) = .ok names ↔
      ∃ definition, Dispatch.Resolves table fn.code definition ∧ definition.cellvars = some names :=
  readMetadata_iff (field := .cellvars)

theorem readCodeNames_iff {table : CodeTable} {fn : Function} {names : List String} :
    readCodeNames table (.function fn) = .ok names ↔
      ∃ definition, Dispatch.Resolves table fn.code definition ∧
        definition.codeNames = some ⟨.cpython3135ExecOptimize0, names⟩ := by
  rw [readMetadata_iff]
  refine exists_congr fun definition => and_congr_right fun _ => ?_
  cases tuple : definition.codeNames with
  | none => simp [MetadataField.select, tuple]
  | some metadata =>
    obtain ⟨profile, names⟩ := metadata
    cases profile <;> simp [MetadataField.select, tuple]

private theorem name_read_eval (source : NameRead layout) :
    source.operand.evalIn globals heap frame = source.evalIn globals heap frame := by
  cases source <;> rfl

private theorem eval_eq {operand : Operand layout} {result : Except Failure Value}
    (eval : EvaluatesIn globals heap frame operand result) : operand.evalIn globals heap frame = result := by
  induction eval with
  | globalFound found => simp [Operand.evalIn, NameRead.evalIn, found]
  | globalMissing missing => simp [Operand.evalIn, NameRead.evalIn, missing]
  | eqInt _ ih => rw [Operand.evalIn, ← name_read_eval, ih]
  | binaryLeftError _ first => simp [Operand.evalIn, first, Except.bind]
  | binaryRightError _ _ first second => simp [Operand.evalIn, first, second, Except.bind]
  | binaryValues _ _ first second => simp [Operand.evalIn, first, second, Except.bind]
  | _ => rfl

private theorem name_rule (source : NameRead layout) :
    EvaluatesIn globals heap frame source.operand (source.evalIn globals heap frame) := by
  cases source with
  | slot location => exact .read location
  | global name =>
    cases found : globals name with
    | none => simpa [NameRead.operand, NameRead.evalIn, found] using
        (EvaluatesIn.globalMissing (heap := heap) (frame := frame) found)
    | some value => simpa [NameRead.operand, NameRead.evalIn, found] using
        (EvaluatesIn.globalFound (heap := heap) (frame := frame) found)

private theorem eval_rule (operand : Operand layout) :
    EvaluatesIn globals heap frame operand (operand.evalIn globals heap frame) := by
  induction operand with
  | readGlobal name => exact name_rule (.global name)
  | eqInt source _ => exact .eqInt (name_rule source)
  | binaryInt op left right ihLeft ihRight =>
    cases first : left.evalIn globals heap frame with
    | error error =>
      simpa [Operand.evalIn, first, Except.bind] using
        (EvaluatesIn.binaryLeftError (right := right) (first ▸ ihLeft))
    | ok lhs =>
      cases second : right.evalIn globals heap frame with
      | error error =>
        simpa [Operand.evalIn, first, second, Except.bind] using
          (EvaluatesIn.binaryRightError (first ▸ ihLeft) (second ▸ ihRight))
      | ok rhs =>
        simpa [Operand.evalIn, first, second, Except.bind] using
          (EvaluatesIn.binaryValues (first ▸ ihLeft) (second ▸ ihRight))
  | _ => constructor

private theorem arguments_eq {operands : List (Operand layout)} {result : Except Failure (List Value)}
    (eval : ArgumentsIn globals heap frame operands result) : evalArgumentsIn globals heap frame operands = result := by
  induction eval with
  | nil => rfl
  | headError head => simp [evalArgumentsIn, eval_eq head, Except.bind]
  | tailError head _ tail => simp [evalArgumentsIn, eval_eq head, tail, Except.bind, Except.map]
  | cons head _ tail => simp [evalArgumentsIn, eval_eq head, tail, Except.bind, Except.map]

private theorem arguments_rule (operands : List (Operand layout)) :
    ArgumentsIn globals heap frame operands (evalArgumentsIn globals heap frame operands) := by
  induction operands with
  | nil => exact .nil
  | cons head tail ih =>
    cases first : head.evalIn globals heap frame with
    | error error =>
      simpa [evalArgumentsIn, first, Except.bind] using
        (ArgumentsIn.headError (tail := tail) (first ▸ eval_rule head))
    | ok value =>
      cases remaining : evalArgumentsIn globals heap frame tail with
      | error error =>
        simpa [evalArgumentsIn, first, remaining, Except.bind, Except.map] using
          (ArgumentsIn.tailError (first ▸ eval_rule head) (remaining ▸ ih))
      | ok values =>
        simpa [evalArgumentsIn, first, remaining, Except.bind, Except.map] using
          (ArgumentsIn.cons (first ▸ eval_rule head) (remaining ▸ ih))

private theorem inputs_eq {callee : Operand layout} {arguments : List (Operand layout)}
    {result : Except Failure (Value × List Value)} (eval : InputsIn globals heap frame callee arguments result) :
    evalCallIn globals heap frame callee arguments = result := by
  cases eval with
  | calleeError callee => simp [evalCallIn, eval_eq callee, Except.bind]
  | argumentError callee args => simp [evalCallIn, eval_eq callee, arguments_eq args, Except.bind, Except.map]
  | ok callee args => simp [evalCallIn, eval_eq callee, arguments_eq args, Except.bind, Except.map]

private theorem inputs_rule (callee : Operand layout) (arguments : List (Operand layout)) :
    InputsIn globals heap frame callee arguments (evalCallIn globals heap frame callee arguments) := by
  cases first : callee.evalIn globals heap frame with
  | error error =>
    simpa [evalCallIn, first, Except.bind] using
      (InputsIn.calleeError (arguments := arguments) (first ▸ eval_rule callee))
  | ok value =>
    cases rest : evalArgumentsIn globals heap frame arguments with
    | error error =>
      simpa [evalCallIn, first, rest, Except.bind, Except.map] using
        (InputsIn.argumentError (first ▸ eval_rule callee) (rest ▸ arguments_rule arguments))
    | ok values =>
      simpa [evalCallIn, first, rest, Except.bind, Except.map] using
        (InputsIn.ok (first ▸ eval_rule callee) (rest ▸ arguments_rule arguments))

variable {table : CodeTable} {args : List Value} {callee : Value} {failure : Dispatch.Failure}
  {caller : Call.Saved Continuation} {stack : Stack}

private theorem rejected_eq (rejected : Rejects table args heap callee failure) :
    Dispatch.dispatch table callee args heap caller stack = .error failure := by
  cases rejected with
  | nonCallableNone => rfl
  | nonCallable value => rfl
  | nonCallableBool value => rfl
  | missing fn absent => simp [Dispatch.dispatch, Dispatch.resolve_missing absent]
  | mismatch fn entry found different => simp [Dispatch.dispatch, Dispatch.resolve_layout_mismatch found different]
  | dangling found first => simp [Dispatch.dispatch, Dispatch.resolve_iff.mpr found, Call.enter, first]
  | arguments found live rejected =>
    simp [Dispatch.dispatch, Dispatch.resolve_iff.mpr found, Call.enter, live, rejected, Except.bind]

private theorem captures_live {fn : Function} (valid : Call.firstDangling fn heap = none) :
    ∀ identity ∈ fn.captures.toList, identity.address < heap.next := by
  change fn.captures.toList.find? (fun identity => decide (heap.next ≤ identity.address)) = none at valid
  intro identity captured
  have answer := List.find?_eq_none.mp valid identity captured
  simpa [Nat.not_le] using answer

private theorem rejected_rule (rejected : Dispatch.dispatch table callee args heap caller stack = .error failure) :
    Rejects table args heap callee failure := by
  cases callee with
  | none =>
    simp [Dispatch.dispatch] at rejected
    subst failure
    exact .nonCallableNone
  | int value =>
    simp [Dispatch.dispatch] at rejected
    subst failure
    exact .nonCallable value
  | bool value =>
    simp [Dispatch.dispatch] at rejected
    subst failure
    exact .nonCallableBool value
  | function fn =>
    cases found : table fn.code.key with
    | none =>
      simp [Dispatch.dispatch, Dispatch.resolve_missing found] at rejected
      subst failure
      exact .missing fn found
    | some entry =>
      by_cases same : entry.layout = fn.code.layout
      · obtain ⟨actual, definition⟩ := entry
        change actual = fn.code.layout at same
        subst actual
        have member : Dispatch.Resolves table fn.code definition := found
        have resolved := Dispatch.resolve_iff.mpr member
        cases check : Call.firstDangling fn heap with
        | some identity =>
          simp [Dispatch.dispatch, resolved, Call.enter, check] at rejected
          subst failure
          exact .dangling member check
        | none =>
          cases completion : Call.completeArguments definition.parameters fn.positionalDefaults args with
          | ok completed =>
            obtain ⟨entered, success⟩ := Call.enter_complete (caller := caller) (stack := stack)
              completion (captures_live check)
            simp [Dispatch.dispatch, resolved, success] at rejected
          | error error =>
            simp [Dispatch.dispatch, resolved, Call.enter, check, completion, Except.bind] at rejected
            subst failure
            exact .arguments member check completion
      · simp [Dispatch.dispatch, Dispatch.resolve_layout_mismatch found same] at rejected
        subst failure
        exact .mismatch fn entry found same

private theorem store_eq {destination : Slot layout} {value : Value} {body : Body layout}
    {transition : Transition} (stored : Stores heap frame destination value body stack transition) :
    resumeStore heap frame destination value body stack = transition := by
  cases stored with
  | ok written => simp [resumeStore, written]
  | error written => simp [resumeStore, written]

private theorem store_rule (destination : Slot layout) (value : Value) (body : Body layout) (stack : Stack) :
    Stores heap frame destination value body stack (resumeStore heap frame destination value body stack) := by
  cases written : frame.write heap destination value with
  | error error => simpa [resumeStore, written] using
      (Stores.error (body := body) (stack := stack) written)
  | ok environment =>
    obtain ⟨updated, frame'⟩ := environment
    simpa [resumeStore, written] using (Stores.ok (body := body) (stack := stack) written)

theorem advance_of_step {source target : State} {label : Option Event}
    (step : StepIn table globals source label target) : advanceIn table globals source = some (label, target) := by
  cases step with
  | ret eval => simp [advanceIn, eval_eq eval]
  | retError eval => simp [advanceIn, eval_eq eval]
  | store eval wrote => simp [advanceIn, eval_eq eval, store_eq wrote]
  | storeError eval => simp [advanceIn, eval_eq eval]
  | assertTrue eval holds => simp [advanceIn, eval_eq eval, holds]
  | assertFalse eval fails => simp [advanceIn, eval_eq eval, fails]
  | assertError eval => simp [advanceIn, eval_eq eval]
  | assertFreevarsTrue eval => simp [advanceIn, eval]
  | assertFreevarsFalse eval => simp [advanceIn, eval]
  | assertFreevarsError eval => simp [advanceIn, eval]
  | assertCellvarsTrue eval => simp [advanceIn, eval]
  | assertCellvarsFalse eval => simp [advanceIn, eval]
  | assertCellvarsError eval => simp [advanceIn, eval]
  | assertCodeNamesTrue eval => simp [advanceIn, eval]
  | assertCodeNamesFalse eval => simp [advanceIn, eval]
  | assertCodeNamesError eval => simp [advanceIn, eval]
  | call evaluated entered => simp [advanceIn, inputs_eq evaluated, Dispatch.dispatch_iff.mpr entered]
  | callError evaluated => simp [advanceIn, inputs_eq evaluated]
  | rejected evaluated reject => simp [advanceIn, inputs_eq evaluated, rejected_eq reject]
  | complete heap result => rfl
  | resume heap caller stack result => rfl
  | receive destination wrote => simp [advanceIn, destination, store_eq wrote]
  | receiveDiscard destination => simp [advanceIn, destination]
  | receiveReturn continuation => simp [advanceIn, continuation]
  | receiveError heap caller stack error => rfl

theorem step_of_advance {source : State} {transition : Transition}
    (advanced : advanceIn table globals source = some transition) : StepIn table globals source transition.1 transition.2 := by
  cases source with
  | running heap frame body stack =>
    cases body with
    | ret operand =>
      cases evaluated : operand.evalIn globals heap frame with
      | ok value =>
        simp only [advanceIn, evaluated, Option.some.injEq] at advanced
        subst transition
        exact .ret (evaluated ▸ eval_rule operand)
      | error error =>
        simp only [advanceIn, evaluated, Option.some.injEq] at advanced
        subst transition
        exact .retError (evaluated ▸ eval_rule operand)
    | store destination operand next =>
      cases evaluated : operand.evalIn globals heap frame with
      | ok value =>
        simp only [advanceIn, evaluated, Option.some.injEq] at advanced
        subst transition
        exact .store (evaluated ▸ eval_rule operand) (store_rule destination value next stack)
      | error error =>
        simp only [advanceIn, evaluated, Option.some.injEq] at advanced
        subst transition
        exact .storeError (evaluated ▸ eval_rule operand)
    | assert test next =>
      cases evaluated : test.evalIn globals heap frame with
      | error error =>
        simp only [advanceIn, evaluated, Option.some.injEq] at advanced
        subst transition
        exact .assertError (evaluated ▸ eval_rule test)
      | ok value =>
        cases truth : value.truth with
        | false =>
          simp [advanceIn, evaluated, truth] at advanced
          subst transition
          exact .assertFalse (evaluated ▸ eval_rule test) truth
        | true =>
          simp [advanceIn, evaluated, truth] at advanced
          subst transition
          exact .assertTrue (evaluated ▸ eval_rule test) truth
    | assertFreevars test next =>
      cases evaluated : test.evalIn table globals heap frame with
      | error error =>
        simp [advanceIn, evaluated] at advanced
        subst transition
        exact .assertFreevarsError evaluated
      | ok holds =>
        cases holds <;> simp [advanceIn, evaluated] at advanced <;> subst transition
        · exact .assertFreevarsFalse evaluated
        · exact .assertFreevarsTrue evaluated
    | assertCellvars test next =>
      cases evaluated : test.evalIn table globals heap frame with
      | error error =>
        simp [advanceIn, evaluated] at advanced
        subst transition
        exact .assertCellvarsError evaluated
      | ok holds =>
        cases holds <;> simp [advanceIn, evaluated] at advanced <;> subst transition
        · exact .assertCellvarsFalse evaluated
        · exact .assertCellvarsTrue evaluated
    | assertCodeNames test next =>
      cases evaluated : test.evalIn table globals heap frame with
      | error error =>
        simp [advanceIn, evaluated] at advanced
        subst transition
        exact .assertCodeNamesError evaluated
      | ok holds =>
        cases holds <;> simp [advanceIn, evaluated] at advanced <;> subst transition
        · exact .assertCodeNamesFalse evaluated
        · exact .assertCodeNamesTrue evaluated
    | invoke callee arguments continuation =>
      cases evaluated : evalCallIn globals heap frame callee arguments with
      | error error =>
        simp only [advanceIn, evaluated, Option.some.injEq] at advanced
        subst transition
        exact .callError (evaluated ▸ inputs_rule callee arguments)
      | ok inputs =>
        obtain ⟨value, values⟩ := inputs
        cases dispatched : Dispatch.dispatch table value values heap ⟨_, frame, continuation⟩ stack with
        | error failure =>
          simp only [advanceIn, evaluated, dispatched, Option.some.injEq] at advanced
          subst transition
          exact .rejected (evaluated ▸ inputs_rule callee arguments) (rejected_rule dispatched)
        | ok active =>
          simp only [advanceIn, evaluated, dispatched, Option.some.injEq] at advanced
          subst transition
          exact .call (evaluated ▸ inputs_rule callee arguments) (Dispatch.dispatch_iff.mp dispatched)
  | delivering heap stack result =>
    cases stack with
    | nil =>
      simp only [advanceIn, Call.finish, Option.some.injEq] at advanced
      subst transition
      exact .complete heap result
    | cons caller older =>
      simp only [advanceIn, Call.finish, Option.some.injEq] at advanced
      subst transition
      exact .resume heap caller older result
  | receiving heap caller stack result =>
    cases result with
    | ok value =>
      cases continuation : caller.continuation with
      | none =>
        simp only [advanceIn, continuation, Option.some.injEq] at advanced
        subst transition
        exact .receiveReturn continuation
      | some resume =>
        obtain ⟨destination, body⟩ := resume
        cases destination with
        | store slot =>
          simp only [advanceIn, continuation, Option.some.injEq] at advanced
          subst transition
          exact .receive continuation (store_rule slot value body stack)
        | discard =>
          simp only [advanceIn, continuation, Option.some.injEq] at advanced
          subst transition
          exact .receiveDiscard continuation
    | error error =>
      simp only [advanceIn, Option.some.injEq] at advanced
      subst transition
      exact .receiveError heap caller stack error
  | finished heap result => simp [advanceIn] at advanced
  | faulted heap stack fault => simp [advanceIn] at advanced

theorem run_path (table : CodeTable) (globals : GlobalLookup) (fuel : Nat) (source : State) :
    (labelledIn table globals).Path source (runPrefixIn table globals fuel source).1 (runPrefixIn table globals fuel source).2 := by
  induction fuel generalizing source with
  | zero => exact .nil source
  | succ fuel ih =>
    cases selected : advanceIn table globals source with
    | none => simpa [runPrefixIn, selected] using (Semantics.Operational.Labelled.Path.nil (sem := labelledIn table globals) source)
    | some edge =>
      obtain ⟨label, target⟩ := edge
      have stepped := step_of_advance selected
      cases label with
      | none =>
        simpa [runPrefixIn, selected] using
          ((.silent stepped (ih target)) : (labelledIn table globals).Path source
            (runPrefixIn table globals fuel target).1 (runPrefixIn table globals fuel target).2)
      | some event =>
        simpa [runPrefixIn, selected] using
          ((.visible stepped (ih target)) : (labelledIn table globals).Path source
            (event :: (runPrefixIn table globals fuel target).1) (runPrefixIn table globals fuel target).2)

end Silmaril.Proofs.Languages.Python.Core.Closure.Executor
