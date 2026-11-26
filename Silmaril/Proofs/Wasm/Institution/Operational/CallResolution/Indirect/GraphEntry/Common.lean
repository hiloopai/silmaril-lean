module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outer : Frame}
  {index : FuncIdx} {args : List Value} {active : Source.Activation}

theorem locals_typed (ready : entry.Checked program tables outer index args) :
    (entry.frame args).locals.map Value.type = entry.cont.owner.localTypes := by
  simp [Entry.frame, Declaration.frame, Graph.Function.localTypes, Function.comp_def, Value.zero, ready.typed]

theorem prepare_spec {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active) :
    entry.op.Prepared program tables (entry.frame args) stack active :=
  Source.prepare_spec (by simpa only [Entry.prepare, ite_eq_left ready.checked.typed] using ready.prepared)

private theorem checked_spine (blocks : List Context.Resume.Block) (saved : List Value)
    (fallthrough : List NumType) (enclosing : Graph.EnclosingLabels)
    (checked : (entry.region blocks).checkRegion program tables entry.cont.owner fallthrough enclosing
      (Prefix.stackTypes saved) = true) :
    let innermost := Context.Resume.Block.context blocks fallthrough enclosing
    entry.siteBody.checkRegion program tables entry.cont.owner innermost.1 innermost.2
      (Prefix.stackTypes (if blocks.isEmpty then saved else [])) = true ∧
      Context.Resume.Block.check entry.cont.owner blocks saved fallthrough enclosing = true := by
  induction blocks generalizing saved fallthrough enclosing with
  | nil => exact ⟨checked, rfl⟩
  | cons block rest ih =>
    have ⟨inside, tail⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨site, blocks⟩ := ih [] block.result.toList (fallthrough :: enclosing) inside
    exact ⟨by simpa [Context.Resume.Block.context] using site, Bool.and_eq_true_iff.mpr ⟨blocks, tail⟩⟩

private theorem checked_region (checked : entry.check program tables = true) :
    entry.siteBody.checkRegion program tables entry.cont.owner entry.cont.fallthrough entry.cont.enclosing
      (Prefix.stackTypes entry.initial) = true ∧ entry.cont.blockCheck = true :=
  checked_spine entry.cont.blocks entry.cont.owner.initial entry.cont.owner.declaration.results []
    (Bool.and_eq_true_iff.mp checked).2

private theorem checked_body (checked : entry.check program tables = true) :
    (entry.op.bind program tables entry.cont.owner.declaration.module).isSome = true ∧
      ∃ types, Prefix.check entry.cont.owner.localTypes (Prefix.stackTypes entry.initial)
        entry.before = some types ∧
        entry.op.checkTail entry.cont.owner entry.cont.fallthrough entry.cont.enclosing types entry.cont.code = true := by
  have body := (checked_region checked).1
  have head := (Bool.and_eq_true_iff.mp body).1
  have tail := (Bool.and_eq_true_iff.mp body).2
  refine ⟨head, ?_⟩
  cases checkedPrefix : Prefix.check entry.cont.owner.localTypes (Prefix.stackTypes entry.initial) entry.before with
  | none => simp [checkedPrefix] at tail
  | some types => exact ⟨types, rfl, by simpa [checkedPrefix] using tail⟩

theorem trace_exists {locals stack : List Value} {code : List Prefix.Op} {types : List NumType}
    (wellTyped : Prefix.WellTyped locals stack code types) :
    ∃ states result, OperandTrace locals stack code states result := by
  induction code generalizing stack with
  | nil => exact ⟨[], .values stack, .done stack⟩
  | cons op rest ih =>
    obtain ⟨result, step⟩ := Prefix.progress wellTyped
    cases result with
    | values next =>
      obtain ⟨states, outcome, trace⟩ := ih (Prefix.preserve step wellTyped)
      exact ⟨_, outcome, .value step trace⟩
    | trap saved => exact ⟨_, .trap saved rest, .trap step⟩

theorem operand_trace_exists (ready : entry.Checked program tables outer index args) :
    ∃ states result, entry.OperandTrace args states result := by
  obtain ⟨_, types, checkedPrefix, _⟩ := checked_body ready.source
  have typed : Prefix.WellTyped (entry.frame args).locals entry.initial entry.before types.reverse := by
    simpa only [Prefix.WellTyped, locals_typed ready, List.reverse_reverse] using checkedPrefix
  exact trace_exists typed

private def ResultTyped (locals : List Value) (types : List NumType) : OperandResult → Prop
  | .values values => Prefix.WellTyped locals values [] types
  | .trap _ _ => True

private theorem trace_finish {locals stack : List Value} {code : List Prefix.Op} {types : List NumType}
    {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals stack code states result) (typed : Prefix.WellTyped locals stack code types) :
    ResultTyped locals types result := by
  induction trace with
  | done => exact typed
  | value step _ ih => exact ih (Prefix.preserve step typed)
  | trap => trivial

theorem trace_values {locals stack output : List Value} {code : List Prefix.Op} {types : List NumType}
    {states : List OperandState} (trace : OperandTrace locals stack code states (.values output))
    (typed : Prefix.WellTyped locals stack code types) :
    Prefix.stackTypes output = types.reverse := by
  simpa only [ResultTyped, Prefix.WellTyped, Prefix.check, Option.some.injEq] using trace_finish trace typed

private theorem lookup_tail (ready : entry.Checked program tables outer index args)
    {states : List OperandState} {stack : List Value}
    (trace : entry.OperandTrace args states (.values stack)) :
    entry.op.checkTail entry.cont.owner entry.cont.fallthrough entry.cont.enclosing
      (Prefix.stackTypes stack) entry.cont.code = true := by
  obtain ⟨_, types, checkedPrefix, tail⟩ := checked_body ready.source
  have typed : Prefix.WellTyped (entry.frame args).locals entry.initial entry.before types.reverse := by
    simpa only [Prefix.WellTyped, locals_typed ready, List.reverse_reverse] using checkedPrefix
  have endTyped := trace_finish trace typed
  have stackEq : Prefix.stackTypes stack = types := by
    simpa only [ResultTyped, Prefix.WellTyped, Prefix.check, List.reverse_reverse, Option.some.injEq] using endTyped
  simpa only [stackEq] using tail

theorem prepare_exists (ready : entry.Checked program tables outer index args)
    {states : List OperandState} {stack : List Value}
    (trace : entry.OperandTrace args states (.values stack)) :
    ∃ active, entry.prepare program tables args stack = some active := by
  have binding := (checked_body ready.source).1
  have tail := lookup_tail ready trace
  cases stackEq : entry.op.checkStack entry.cont.owner.declaration.module.types (Prefix.stackTypes stack) with
  | none => simp [Source.Op.checkTail, stackEq] at tail
  | some next =>
    simpa only [Entry.prepare, ite_eq_left ready.typed] using
      (Source.prepare_of_check (caller := entry.frame args) binding stackEq)

theorem resume_guard {states : List OperandState} {stack : List Value}
    (ready : entry.AtSite program tables outer index args states stack active)
    {call : Context.Invocation} (invoked : active.invocation program = some call) :
    call.Checked program ∧ entry.cont.Checked program call.caller call.saved call.site.signature.results := by
  have prepared := prepare_spec ready
  exact ⟨Source.invocation_checked prepared.checked (Bool.and_eq_true_iff.mp ready.checked.source).1 invoked,
    Source.resume_checked prepared invoked ready.checked.found rfl
      (locals_typed ready.checked) (lookup_tail ready.checked ready.trace) (checked_region ready.checked.source).2⟩

/-- A nonempty trace starts at the supplied prefix head. An empty trace
already supplies the lookup stack. -/
theorem operand_head {C : Type} (render : OperandState → C) (finish : OperandResult → C)
    (endValues : ∀ stack, finish (.values stack) = render (stack, []))
    {locals stack code states result} (trace : OperandTrace locals stack code states result) :
    (states.map render ++ [finish result]).head? = some (render (stack, code)) := by
  cases trace with
  | done stack => simp [endValues]
  | value => rfl
  | trap => rfl

theorem resolved_entry_ref {call : Context.Invocation} (invoked : active.invocation program = some call) :
    some call.address ∈ active.binding.site.table.refs ∧ program.lookup call.address = some call.callee ∧
      active.resolve program = some (.resolved call.address) := by
  obtain ⟨address, callee, resolved, found, rfl⟩ := Source.invocation_fields invoked
  refine ⟨?_, found, resolved⟩
  cases resolve_iff.mp resolved with
  | resolved entry _ _ => exact List.mem_of_getElem? entry

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Proofs
