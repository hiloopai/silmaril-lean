module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Field.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Thms
import Silmaril.Formats.Arrow.MixedFlat.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Incremental MixedFlat.Stream.Incremental.Failure
open MixedFlat.Stream.Incremental.Failure.Admitted
open MixedFlat.Stream.Incremental.Portable (reference reference_congr completed_exact)
open MixedFlat.Stream (BatchRange)
open Arrow.Framing.Incremental (Window)

private theorem current_budget {limits : ObservationLimits} {fields before current : Nat}
    (checked : Body.checkBudget limits fields (before + current) = .ok ()) :
    Body.checkBudget limits fields current = .ok () := by
  have rows : ¬ before + current > limits.totalRows := by
    intro exceeded
    simp [Body.checkBudget, exceeded] at checked
  have cells : ¬ fields * (before + current) > limits.totalCells := by
    intro exceeded
    simp [Body.checkBudget, rows, exceeded] at checked
  have currentRows : ¬ current > limits.totalRows := by omega
  have bound := Nat.mul_le_mul_left fields (Nat.le_add_left current before)
  have currentCells : ¬ fields * current > limits.totalCells := by omega
  simp [Body.checkBudget, currentRows, currentCells]

theorem readParsed_covered {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {rowsBefore : Nat} {fault : MixedFlat.Error}
    (source : body.wf = true) (extent : metadata.bodyLength = body.len)
    (aligned : body.len % 8 = 0) (bodyCap : body.len ≤ limits.observation.ipc.bodyBytes)
    (fieldCap : fields.length ≤ limits.observation.ipc.fields)
    (rowCap : metadata.batch.rowCount ≤ limits.observation.ipc.rows)
    (budget : Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount) = .ok ())
    (failed : MixedFlat.readParsed limits fields metadata body = .error fault) :
    ∃ cause : Cause, cause.batchError = .decode fault := by
  cases binding : MixedFlat.bindBatch limits fields metadata body with
  | error rejected =>
    have same : rejected = fault := by
      simpa [MixedFlat.readParsed, binding, bind, Except.bind] using failed
    subst fault
    have batchBudget := current_budget budget
    simp only [MixedFlat.bindBatch, dite_eq_left source, dite_eq_left extent, ne_eq, aligned, not_true_eq_false,
      ite_false, Nat.not_lt_of_ge bodyCap, Nat.not_lt_of_ge fieldCap, Nat.not_lt_of_ge rowCap,
      batchBudget, Except.mapError, bind, Except.bind] at binding
    cases assignment : MixedFlat.assign metadata.batch.rowCount fields metadata.batch.nodes
        metadata.counts metadata.batch.buffers 0 with
    | error assignmentError =>
      have same : MixedFlat.Error.plan assignmentError = rejected := by
        simpa [assignment, Except.mapError] using binding
      exact ⟨.layout (.assignment assignmentError), by simp [Cause.batchError, BodyLayout.Cause.decodeError, same]⟩
    | ok accepted =>
      simp only [assignment] at binding
      split at binding
      · simp [pure, Except.pure] at binding
      · have same : MixedFlat.Error.body (.malformed .batchLayout) = rejected := by
          simpa [throw, throwThe, MonadExceptOf.throw] using binding
        exact ⟨.layout .descriptors, by simp [Cause.batchError, BodyLayout.Cause.decodeError, same]⟩
  | ok plan =>
    cases columns : MixedFlat.readGroups limits.view body 0 plan.assignment.groups with
    | error rejected =>
      have same : rejected = fault := by
        simpa [MixedFlat.readParsed, binding, columns, bind, Except.bind] using failed
      obtain ⟨index, cause, exactCause⟩ := MixedFlat.readGroups_error_field columns
      exact ⟨.column index cause, by rw [← same, exactCause]; rfl⟩
    | ok observed =>
      simp [MixedFlat.readParsed, binding, columns, bind, Except.bind, pure, Except.pure] at failed

theorem rejection_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run := by
  rcases run with ⟨fields, batches, ordinal, offset, cause, ran⟩
  cases cause with
  | metadata fault =>
    exact RecordMetadata.metadata_exact ⟨fields, batches, ordinal, offset, fault, ran⟩
  | layout fault =>
    exact BodyLayout.layout_exact ⟨fields, batches, ordinal, offset, fault, ran⟩
  | column index fault =>
    exact Field.field_exact ⟨fields, batches, ordinal, offset, index, fault, ran⟩

private theorem replay_ordinal {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {before final : Position} {batches : List (Published fields)}
    (replay : Replay limits input fields before batches final) :
    final.ordinal = before.ordinal + batches.length := by
  induction replay with
  | stop => simp
  | next _ _ ih =>
    simp only [Position.after] at ih
    simp only [List.length_cons]
    omega

theorem ordinal_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : run.ordinal = run.batches.length := by
  obtain ⟨_, _, _, _, replay, ordinal, _, _, _, _⟩ := rejection_exact run
  simpa only [Position.ofRunning, ordinal, List.length_map, Nat.zero_add] using replay_ordinal replay

theorem pull_exact {limits : MixedFlat.Stream.Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    MixedFlat.Stream.Events.readAll limits.mixed (reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ := by
  obtain ⟨_, _, _, schemaRead, replay, _, _, _, failed, _⟩ := rejection_exact run
  simpa only [List.map_map, Function.comp_def, Delivered.published, Run.nativeCause] using
    replay_read_all_error rfl schemaRead replay failed

theorem schedules_equivalent {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace := by
  have sameRef := reference_congr leftWf rightWf octets
  have checkedA := rejection_exact a
  have checkedB := rejection_exact b
  rcases a with ⟨fieldsA, batchesA, ordinalA, offsetA, causeA, runA⟩
  rcases b with ⟨fieldsB, batchesB, ordinalB, offsetB, causeB, runB⟩
  obtain ⟨startA, runningA, rangeA, schemaA, replayA, _, _, _, failedA, _⟩ := checkedA
  obtain ⟨startB, runningB, rangeB, schemaB, replayB, _, _, _, failedB, _⟩ := checkedB
  rw [sameRef] at schemaA replayA failedA
  obtain ⟨fieldsEq, startEq⟩ := Prod.mk.inj (Except.ok.inj (schemaA.symm.trans schemaB))
  dsimp only at fieldsEq startEq
  subst fieldsB
  subst startB
  obtain ⟨publishedEq, _, coordinates⟩ := replay_unique_at_error replayA replayB failedA failedB
  have rangesEq := congrArg (List.map fun (item : Published fieldsA) => item.1.range) publishedEq
  have eventsEq := congrArg (List.map fun (item : Published fieldsA) => item.2) publishedEq
  obtain ⟨ordinalEq, offsetEq, causeEq⟩ :
      ordinalA = ordinalB ∧ offsetA = offsetB ∧ causeA.batchError = causeB.batchError := by
    simpa using coordinates
  simp only [List.map_map, Function.comp_def, Delivered.published] at rangesEq eventsEq
  simp [Run.ranges, Run.trace, Run.cause, feedError, rangesEq, eventsEq,
    ordinalEq, offsetEq, causeEq]

theorem no_success {limits : MixedFlat.Stream.Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, immutableError⟩ := rejection_exact failed
  rw [reference_congr leftWf rightWf octets] at immutableError
  have immutableSuccess := (completed_exact succeeded).2.1
  rw [immutableError] at immutableSuccess
  contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted
