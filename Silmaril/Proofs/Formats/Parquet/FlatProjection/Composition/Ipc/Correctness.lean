module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Defs
import all Silmaril.Formats.Parquet.FlatProjection.Defs
import Silmaril.Formats.Parquet.FlatProjection.Composition.Thms
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc

open Silmaril.Formats Silmaril.Formats.Parquet
open FlatProjection FlatProjection.Composition FlatProjection.Composition.Ipc
open Arrow.MixedFlat

private theorem observeSlots_cells (column : Arrow.MixedFlat.Column) :
    observeSlots (match column with
      | .primitive values => .int32 values
      | .binaryView values => .binaryView (values.map (Option.map KBytes.toList))
      | .utf8View values => .utf8View values) =
      (Arrow.MixedFlat.Events.cells column).map (Option.map observeCell) := by
  cases column <;> simp [observeSlots, Arrow.MixedFlat.Events.cells, observeCell, List.map_map,
    Function.comp_def, Option.map_map]

private theorem observeColumns_eq (columns : List (Field × Arrow.MixedFlat.Column)) :
    Writer.observeColumns columns = some (columns.map fun (field, column) =>
      (field, match column with
        | .primitive values => .int32 values
        | .binaryView values => .binaryView (values.map (Option.map KBytes.toList))
        | .utf8View values => .utf8View values)) := by
  induction columns with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨field, column⟩ := pair
    simp [Writer.observeColumns, Bind.bind, Option.bind, pure] at ih
    unfold Writer.observeColumns
    cases column <;> simp [List.mapM_cons, ih, Bind.bind, Option.bind, pure]

private theorem observeBatch_eq {fields : List Field} {record : Stream.Batch}
    {event : Arrow.MixedFlat.Events.Batch (Arrow.MixedFlat.Events.schema fields)}
    (agrees : Arrow.MixedFlat.Events.Agrees (Arrow.MixedFlat.Events.schema fields) record.observed event) :
    observeSourceBatch (StreamWriter.observeBatch record) = some (observeBatch event) := by
  obtain ⟨rows, width, columns⟩ := agrees
  simp only [observeSourceBatch, StreamWriter.observeBatch, observeColumns_eq, Option.map_some,
    observeBatch, rows, Option.some.injEq, Prod.mk.injEq, true_and, List.map_map, Function.comp_def,
    observeSlots_cells]
  apply List.ext_getElem
  · simpa using width
  · intro i hi hj
    have inside : i < (Arrow.MixedFlat.Events.schema fields).width := by simpa using hj
    have h := columns ⟨i, inside⟩
    rw [List.getElem?_eq_getElem (show i < record.observed.columns.length by simpa using hi)] at h
    have values := congrArg Prod.snd (Option.some.inj h)
    simpa using congrArg (List.map (Option.map observeCell)) values

private theorem observeBatches_eq {fields : List Field} {records : List Stream.Batch}
    {events : List (Arrow.MixedFlat.Events.Batch (Arrow.MixedFlat.Events.schema fields))}
    (agrees : List.Forall₂
      (fun record => Arrow.MixedFlat.Events.Agrees (Arrow.MixedFlat.Events.schema fields) record.observed) records events) :
    (records.map StreamWriter.observeBatch).mapM observeSourceBatch = some (events.map observeBatch) := by
  induction agrees with
  | nil => rfl
  | cons head _ ih =>
    simp [List.mapM_cons, observeBatch_eq head, ih, Bind.bind, Option.bind, pure]

theorem read_emitted {limits : Arrow.MixedFlat.Limits} {fields : List Field}
    {batches : List OrderedWriter.BatchInput} {wire : KBytes}
    (emitted : OrderedWriter.emit limits fields batches = .ok wire) :
    readEvents limits wire = observeSource ⟨fields, batches.map OrderedWriter.BatchInput.observe⟩ ∧
      ∃ (start : Nat) (trace : Stream.Events.Trace (Arrow.MixedFlat.Events.schema fields)),
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (fields, start) ∧
        Stream.Events.readAll limits wire = .ok ⟨Arrow.MixedFlat.Events.schema fields, trace⟩ ∧
        trace.termination = .eos := by
  obtain ⟨decoded, read, ordered, values, wf, start, framed, _⟩ := OrderedWriter.emit_readback emitted
  subst fields
  have admitted : Stream.Events.admit limits wire = .ok (decoded.fields, start) := by
    simp [Stream.Events.admit, wf, framed, Except.mapError]
  have exactRead := Stream.Events.readAll_exact limits wire
  rw [admitted] at exactRead
  obtain ⟨trace, pulled, done⟩ := exactRead
  rw [read] at done
  obtain ⟨_, eos, agrees⟩ := done
  refine ⟨?_, start, trace, framed, pulled, eos⟩
  simp [readEvents, complete, pulled, eos, Arrow.MixedFlat.Events.schema, observeSource, ← values,
    observeBatches_eq agrees]

theorem read_emittedWith {limits : Arrow.MixedFlat.Limits} {fields : List Field}
    {batches : List OrderedWriter.BatchInput} {admit : List Field → Bool} {wire : KBytes}
    (emitted : OrderedWriter.emitWith limits fields batches admit = .ok wire) :
    readEvents limits wire = observeSource ⟨fields, batches.map OrderedWriter.BatchInput.observe⟩ := by
  obtain ⟨decoded, trace, _, _, values, pulled, eos, agrees⟩ := OrderedWriter.emitWith_pull_exact emitted
  simp [readEvents, complete, pulled, eos, Arrow.MixedFlat.Events.schema, observeSource, ← values,
    observeBatches_eq agrees]

private theorem project_observeBatch {positions : List Nat} {wide direct : StreamWriter.BatchObservation}
    (projected : projectBatch positions wide = some direct) :
    ∃ wideEvent directEvent, observeSourceBatch wide = some wideEvent ∧
      observeSourceBatch direct = some directEvent ∧
      projectEventBatch positions wideEvent = some directEvent := by
  obtain ⟨rows, columns⟩ := wide
  cases columns with
  | none => simp [projectBatch, Bind.bind, Option.bind] at projected
  | some columns =>
    cases selected : select positions columns with
    | none => simp [projectBatch, selected, Bind.bind, Option.bind] at projected
    | some chosen =>
      have same : (rows, some chosen) = direct := by
        simpa [projectBatch, selected, Bind.bind, Option.bind, pure] using projected
      subst direct
      refine ⟨_, _, rfl, rfl, ?_⟩
      simp [projectEventBatch, select_map, selected]

private theorem project_observeBatches {positions : List Nat} {wide direct : List StreamWriter.BatchObservation}
    (projected : wide.mapM (projectBatch positions) = some direct) :
    ∃ wideEvents directEvents, wide.mapM observeSourceBatch = some wideEvents ∧
      direct.mapM observeSourceBatch = some directEvents ∧
      wideEvents.mapM (projectEventBatch positions) =
        some directEvents := by
  induction wide generalizing direct with
  | nil =>
    have empty : [] = direct := by simpa using projected
    subst direct
    exact ⟨[], [], rfl, rfl, rfl⟩
  | cons head tail ih =>
    simp only [List.mapM_cons] at projected
    cases picked : projectBatch positions head with
    | none => simp [picked, Bind.bind, Option.bind] at projected
    | some headDirect =>
      cases rest : tail.mapM (projectBatch positions) with
      | none => simp [picked, rest, Bind.bind, Option.bind] at projected
      | some tailDirect =>
        have same : headDirect :: tailDirect = direct := by
          simpa [picked, rest, Bind.bind, Option.bind, pure] using projected
        subst direct
        obtain ⟨first, second, readFirst, readSecond, headEq⟩ := project_observeBatch picked
        obtain ⟨wideRest, directRest, readWide, readDirect, tailEq⟩ := ih rest
        refine ⟨first :: wideRest, second :: directRest, ?_, ?_, ?_⟩
        all_goals simp [List.mapM_cons, readFirst, readSecond, readWide, readDirect, headEq, tailEq,
          Bind.bind, Option.bind, pure]

theorem project_source {positions : List Nat} {wide direct : Observation}
    (projected : project positions wide = some direct) :
    ∃ wideEvents directEvents, observeSource wide = some wideEvents ∧
      observeSource direct = some directEvents ∧ projectEvents positions wideEvents = some directEvents := by
  cases fields : select positions wide.fields with
  | none => simp [project, fields, Bind.bind, Option.bind] at projected
  | some selected =>
    cases batches : wide.batches.mapM (projectBatch positions) with
    | none => simp [project, fields, batches, Bind.bind, Option.bind] at projected
    | some selectedBatches =>
      have same : (⟨selected, selectedBatches⟩ : Observation) = direct := by
        simpa [project, fields, batches, Bind.bind, Option.bind, pure] using projected
      subst direct
      obtain ⟨wideEvents, directEvents, readWide, readDirect, selectedEvents⟩ := project_observeBatches batches
      refine ⟨⟨wide.fields, wideEvents⟩, ⟨selected, directEvents⟩, ?_, ?_, ?_⟩
      · simp [observeSource, readWide]
      · simp [observeSource, readDirect]
      · simp [projectEvents, fields, selectedEvents, Bind.bind, Option.bind, pure]

private theorem batch_rows {positions : List Nat} {wide direct : List BatchObservation}
    (projected : wide.mapM (projectEventBatch positions) =
      some direct) :
    direct.map Prod.fst = wide.map Prod.fst := by
  induction wide generalizing direct with
  | nil =>
    have empty : [] = direct := by simpa using projected
    simp [← empty]
  | cons batch tail ih =>
    obtain ⟨rows, columns⟩ := batch
    cases chosen : select positions columns with
    | none => simp [List.mapM_cons, projectEventBatch, chosen, Bind.bind, Option.bind] at projected
    | some values =>
      cases rest : tail.mapM (projectEventBatch positions) with
      | none => simp [List.mapM_cons, projectEventBatch, chosen, rest, Bind.bind, Option.bind] at projected
      | some more =>
        have same : (rows, values) :: more = direct := by
          simpa [List.mapM_cons, projectEventBatch, chosen, rest, Bind.bind, Option.bind, pure] using projected
        subst direct
        simp [ih rest]

theorem projectEvents_rowCounts {positions : List Nat} {wide direct : EventObservation}
    (projected : projectEvents positions wide = some direct) :
    direct.batches.map Prod.fst = wide.batches.map Prod.fst := by
  cases fields : select positions wide.fields with
  | none => simp [projectEvents, fields, Bind.bind, Option.bind] at projected
  | some chosen =>
    cases batches : wide.batches.mapM (projectEventBatch positions) with
    | none =>
      simp [projectEvents, fields, batches, Bind.bind, Option.bind] at projected
    | some more =>
      have same : (⟨chosen, more⟩ : EventObservation) = direct := by
        simpa [projectEvents, fields, batches, Bind.bind, Option.bind, pure]
          using projected
      subst direct
      exact batch_rows batches

theorem convert_compose_events {originalLimits directLimits : FlatProjection.Limits}
    {wideIpc directIpc : Arrow.MixedFlat.Limits} {input : Bytes} {ordinals positions composed : List Nat}
    {original : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (originalRead : original.readAll originalLimits = .ok wide)
    (fileBytes : input.length ≤ directLimits.column.maxFileBytes)
    (rows : original.snapshot.metadata.numRows.toNat ≤ directLimits.maxFileRows)
    (fields : composed.length ≤ directLimits.maxFields) :
    ∃ direct narrow, openFile directLimits input composed = .ok direct ∧
      direct.readAll directLimits = .ok narrow ∧
      ∀ {wideWire directWire : KBytes},
        OrderedWriter.emit wideIpc original.fields wide = .ok wideWire →
        OrderedWriter.emit directIpc direct.fields narrow = .ok directWire →
        convert originalLimits wideIpc input ordinals = .ok wideWire ∧
        convert directLimits directIpc input composed = .ok directWire ∧
        ∃ wideEvents directEvents,
          readEvents wideIpc wideWire = some wideEvents ∧
          readEvents directIpc directWire = some directEvents ∧
          projectEvents positions wideEvents = some directEvents := by
  obtain ⟨direct, narrow, directOpen, directRead, projected⟩ :=
    project_compose_of_caps same composition originalOpen originalRead fileBytes rows fields
  obtain ⟨wideEvents, directEvents, wideObserved, directObserved, eventProjection⟩ :=
    project_source projected
  refine ⟨direct, narrow, directOpen, directRead, ?_⟩
  intro wideWire directWire wideEmit directEmit
  refine ⟨?_, ?_, wideEvents, directEvents, ?_, ?_, eventProjection⟩
  · simp [convert, originalOpen, originalRead, wideEmit, Except.mapError, Bind.bind, Except.bind]
  · simp [convert, directOpen, directRead, directEmit, Except.mapError, Bind.bind, Except.bind]
  · exact (read_emitted wideEmit).1.trans wideObserved
  · exact (read_emitted directEmit).1.trans directObserved

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc
