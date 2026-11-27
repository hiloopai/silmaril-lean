module

public import Silmaril.Formats.Parquet.FlatProjection.Defs
import all Silmaril.Formats.Parquet.FlatProjection.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection

open Silmaril.Formats Silmaril.Formats.Parquet FlatProjection
open Arrow.MixedFlat

private theorem mapM_exact {α β ε : Type} {read : α → Except ε β}
    {R : α → β → Prop} (step : ∀ a b, read a = .ok b → R a b)
    {inputs : List α} {outputs : List β} (done : inputs.mapM read = .ok outputs) :
    List.Forall₂ R inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases done; exact .nil
  | cons input rest ih =>
    cases head : read input with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at done
    | ok output =>
      cases tail : rest.mapM read with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at done
      | ok later =>
        simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure] at done
        subst outputs
        exact .cons (step input output head) (ih tail)

private theorem indexed_mapM_exact {α β ε : Type} {read : α × Nat → Except ε β}
    {R : α → β → Prop} (step : ∀ a position b, read (a, position) = .ok b → R a b)
    {inputs : List α} {outputs : List β} {start : Nat}
    (done : (inputs.zipIdx start).mapM read = .ok outputs) :
    List.Forall₂ R inputs outputs := by
  induction inputs generalizing start outputs with
  | nil => cases done; exact .nil
  | cons input rest ih =>
    cases head : read (input, start) with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at done
    | ok output =>
      cases tail : (rest.zipIdx (start + 1)).mapM read with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at done
      | ok later =>
        simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure] at done
        subst outputs
        exact .cons (step input start output head) (ih tail)

private theorem weaken {α β : Type} {R S : α → β → Prop} {xs : List α} {ys : List β}
    (step : ∀ {x y}, R x y → S x y) (related : List.Forall₂ R xs ys) : List.Forall₂ S xs ys := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (step head) ih

theorem bind_ordinal {snapshot : Snapshot.Checked} {ordinal : Nat} {bound : Bound snapshot}
    (boundOk : bindOrdinal snapshot ordinal = .ok bound) : bound.ordinal = ordinal := by
  cases selected : bindLeaf snapshot ordinal with
  | error cause => simp [bindOrdinal, selected, Bind.bind, Except.bind] at boundOk
  | ok actual =>
    by_cases exactOrdinal : actual.ordinal = ordinal
    · simp [bindOrdinal, selected, exactOrdinal, Bind.bind, Except.bind] at boundOk
      exact boundOk ▸ exactOrdinal
    · simp [bindOrdinal, selected, exactOrdinal, Bind.bind, Except.bind] at boundOk

theorem bound_leaf {snapshot : Snapshot.Checked} (bound : Bound snapshot) :
    snapshot.metadata.schema[bound.ordinal + 1]? = some bound.binding.leaf ∧
    bound.field.name = bound.binding.leaf.name ∧
    bound.field.nullable = decide (bound.binding.leaf.repetition = some .optional) ∧
    bound.binding.leaf.physicalType = some bound.selection.physical := by
  refine ⟨bound.binding.leafAt, ?_, ?_, bound.binding.leafPhysical⟩
  · cases bound with
    | int32 name layout binding => exact binding.leafName.symm
    | byteArray name layout binding => exact binding.leafName.symm
  · cases bound with
    | int32 name layout binding =>
      change decide (layout.repetition = .optional) = decide (binding.leaf.repetition = some .optional)
      rw [binding.leafRepetition]
      cases layout.repetition <;> simp
    | byteArray name layout binding =>
      change decide (layout.repetition = .optional) = decide (binding.leaf.repetition = some .optional)
      rw [binding.leafRepetition]
      cases layout.repetition <;> simp

theorem bindProjection_lookup {snapshot : Snapshot.Checked}
    {ordinals : List Nat} {columns : List (Bound snapshot)}
    (bound : bindProjection snapshot ordinals = .ok columns) :
    List.Forall₂ (fun ordinal column => bindOrdinal snapshot ordinal = .ok column) ordinals columns := by
  apply indexed_mapM_exact (fun ordinal position column h => ?_) bound
  change (bindOrdinal snapshot ordinal).mapError (SourceError.bind position ordinal) = .ok column at h
  cases resolved : bindOrdinal snapshot ordinal with
  | error cause => simp [resolved, Except.mapError] at h
  | ok actual =>
    simp [resolved, Except.mapError] at h
    exact h ▸ rfl

private theorem bindProjection_ordinals {snapshot : Snapshot.Checked}
    {ordinals : List Nat} {columns : List (Bound snapshot)}
    (bound : bindProjection snapshot ordinals = .ok columns) :
    columns.map Bound.ordinal = ordinals := by
  have each := weaken (fun h => bind_ordinal h) (bindProjection_lookup bound)
  clear bound
  induction each with
  | nil => rfl
  | cons head _ ih => simp [head, ih]

theorem open_bindings {limits : FlatProjection.Limits} {input : Bytes} {ordinals : List Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.column.snapshot input = .ok checked.snapshot ∧
    bindProjection checked.snapshot ordinals = .ok checked.columns ∧
    input.length ≤ limits.column.maxFileBytes ∧
    checked.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows ∧ ordinals.length ≤ limits.maxFields := by
  by_cases bytes : limits.column.maxFileBytes < input.length
  · simp [openFile, bytes, Bind.bind, Except.bind, throw] at opened
  by_cases fields : limits.maxFields < ordinals.length
  · simp [openFile, bytes, fields, Bind.bind, Except.bind, throw] at opened
  cases snapshotResult : Snapshot.check (Failure := Unit) limits.column.snapshot input with
  | error cause => simp [openFile, bytes, fields, snapshotResult, Except.mapError, Bind.bind, Except.bind] at opened
  | ok snapshot =>
    by_cases rows : limits.maxFileRows < snapshot.metadata.numRows.toNat
    · simp [openFile, bytes, fields, snapshotResult, rows, Except.mapError, Bind.bind, Except.bind, throw] at opened
    cases bound : bindProjection snapshot ordinals with
    | error cause => simp [openFile, bytes, fields, snapshotResult, rows, bound, Except.mapError, Bind.bind, Except.bind]
        at opened
    | ok columns =>
      simp [openFile, bytes, fields, snapshotResult, rows, bound, Except.mapError, Bind.bind, Except.bind,
        pure, Except.pure] at opened
      subst checked
      exact ⟨rfl, bound, Nat.le_of_not_gt bytes,
        Nat.le_of_not_gt rows, Nat.le_of_not_gt fields⟩

theorem open_exact {limits : FlatProjection.Limits} {input : Bytes} {ordinals : List Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.column.snapshot input = .ok checked.snapshot ∧
    checked.columns.map Bound.ordinal = ordinals ∧
    input.length ≤ limits.column.maxFileBytes ∧
    checked.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows ∧ ordinals.length ≤ limits.maxFields := by
  obtain ⟨snapshot, bindings, caps⟩ := open_bindings opened
  exact ⟨snapshot, bindProjection_ordinals bindings, caps⟩

theorem bound_read_congr {snapshot : Snapshot.Checked} {left right : FlatProjection.Limits}
    (same : left.column = right.column) (bound : Bound snapshot) (index : Nat) :
    bound.read left index = bound.read right index := by
  cases bound <;> simp [Bound.read, same]

theorem packBinary_exact (slots : List (Option Bytes)) :
    (packBinary slots).map (Option.map KBytes.toList) = slots.map (Option.map Bytes.toList) := by
  simp [packBinary, List.map_map, Option.map_map, Function.comp_def, Arrow.Writer.emitBytes_bytes]

theorem bound_read_exact {snapshot : Snapshot.Checked} {limits : FlatProjection.Limits} {index : Nat}
    {bound : Bound snapshot} {group : Footer.RowGroup} {column : OrderedWriter.Column}
    (original : snapshot.groupAt index = some group) (read : bound.read limits index = .ok column) :
    bound.Wire limits index group column ∧ column.field = bound.field ∧ column.length = group.numRows.toNat := by
  cases bound with
  | int32 name layout binding =>
    cases decoded : FlatColumn.readColumn binding limits.column.column Plain.ByteArray.File.policy
        (Int32ByteArrayGroup.decodeInt32 limits.column layout) index with
    | error cause => simp [Bound.read, decoded, Except.map, Except.mapError] at read
    | ok slots =>
      simp [Bound.read, decoded, Except.map, Except.mapError] at read
      subst column
      obtain ⟨actual, wire⟩ := FlatColumn.readColumn_wire decoded
      have actualWire := wire
      obtain ⟨_, _, _, _, found, _, _, _, _, _, _, _, _, _, _, count⟩ := actualWire
      rw [original] at found
      cases found
      exact ⟨⟨slots, rfl, wire⟩, rfl, count⟩
  | byteArray name layout binding =>
    cases decoded : FlatColumn.readColumn binding limits.column.column Plain.ByteArray.File.policy
        (Int32ByteArrayGroup.decodeByteArray limits.column layout) index with
    | error cause => simp [Bound.read, decoded, Except.map, Except.mapError] at read
    | ok slots =>
      simp [Bound.read, decoded, Except.map, Except.mapError] at read
      subst column
      obtain ⟨actual, wire⟩ := FlatColumn.readColumn_wire decoded
      have actualWire := wire
      obtain ⟨_, _, _, _, found, _, _, _, _, _, _, _, _, _, _, count⟩ := actualWire
      rw [original] at found
      cases found
      exact ⟨⟨slots, rfl, wire⟩, rfl, by simpa [OrderedWriter.Column.length, packBinary] using count⟩

theorem group_lookup {limits : FlatProjection.Limits} {index : Nat} {checked : Checked} {batch : OrderedWriter.BatchInput}
    (read : checked.readGroup limits index = .ok batch) :
    ∃ group, checked.snapshot.groupAt index = some group ∧ batch.rowCount = group.numRows.toNat ∧
      List.Forall₂ (fun bound column => bound.read limits index = .ok column)
        checked.columns batch.columns := by
  cases found : checked.snapshot.groupAt index with
  | none => simp [Checked.readGroup, found, throw] at read
  | some group =>
    by_cases rows : limits.column.column.maxRows < group.numRows.toNat
    · simp [Checked.readGroup, found, rows, Bind.bind, Except.bind, throw] at read
    cases columns : readColumns limits index checked.columns with
    | error cause => simp [Checked.readGroup, found, rows, columns, Bind.bind, Except.bind] at read
    | ok ordered =>
      simp [Checked.readGroup, found, rows, columns, Bind.bind, Except.bind, pure, Except.pure] at read
      subst batch
      refine ⟨group, rfl, rfl, indexed_mapM_exact (fun bound position column h => ?_) columns⟩
      change (bound.read limits index).mapError (SourceError.read index position bound.ordinal) = .ok column at h
      cases raw : bound.read limits index with
      | error cause => simp [raw, Except.mapError] at h
      | ok value =>
        simp [raw, Except.mapError] at h
        exact h ▸ rfl

theorem group_exact {limits : FlatProjection.Limits} {index : Nat} {checked : Checked} {batch : OrderedWriter.BatchInput}
    (read : checked.readGroup limits index = .ok batch) :
    ∃ group, checked.snapshot.groupAt index = some group ∧ batch.rowCount = group.numRows.toNat ∧
      batch.fields = checked.fields ∧ List.Forall₂
        (fun bound column => bound.Wire limits index group column ∧ column.length = batch.rowCount)
        checked.columns batch.columns := by
  obtain ⟨group, found, count, lookup⟩ := group_lookup read
  have each := weaken (fun h => bound_read_exact found h) lookup
  refine ⟨group, found, count, ?_, weaken (fun h => ⟨h.1, h.2.2.trans count.symm⟩) each⟩
  have exactFields {bindings : List (Bound checked.snapshot)} {values : List OrderedWriter.Column}
      (same : List.Forall₂ (fun bound column => column.field = bound.field) bindings values) :
      values.map OrderedWriter.Column.field = bindings.map Bound.field := by
    induction same with
    | nil => rfl
    | cons head _ ih => simp [head, ih]
  exact exactFields (weaken (fun h => h.2.1) each)

theorem readAll_indexed {limits : FlatProjection.Limits} {checked : Checked} {batches : List OrderedWriter.BatchInput}
    (read : checked.readAll limits = .ok batches) :
    List.Forall₂ (fun index batch => checked.readGroup limits index = .ok batch) checked.indices batches :=
  mapM_exact (fun _ _ h => h) read

theorem convert_readback {parquet : FlatProjection.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals : List Nat} {wire : KBytes} (written : convert parquet ipc input ordinals = .ok wire) :
    ∃ (checked : Checked) (batches : List OrderedWriter.BatchInput) (decoded : Stream.Observed),
      openFile parquet input ordinals = .ok checked ∧
      checked.columns.map Bound.ordinal = ordinals ∧ checked.readAll parquet = .ok batches ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = checked.fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map OrderedWriter.BatchInput.observe ∧
      decoded.batches.map (·.observed.rowCount) = batches.map (·.rowCount) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : openFile parquet input ordinals with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    cases all : checked.readAll parquet with
    | error cause => simp [convert, opened, all, Except.mapError, Bind.bind, Except.bind] at written
    | ok batches =>
      cases emitted : OrderedWriter.emit ipc checked.fields batches with
      | error cause => simp [convert, opened, all, emitted, Except.mapError, Bind.bind, Except.bind] at written
      | ok output =>
        simp [convert, opened, all, emitted, Except.mapError, Bind.bind, Except.bind] at written
        subst wire
        obtain ⟨decoded, read, fields, observations, framing⟩ := OrderedWriter.emit_readback emitted
        have counts := congrArg (List.map (fun item : StreamWriter.BatchObservation => item.1)) observations
        refine ⟨checked, batches, decoded, rfl, (open_exact opened).2.1, all, read, fields, observations, ?_, framing⟩
        simpa only [List.map_map, Function.comp_def, StreamWriter.observeBatch, OrderedWriter.BatchInput.observe]
          using counts

theorem convert_first_error {parquet : FlatProjection.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals : List Nat} {checked : Checked} {before after : List Nat} {index : Nat}
    {preceding : List OrderedWriter.BatchInput} {cause : SourceError}
    (opened : openFile parquet input ordinals = .ok checked)
    (split : checked.indices = before ++ index :: after)
    (earlier : before.mapM (fun i => checked.readGroup parquet i) = .ok preceding)
    (failed : checked.readGroup parquet index = .error cause) :
    convert parquet ipc input ordinals = .error (.source cause) := by
  simp [convert, opened, Checked.readAll, split, List.mapM_append, List.mapM_cons, earlier, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.FlatProjection
