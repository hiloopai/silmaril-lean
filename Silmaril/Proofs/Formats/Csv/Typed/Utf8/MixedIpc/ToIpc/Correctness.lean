module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs
import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
open Arrow.MixedFlat

private theorem mapM_exact {α β γ ε : Type} {inputs : List α} {outputs : List β}
    {f : α → Except ε β} {observe : β → γ} {original : α → γ}
    (prepared : inputs.mapM f = .ok outputs)
    (step : ∀ input output, f input = .ok output → observe output = original input) :
    outputs.map observe = inputs.map original := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : [] = outputs := Except.ok.inj prepared
    simp [← empty]
  | cons head rest ih =>
    cases first : f head with
    | error cause => simp [List.mapM_cons, first, Bind.bind, Except.bind] at prepared
    | ok value =>
      cases tail : rest.mapM f with
      | error cause => simp [List.mapM_cons, first, tail, Bind.bind, Except.bind] at prepared
      | ok more =>
        have all : value :: more = outputs := by
          simpa [List.mapM_cons, first, tail, Bind.bind, Except.bind, pure, Except.pure] using prepared
        subst outputs
        simp only [List.map_cons, step head value first, ih tail]

private theorem values_exact {α : Type} {column : Nat} {slots : List (Option Cell)}
    {values : List (Option α)} {extract : Cell → Option α} {put : α → Cell}
    (recover : ∀ c v, extract c = some v → put v = c)
    (prepared : prepareValues column extract slots = .ok values) :
    values.map (Option.map put) = slots := by
  have exactness := mapM_exact (original := id) (observe := Option.map put) prepared
  have step : ∀ (slot : Option Cell) (value : Option α), (match slot with
      | none => Except.ok (none : Option α)
      | some cell => match extract cell with
        | some result => .ok (some result)
        | none => .error (PrepareError.cellKind column)) = .ok value → Option.map put value = id slot := by
    intro slot value h
    cases slot with
    | none => cases h; rfl
    | some cell =>
      cases found : extract cell with
      | none => simp [found] at h
      | some result =>
        simp [found] at h
        subst value
        simp [recover cell result found]
  exact (exactness step).trans (List.map_id slots)

private theorem column_of_values {α : Type} {column : Nat} {slots : List (Option Cell)}
    {extract : Cell → Option α} {put : α → Cell} {build : List (Option α) → OrderedWriter.Column}
    {output : OrderedWriter.Column} (recover : ∀ c v, extract c = some v → put v = c)
    (observes : ∀ values, observeSlots (build values).observe = values.map (Option.map put))
    (prepared : (prepareValues column extract slots).map build = .ok output) :
    observeSlots output.observe = slots := by
  cases result : prepareValues column extract slots with
  | error cause => simp [result, Except.map] at prepared
  | ok values =>
    have same : build values = output := by simpa [result, Except.map] using prepared
    subst output
    rw [observes]
    exact values_exact recover result

private theorem column_exact {column : Nat} {field : Arrow.MixedFlat.Field} {slots : List (Option Cell)}
    {output : OrderedWriter.Column} (prepared : prepareColumn column field slots = .ok output) :
    observeSlots output.observe = slots := by
  obtain ⟨name, nullable, kind⟩ := field
  cases kind with
  | primitive kind =>
    cases kind with
    | int32 =>
      refine column_of_values (put := Cell.primitive ∘ Arrow.Value.int32) ?_ ?_ prepared
      · intro c v found
        cases c with
        | primitive original => cases original <;> simp_all
        | binaryView _ | utf8View _ => contradiction
      · intro values
        simp [observeSlots, OrderedWriter.Column.observe, List.map_map, Option.map_map, Function.comp_def]
    | utf8 =>
      refine column_of_values (put := Cell.primitive ∘ Arrow.Value.utf8) ?_ ?_ prepared
      · intro c v found
        cases c with
        | primitive original => cases original <;> simp_all
        | binaryView _ | utf8View _ => contradiction
      · intro values
        simp [observeSlots, OrderedWriter.Column.observe, Arrow.Writer.ColumnValues.observe,
          List.map_map, Option.map_map, Function.comp_def]
  | view kind =>
    cases kind with
    | binary => simp [prepareColumn] at prepared
    | utf8 =>
      refine column_of_values (put := Cell.utf8View) ?_ ?_ prepared
      · intro c v found
        cases c <;> simp_all
      · intro values
        rfl

theorem prepare_observe {table : Rows.Table} {batch : OrderedWriter.BatchInput}
    (prepared : prepare table = .ok batch) :
    observeSourceBatch batch.observe = some (Rows.observeColumns (AlignedColumns.ofRows table.rows)) := by
  let convertColumn := fun i : Fin table.schema.width =>
    prepareColumn i.val (table.schema.kind i).1 ((AlignedColumns.ofRows table.rows).values i)
  change (do
    let compiled ← (List.finRange table.schema.width).mapM convertColumn
    pure (⟨table.rowCount, compiled⟩ : OrderedWriter.BatchInput)) = .ok batch at prepared
  cases result : (List.finRange table.schema.width).mapM convertColumn with
  | error cause => simp [result, Bind.bind, Except.bind] at prepared
  | ok columns =>
    have same : (⟨table.rowCount, columns⟩ : OrderedWriter.BatchInput) = batch := by
      simpa [result, Bind.bind, Except.bind, pure, Except.pure] using prepared
    subst batch
    have observed := mapM_exact (observe := fun c => observeSlots c.observe)
      (original := (AlignedColumns.ofRows table.rows).values) result (fun _ _ h => column_exact h)
    simp [observeSourceBatch, OrderedWriter.BatchInput.observe, Rows.observeColumns, List.map_map,
      Function.comp_def, observed, List.finRange, List.map_ofFn, AlignedColumns.ofRows, Scan.Observation.rowCount]

theorem emitted_table {limits : Arrow.MixedFlat.Limits} {table : Rows.Table} {batch : OrderedWriter.BatchInput}
    {wire : KBytes} (prepared : prepare table = .ok batch)
    (written : OrderedWriter.emitWith limits (fields table.schema) [batch]
      (fun signature => signature.all Csv.Typed.Utf8.MixedIpc.supported) = .ok wire) :
    readEvents limits wire = some ⟨fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ ∧
      Rows.readRows limits wire = some table := by
  have events := read_emittedWith written
  have normalized := prepare_observe prepared
  have exactEvents :
      readEvents limits wire =
        some ⟨fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ := by
    simpa [observeSource, List.mapM_cons, normalized, Bind.bind, Option.bind, pure] using events
  refine ⟨exactEvents, ?_⟩
  have materialized := Rows.toTable_columns table.schema [AlignedColumns.ofRows table.rows]
  simpa [Rows.readRows, exactEvents, fields, AlignedColumns.toRows_ofRows] using materialized

private theorem decode_schema {csv : Csv.Typed.Utf8.MixedIpc.Limits} {schema : Rows.Schema}
    {input : Csv.Bytes} {table : Rows.Table}
    (read : Csv.Typed.Utf8.MixedIpc.decode csv schema input = .ok table) :
    table.schema = schema := by
  unfold Csv.Typed.Utf8.MixedIpc.decode at read
  simp only [Bind.bind, Except.bind] at read
  repeat' first | split at read | contradiction
  exact congrArg Scan.Observation.schema (Except.ok.inj read).symm

theorem convert_readback {csv : Csv.Typed.Utf8.MixedIpc.Limits} {ipc : Arrow.MixedFlat.Limits}
    {schema : Rows.Schema} {input : Csv.Bytes} {wire : KBytes}
    (converted : convert csv ipc schema input = .ok wire) :
    ∃ table, Csv.Typed.Utf8.MixedIpc.decode csv schema input = .ok table ∧ table.schema = schema ∧
      readEvents ipc wire = some ⟨fields schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ ∧
      Rows.readRows ipc wire = some table := by
  cases read : Csv.Typed.Utf8.MixedIpc.decode csv schema input with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at converted
  | ok table =>
    cases prepared : prepare table with
    | error cause => simp [convert, read, prepared, Except.mapError, Bind.bind, Except.bind] at converted
    | ok batch =>
      cases emitted : OrderedWriter.emitWith ipc (fields table.schema) [batch]
          (fun signature => signature.all Csv.Typed.Utf8.MixedIpc.supported) with
      | error cause => simp [convert, read, prepared, emitted, Except.mapError, Bind.bind, Except.bind] at converted
      | ok output =>
        have exactWire : output = wire := by
          simpa [convert, read, prepared, emitted, Except.mapError, Bind.bind, Except.bind] using converted
        subst wire
        have exactSchema := decode_schema read
        obtain ⟨events, rows⟩ := emitted_table prepared emitted
        exact ⟨table, rfl, exactSchema, by simpa [exactSchema] using events, rows⟩

theorem encoded_readback {csv : Csv.Typed.Utf8.MixedIpc.Limits} {ipc : Arrow.MixedFlat.Limits}
    {table : Rows.Table} {input : Csv.Bytes} {wire : KBytes}
    (encoded : Csv.Typed.Utf8.MixedIpc.encode csv table = .ok input)
    (converted : convert csv ipc table.schema input = .ok wire) :
    Rows.readRows ipc wire = some table := by
  obtain ⟨readTable, read, _, _, rows⟩ := convert_readback converted
  rw [Except.ok.inj (read.symm.trans (Csv.Typed.Utf8.MixedIpc.decode_encode encoded))] at rows
  exact rows

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc
