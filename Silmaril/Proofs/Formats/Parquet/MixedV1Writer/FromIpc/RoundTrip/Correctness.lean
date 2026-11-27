module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Thms
import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Int32ByteArrayGroup
open MixedV1Writer.FromIpc
open Silmaril.Formats.Relational.NamedTable

private theorem mapM_range_exact {α ε : Type} (rows : List α) (read : Nat → Except ε α)
    (atIndex : ∀ i : Fin rows.length, read i.val = .ok (rows.get i)) :
    (List.range rows.length).mapM read = .ok rows := by
  induction rows generalizing read with
  | nil => rfl
  | cons row rest ih =>
    have head : read 0 = .ok row := atIndex ⟨0, by simp⟩
    have tail := ih (read ∘ Nat.succ) (fun i => atIndex i.succ)
    simp [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, head, tail, Bind.bind, Except.bind,
      pure, Except.pure]

private theorem descriptor_exact (schema : MixedIpc.Descriptor) (ordered : schema.viewFirst = false) :
    MixedIpc.FromParquet.descriptor (field schema.integer) (field schema.binary) = schema := by
  rcases schema with ⟨first, ⟨integer, ni⟩, ⟨binary, nb⟩⟩
  change first = false at ordered
  subst first
  cases ni <;> cases nb <;> rfl

private theorem batches_exact (batches : List (List MixedIpc.Pair)) :
    (batches.map (List.map toRow)).map MixedIpc.FromParquet.groupPairs = batches := by
  have row (pair : MixedIpc.Pair) :
      ((toRow pair).1, (toRow pair).2.map Bytes.toList) = pair := by
    rcases pair with ⟨integer, binary⟩
    cases binary <;> simp [toRow]
  simp [MixedIpc.FromParquet.groupPairs, List.map_map, Function.comp_def, row]

theorem read_roundTrip {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (backward : ToIpc.convert reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed := by
  obtain ⟨actual, projection, reread, order, opened, count, indexed⟩ := convert_indexed forward
  rw [original] at reread
  cases reread
  obtain ⟨checked, groups, reverseOpen, reads, returnedOk⟩ :=
    MixedIpc.FromParquet.convert_observation backward carrier
  have sameProjection := File.openFile_projection reverseOpen
  rw [groupLimits, opened] at sameProjection
  have project := (Except.ok.inj sameProjection).symm
  have ordered := mapM_range_exact (observed.batches.map (List.map toRow))
    (projection.readGroup sink.writer.readback) (fun i => by
      let index : Fin observed.batches.length := ⟨i.val, by simpa using i.isLt⟩
      simpa [index] using (indexed index).1)
  have readsExact : groups = observed.batches.map (List.map toRow) := by
    rw [project, count, groupLimits] at reads
    simp only [List.length_map] at ordered
    exact (Except.ok.inj (reads.symm.trans ordered))
  rw [readsExact] at returnedOk
  cases observed with
  | mk descriptor batches =>
    simpa only [MixedIpc.FromParquet.observation, descriptor_exact descriptor order, batches_exact] using returnedOk

private def arrowOrder (descriptor : MixedIpc.Descriptor) : Arrow.MixedFlat.Writer.Order :=
  if descriptor.viewFirst then .viewFirst else .intFirst

private theorem binding_ordinal {root first second : Footer.SchemaElement} {ordinal : Nat}
    {leaf : Footer.SchemaElement} (atLeaf : [root, first, second][ordinal + 1]? = some leaf) :
    (ordinal = 0 ∧ leaf = first) ∨ (ordinal = 1 ∧ leaf = second) := by
  rcases ordinal with _ | _ | n
  · simp_all
  · simp_all
  · simp at atLeaf

private theorem selectedOrder_exact {d : MixedIpc.Descriptor}
    (projection : Checked (field d.integer) (field d.binary))
    (schema : projection.snapshot.metadata.schema =
      FlatInt32Writer.Compact.schemaRoot 2 ::
        (physicalOrder d).columns
          (MixedV1Writer.columnIndex (field d.integer) ⟨0, 0⟩).schema
          (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field d.binary) ⟨0, 0⟩))) :
    ToIpc.selectedOrder projection = arrowOrder d := by
  have integers := projection.int32Binding.leafAt
  have binary := projection.byteArrayBinding.leafAt
  rw [schema] at integers binary
  have integerType := projection.int32Binding.leafPhysical
  have binaryType := projection.byteArrayBinding.leafPhysical
  cases order : d.viewFirst <;>
    simp only [physicalOrder, order, Bool.false_eq_true, ite_false, ite_true,
      MixedV1Writer.Order.columns, MixedV1Writer.Order.arrange] at integers binary
  all_goals
    rcases binding_ordinal integers with ⟨intOrdinal, intLeaf⟩ | ⟨intOrdinal, intLeaf⟩ <;>
    rcases binding_ordinal binary with ⟨byteOrdinal, byteLeaf⟩ | ⟨byteOrdinal, byteLeaf⟩ <;>
      simp_all [ToIpc.selectedOrder, arrowOrder, MixedV1Writer.byteSchema,
        FlatInt32Writer.Compact.ColumnIndex.schema]

private theorem fields_exact (d : MixedIpc.Descriptor) :
    (ToIpc.writerSchemaOrdered (arrowOrder d)
      (Prepare.Schema.ofSelection (field d.integer) (field d.binary))).fields = d.fields := by
  rcases d with ⟨order, ⟨integer, ni⟩, ⟨binary, nb⟩⟩
  cases order <;> cases ni <;> cases nb <;> rfl

private theorem group_exact (d : MixedIpc.Descriptor) (rows : List Row) :
    ToIpc.groupObservationOrdered (arrowOrder d) (field d.integer) (field d.binary) rows =
      MixedIpc.Export.observePairs d (MixedIpc.FromParquet.groupPairs rows) := by
  rcases d with ⟨order, ⟨integer, ni⟩, ⟨binary, nb⟩⟩
  cases order <;> cases ni <;> cases nb <;> simp [arrowOrder, field, ToIpc.groupObservationOrdered,
    Arrow.MixedFlat.Writer.Order.pair, MixedIpc.Export.observePairs, MixedIpc.Descriptor.intField,
    MixedIpc.Descriptor.viewField, MixedIpc.FromParquet.groupPairs]

theorem read_of_indexed {returned : MixedIpc.Limits} {reverse : File.Limits}
    {bytes : Bytes} {output : KBytes} {descriptor : MixedIpc.Descriptor}
    {batches : List (List MixedIpc.Pair)} {span : Footer.Span} {metadata : Footer.Metadata}
    {projection : Checked (field descriptor.integer) (field descriptor.binary)}
    (opened : Int32ByteArrayGroup.openFile reverse.group bytes
      (field descriptor.integer) (field descriptor.binary) = .ok projection)
    (count : projection.snapshot.groupCount = batches.length)
    (indexed : ∀ i : Fin batches.length,
      projection.readGroup reverse.group i.val = .ok ((batches.get i).map toRow))
    (footer : Footer.readFooter reverse.group.snapshot.footer bytes = .ok (span, metadata))
    (schema : metadata.schema = FlatInt32Writer.Compact.schemaRoot 2 ::
      (physicalOrder descriptor).columns
        (MixedV1Writer.columnIndex (field descriptor.integer) ⟨0, 0⟩).schema
        (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field descriptor.binary) ⟨0, 0⟩)))
    (backward : ToIpc.convertOrdered reverse returned.mixed bytes
      (field descriptor.integer) (field descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok ⟨descriptor, batches⟩ := by
  obtain ⟨checked, groups, decoded, reverseOpen, reads, returnedOk, fields, observations, _⟩ :=
    ToIpc.convertOrdered_readback backward
  have sameProjection := File.openFile_projection reverseOpen
  rw [opened] at sameProjection
  have project := (Except.ok.inj sameProjection).symm
  have ordered := mapM_range_exact (batches.map (List.map toRow))
    (projection.readGroup reverse.group) (fun i => by
      let index : Fin batches.length := ⟨i.val, by simpa using i.isLt⟩
      simpa [index] using indexed index)
  have readsExact : groups = batches.map (List.map toRow) := by
    rw [project, count] at reads
    simp only [List.length_map] at ordered
    exact Except.ok.inj (reads.symm.trans ordered)
  have snapshot := (File.openFile_snapshot reverseOpen).1
  have checkedFooter := Snapshot.check_metadata snapshot footer
  have order := selectedOrder_exact checked.projection ((congrArg Footer.Metadata.schema checkedFooter).trans schema)
  rw [order, fields_exact] at fields
  rw [order, readsExact] at observations
  have exactBatches : decoded.batches.map Arrow.MixedFlat.StreamWriter.observeBatch =
        batches.map (MixedIpc.Export.observePairs descriptor) := by
    rw [observations]
    calc
      _ = (batches.map (List.map toRow)).map
          (MixedIpc.Export.observePairs descriptor ∘ MixedIpc.FromParquet.groupPairs) :=
        congrArg (fun f => (batches.map (List.map toRow)).map f) (funext (group_exact _))
      _ = _ := by rw [← List.map_map, batches_exact]
  exact MixedIpc.Export.read_of_observed carrier returnedOk fields exactBatches

theorem read_roundTripOrdered {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convertOrdered source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed ∧
      ∃ parsed : Footer.Metadata,
        Footer.readFooter sink.writer.footer parquet.bytes = .ok (parquet.footer, parsed) ∧
        parsed.schema = FlatInt32Writer.Compact.schemaRoot 2 ::
          (physicalOrder observed.descriptor).columns
            (MixedV1Writer.columnIndex (field observed.descriptor.integer) ⟨0, 0⟩).schema
            (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field observed.descriptor.binary) ⟨0, 0⟩)) ∧
        parsed.rowGroups.map Footer.RowGroup.columns =
          parquet.groups.map (fun pages => (physicalOrder observed.descriptor).columns
            (pages.index.ints.metadata pages.index.rows)
            (MixedV1Writer.byteChunk pages.index.octets pages.index.rows)) := by
  obtain ⟨actual, plan, reread, planned, emitted⟩ := convertOrdered_ok_iff.mp forward
  rw [original] at reread
  cases reread
  obtain ⟨_, intLabel, byteLabel, _⟩ := prepareOrdered_exact planned
  obtain ⟨_, _, _, _, verified, _⟩ := MixedV1Writer.Multi.emitOrdered_checked emitted
  obtain ⟨_, _, _, _, footer, _⟩ := verified
  let metadata := MixedV1Writer.Multi.metadataOrdered (physicalOrder observed.descriptor) plan parquet.groups
  have schema : metadata.schema = FlatInt32Writer.Compact.schemaRoot 2 ::
      (physicalOrder observed.descriptor).columns
        (MixedV1Writer.columnIndex (field observed.descriptor.integer) ⟨0, 0⟩).schema
        (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field observed.descriptor.binary) ⟨0, 0⟩)) := by
    simp [metadata, MixedV1Writer.Multi.metadataOrdered, MixedV1Writer.Multi.Input.intIndex,
      MixedV1Writer.Multi.Input.byteIndex, intLabel, byteLabel]
  refine ⟨?_, metadata, footer, schema, ?_⟩
  · obtain ⟨projection, opened, count, indexed⟩ := emit_indexed_of_plan planned emitted
    exact read_of_indexed (by rw [groupLimits]; exact opened) count
      (fun i => by rw [groupLimits]; exact (indexed i).1)
      (by rw [footerLimits]; exact footer) schema backward carrier
  · simp [metadata, MixedV1Writer.Multi.metadataOrdered, List.map_map, Function.comp_def]

theorem read_roundTripSchemaOnly {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {descriptor : MixedIpc.Descriptor}
    (original : MixedIpc.read source input = .ok ⟨descriptor, []⟩)
    (forward : SchemaOnly.convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field descriptor.integer) (field descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok ⟨descriptor, []⟩ ∧ parquet.footer.start = 4 ∧
    Footer.readFooter sink.writer.footer parquet.bytes = .ok (parquet.footer, SchemaOnly.metadata descriptor) := by
  obtain ⟨actual, read, emitted⟩ := SchemaOnly.convert_checked forward
  rw [original] at read
  cases read
  obtain ⟨_, start, footer, projection, opened, zero⟩ := SchemaOnly.emit_checked emitted
  exact ⟨read_of_indexed (batches := []) (by rw [groupLimits]; exact opened) zero
    (fun i => Fin.elim0 i) (by rw [footerLimits]; exact footer) rfl backward carrier, start, footer⟩

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
