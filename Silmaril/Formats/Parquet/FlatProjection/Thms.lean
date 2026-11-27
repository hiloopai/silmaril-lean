module

public import Silmaril.Formats.Parquet.FlatProjection.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatProjection

open Arrow.MixedFlat

/-- Every successful binding retains its requested original physical ordinal. -/
theorem bind_ordinal {snapshot : Snapshot.Checked} {ordinal : Nat} {bound : Bound snapshot}
    (boundOk : bindOrdinal snapshot ordinal = .ok bound) : bound.ordinal = ordinal :=
  Proofs.Formats.Parquet.FlatProjection.bind_ordinal
    boundOk

/-- The bound field name and nullability come from the checked leaf. -/
theorem bound_leaf {snapshot : Snapshot.Checked} (bound : Bound snapshot) :
    snapshot.metadata.schema[bound.ordinal + 1]? = some bound.binding.leaf ∧
    bound.field.name = bound.binding.leaf.name ∧
    bound.field.nullable = decide (bound.binding.leaf.repetition = some .optional) ∧
    bound.binding.leaf.physicalType = some bound.selection.physical :=
  Proofs.Formats.Parquet.FlatProjection.bound_leaf
    bound

/-- The ordered lookup result names the precise successful binding for each source ordinal. -/
theorem bindProjection_lookup {snapshot : Snapshot.Checked}
    {ordinals : List Nat} {columns : List (Bound snapshot)}
    (bound : bindProjection snapshot ordinals = .ok columns) :
    List.Forall₂ (fun ordinal column => bindOrdinal snapshot ordinal = .ok column) ordinals columns :=
  Proofs.Formats.Parquet.FlatProjection.bindProjection_lookup bound

/-- A successful open retains the result of binding the original ordinals on its snapshot. -/
theorem open_bindings {limits : FlatProjection.Limits} {input : Bytes} {ordinals : List Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.column.snapshot input = .ok checked.snapshot ∧
    bindProjection checked.snapshot ordinals = .ok checked.columns ∧
    input.length ≤ limits.column.maxFileBytes ∧
    checked.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows ∧ ordinals.length ≤ limits.maxFields :=
  Proofs.Formats.Parquet.FlatProjection.open_bindings opened

/-- A bound column read depends on the source column policy. -/
theorem bound_read_congr {snapshot : Snapshot.Checked} {left right : FlatProjection.Limits}
    (same : left.column = right.column) (bound : Bound snapshot) (index : Nat) :
    bound.read left index = bound.read right index :=
  Proofs.Formats.Parquet.FlatProjection.bound_read_congr same bound index

/-- A complete group retains the exact successful column read at every projected position. -/
theorem group_lookup {limits : FlatProjection.Limits} {index : Nat} {checked : Checked} {batch : OrderedWriter.BatchInput}
    (read : checked.readGroup limits index = .ok batch) :
    ∃ group, checked.snapshot.groupAt index = some group ∧ batch.rowCount = group.numRows.toNat ∧
      List.Forall₂ (fun bound column => bound.read limits index = .ok column)
        checked.columns batch.columns :=
  Proofs.Formats.Parquet.FlatProjection.group_lookup read

/-- Open retains the projection list in order and witnesses all source admission caps. -/
theorem open_exact {limits : FlatProjection.Limits} {input : Bytes} {ordinals : List Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.column.snapshot input = .ok checked.snapshot ∧
    checked.columns.map Bound.ordinal = ordinals ∧
    input.length ≤ limits.column.maxFileBytes ∧
    checked.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows ∧ ordinals.length ≤ limits.maxFields :=
  Proofs.Formats.Parquet.FlatProjection.open_exact
    opened

/-- Packing preserves every nullable opaque octet list exactly. -/
theorem packBinary_exact (slots : List (Option Bytes)) :
    (packBinary slots).map (Option.map KBytes.toList) = slots.map (Option.map Bytes.toList) :=
  Proofs.Formats.Parquet.FlatProjection.packBinary_exact
    slots

/-- A selected column uses its original framed pages and exact typed slots. -/
theorem bound_read_exact {snapshot : Snapshot.Checked} {limits : FlatProjection.Limits} {index : Nat}
    {bound : Bound snapshot} {group : Footer.RowGroup} {column : OrderedWriter.Column}
    (original : snapshot.groupAt index = some group) (read : bound.read limits index = .ok column) :
    bound.Wire limits index group column ∧ column.field = bound.field ∧ column.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.FlatProjection.bound_read_exact
    original read

/-- Each complete batch has the checked group row count and ordered bound columns. -/
theorem group_exact {limits : FlatProjection.Limits} {index : Nat} {checked : Checked} {batch : OrderedWriter.BatchInput}
    (read : checked.readGroup limits index = .ok batch) :
    ∃ group, checked.snapshot.groupAt index = some group ∧ batch.rowCount = group.numRows.toNat ∧
      batch.fields = checked.fields ∧ List.Forall₂
        (fun bound column => bound.Wire limits index group column ∧ column.length = batch.rowCount)
        checked.columns batch.columns :=
  Proofs.Formats.Parquet.FlatProjection.group_exact
    read

/-- Successful exhaustion returns one complete batch per original group ordinal. -/
theorem readAll_indexed {limits : FlatProjection.Limits} {checked : Checked} {batches : List OrderedWriter.BatchInput}
    (read : checked.readAll limits = .ok batches) :
    List.Forall₂ (fun index batch => checked.readGroup limits index = .ok batch) checked.indices batches :=
  Proofs.Formats.Parquet.FlatProjection.readAll_indexed
    read

/-- Native V5 readback recovers the exact fields and all selected batch observations through EOS. -/
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
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Parquet.FlatProjection.convert_readback
    written

/-- A first failed group returns its original indexed source cause and no IPC carrier. -/
theorem convert_first_error {parquet : FlatProjection.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
    {ordinals : List Nat} {checked : Checked} {before after : List Nat} {index : Nat}
    {preceding : List OrderedWriter.BatchInput} {cause : SourceError}
    (opened : openFile parquet input ordinals = .ok checked)
    (split : checked.indices = before ++ index :: after)
    (earlier : before.mapM (fun i => checked.readGroup parquet i) = .ok preceding)
    (failed : checked.readGroup parquet index = .error cause) :
    convert parquet ipc input ordinals = .error (.source cause) :=
  Proofs.Formats.Parquet.FlatProjection.convert_first_error
    opened split earlier failed

end Silmaril.Formats.Parquet.FlatProjection
