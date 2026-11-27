module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Footer
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Readback

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp

open Arrow.MixedFlat.Timestamp (Stream Batch)
open FlatInt32Writer.Compact

/-- Uniform physical tags retain the previous per-group Compact program. -/
theorem groupFor_legacy (physical : Int) (rows : Nat) (columns : List ColumnIndex) :
    groupFor physical rows columns = (do
      FlatInt32Writer.Compact.field 1 9
      listHeader 12 columns.length
      for column in columns do chunkFor physical rows column
      FlatInt32Writer.Compact.field 1 6
      integer .i64 (columns.map ColumnIndex.size).sum
      FlatInt32Writer.Compact.field 1 6
      integer .i64 rows
      octet 0) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.groupFor_legacy physical rows columns

/-- Uniform physical tags retain the previous bounded footer program. -/
theorem typed_homogeneous_legacy (physical : Int) (limit : Nat) (leaves : List (Write Unit))
    (groups : List (Nat × List ColumnIndex)) :
    encodeGroupsTyped limit leaves (Internal.tagGroups physical groups) =
      ((do
        FlatInt32Writer.Compact.field 1 5
        integer .i32 1
        FlatInt32Writer.Compact.field 1 9
        listHeader 12 (leaves.length + 1)
        root leaves.length
        for writeLeaf in leaves do writeLeaf
        FlatInt32Writer.Compact.field 1 6
        integer .i64 (groups.map Prod.fst).sum
        FlatInt32Writer.Compact.field 1 9
        listHeader 12 groups.length
        for (rows, chunks) in groups do groupFor physical rows chunks
        octet 0 : Write Unit).run ⟨limit, .empty⟩).map (·.2.bytes) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.typed_homogeneous_legacy physical limit leaves groups

/-- Both orders of the existing primitive pair have identical bounded serializer results. -/
theorem typed_primitive_pair (order : MixedV1Writer.Order) (limit : Nat) (ints octets : ColumnIndex)
    (groups : List MixedV1Writer.Compact.GroupIndex) :
    encodeGroupsTyped limit (order.columns (leaf ints) (MixedV1Writer.Compact.byteLeaf octets))
      (groups.map fun group => (group.rows, order.columns ⟨1, group.ints⟩ ⟨6, group.octets⟩)) =
      MixedV1Writer.Compact.encodeGroupsOrdered order limit ints octets groups :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.typed_primitive_pair order limit ints octets groups

/-- Placement retains the tag, name, nullability and measured extent of each chunk. -/
theorem placeColumns_exact (offset : Nat) (columns : List ColumnPlan) :
    (placeColumns offset columns).1 = offset + (columns.map (·.page.size)).sum ∧
      List.Forall₂ (fun column index => index.physical = column.index.physical ∧
        index.column.name = column.index.column.name ∧ index.column.optional = column.index.column.optional ∧
        index.column.size = column.page.size) columns (placeColumns offset columns).2 :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.placeColumns_exact offset columns

/-- Preflight binds the original fields and batches before running the bounded typed footer serializer. -/
theorem preflight_wire {limits : Limits} {source : Stream} {plan : Plan}
    (prepared : preflight limits source = .ok plan) :
    ∃ leaves indices,
      checkBudget limits source = .ok () ∧
      bindFields limits.primitiveFile.snapshot.footer.compact.maxBinaryBytes source.fields.zipIdx [] = .ok leaves ∧
      (source.batches.zipIdx.mapM fun (batch, group) => planGroup limits leaves batch group) = .ok plan.groups ∧
      placeGroups 4 plan.groups = (plan.dataStop, indices) ∧
      encodeGroupsTyped (footerLimit limits plan.dataStop) (leaves.map LeafPlan.write) indices = .ok plan.footer ∧
      plan.dataStop + plan.footer.length + 8 ≤ fileLimit limits :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.preflight_wire prepared

/-- Successful emission uses exactly the measured groups and footer. -/
theorem emit_wire {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ plan groups, preflight limits source = .ok plan ∧
      (plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup limits group ordinal) = .ok groups ∧
      4 + (groups.flatten.map Bytes.length).sum = plan.dataStop ∧ wire = assemble plan groups :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.emit_wire written

/-- The existing heterogeneous Events reader recovers the exact ordered source and all footer row counts. -/
theorem emit_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ projection : FlatProjection.Events.Checked, FooterMatches projection source ∧
      FlatProjection.Events.readAll limits.readback wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace limits.readback⟩ ∧
      (projection.trace limits.readback).termination = .eos ∧
      FlatProjection.Events.ToIpc.observation (projection.trace limits.readback) = source :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.emit_readback written

/-- Inside the input cap, the original IPC error precedes every writer decision. -/
theorem convert_source_error {ipc : Arrow.ObservationLimits} {limits : Limits} {input : KBytes}
    {cause : Arrow.MixedFlat.Timestamp.Error}
    (fits : input.len ≤ limits.maxInputBytes) (failed : Arrow.MixedFlat.Timestamp.read ipc input = .error cause) :
    convert ipc limits input = .error (.source cause) := by
  simp [convert, Nat.not_lt.mpr fits, failed, Except.mapError, Bind.bind, Except.bind]

/-- Conversion recovers the exact original IPC through EOS and preserves its ordered observation. -/
theorem convert_readback {ipc : Arrow.ObservationLimits} {limits : Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ (source : Stream) (projection : FlatProjection.Events.Checked) (start : Nat),
      Arrow.MixedFlat.Timestamp.read ipc input = .ok source ∧
      Arrow.MixedFlat.Timestamp.readSchema ipc.ipc input = .ok (source.fields, start) ∧
      Arrow.MixedFlat.Timestamp.BatchesWire ipc input source.fields ipc.ipc.batches 0 start source.batches ∧
      FooterMatches projection source ∧
      FlatProjection.Events.readAll limits.readback wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace limits.readback⟩ ∧
      (projection.trace limits.readback).termination = .eos ∧
      FlatProjection.Events.ToIpc.observation (projection.trace limits.readback) = source :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.convert_readback written

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp
