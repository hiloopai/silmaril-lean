module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.Readback

public section

namespace Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered

open Arrow.TimestampStream.Ordered (Stream Batch Field)

/-- The original field order and descriptors determine the exact Parquet units and UTC or local semantics. -/
theorem bindFields_exact {nameBytes : Nat} {fields : List (Field × Nat)} {names : List String}
    {leaves : List LeafPlan} (bound : bindFields nameBytes fields names = .ok leaves) :
    List.Forall₂ (fun field leaf => leaf.field = field.1 ∧
      FromIpc.descriptor field.1 = .ok leaf.descriptor ∧
      leaf.descriptor.unit.tickUnit = field.1.metadata.unit ∧
      field.1.metadata.timezone = (if leaf.descriptor.isAdjustedToUTC then some "UTC" else none))
      fields leaves :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.bindFields_exact bound

/-- Each shared page plan accounts for the exact placed column extent. -/
theorem placeColumns_exact (offset : Nat) (columns : List ColumnPlan) :
    (placeColumns offset columns).1 = offset + (columns.map (·.page.size)).sum ∧
      List.Forall₂ (fun column index => index.name = column.index.name ∧
        index.optional = column.index.optional ∧ index.size = column.page.size)
        columns (placeColumns offset columns).2 :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.placeColumns_exact offset columns

/-- Preflight retains the original ordered page plans and the bounded shared INT64 footer. -/
theorem preflight_wire {limits : Limits} {source : Stream} {plan : Plan}
    (prepared : preflight limits source = .ok plan) :
    ∃ leaves indices,
      checkBudget limits source = .ok () ∧
      bindFields limits.writer.snapshot.footer.compact.maxBinaryBytes source.fields.zipIdx [] = .ok leaves ∧
      (source.batches.zipIdx.mapM fun (batch, group) => planGroup limits.writer.leaf leaves batch group) =
        .ok plan.groups ∧
      placeGroups 4 plan.groups = (plan.dataStop, indices) ∧
      FlatInt32Writer.Compact.encodeGroupsWriting 2 (footerLimit limits plan.dataStop)
        (leaves.map fun leaf => FromIpc.Internal.leaf leaf.descriptor leaf.index) indices = .ok plan.footer ∧
      plan.dataStop + plan.footer.length + 8 ≤ fileLimit limits :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.preflight_wire prepared

/-- Emission assembles the measured PLAIN V1 pages and the checked footer in file order. -/
theorem emit_wire {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ plan groups, preflight limits source = .ok plan ∧
      (plan.groups.zipIdx.mapM fun (group, ordinal) => emitGroup group ordinal) = .ok groups ∧
      4 + (groups.flatten.map Bytes.length).sum = plan.dataStop ∧ wire = assemble plan groups :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.emit_wire written

/-- Certification retains every field and group from the ordered Parquet Events projection. -/
theorem certify_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (checked : certify limits source wire = .ok ()) :
    ∃ projection : Leaf.Projection.Checked,
      Leaf.Projection.openFile (readbackLimits limits) wire (ordinals source) = .ok projection ∧
      FooterMatches projection source ∧
      (projection.trace (readbackLimits limits)).termination = .eos ∧
      Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.certify_readback checked

/-- The emitted file reads back to the complete ordered input observation. -/
theorem emit_readback {limits : Limits} {source : Stream} {wire : Bytes}
    (written : emit limits source = .ok wire) :
    ∃ projection : Leaf.Projection.Checked, FooterMatches projection source ∧
      Leaf.Projection.readAll (readbackLimits limits) wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace (readbackLimits limits)⟩ ∧
      (projection.trace (readbackLimits limits)).termination = .eos ∧
      Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.emit_readback written

/-- Within the input byte cap, the original IPC error precedes every Parquet writer decision. -/
theorem convert_source_error {ipc : Arrow.Limits} {limits : Limits} {input : KBytes}
    {cause : Arrow.TimestampStream.Ordered.Error}
    (fits : input.len ≤ limits.writer.maxInputBytes)
    (failed : Arrow.TimestampStream.Ordered.read ipc input = .error cause) :
    convert ipc limits input = .error (.source cause) :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.convert_source_error fits failed

/-- Successful reverse conversion preserves input IPC through exact EOS and recovers the exact ordered Parquet observation. -/
theorem convert_readback {ipc : Arrow.Limits} {limits : Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ (source : Stream) (projection : Leaf.Projection.Checked) (start : Nat),
      Arrow.TimestampStream.Ordered.read ipc input = .ok source ∧
      Arrow.TimestampStream.Ordered.readSchema ipc input = .ok (source.fields, start) ∧
      Arrow.TimestampStream.Ordered.BatchesWire ipc input source.fields ipc.batches start source.batches ∧
      FooterMatches projection source ∧
      Leaf.Projection.readAll (readbackLimits limits) wire (ordinals source) =
        .ok ⟨projection.schema, projection.trace (readbackLimits limits)⟩ ∧
      (projection.trace (readbackLimits limits)).termination = .eos ∧
      Leaf.Projection.ToIpc.observation (projection.trace (readbackLimits limits)) = source :=
  Proofs.Formats.Parquet.Timestamp.FromIpc.Ordered.convert_readback written

end Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered
