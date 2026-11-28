module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Read

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader

open Arrow.RecursiveSchema.Batch.Rows (Observation RowFits)

public section

/-- Both wrapper stops depend on the LIST declarations. The optional
Struct adds a definition step after the inner wrapper. -/
theorem Plan.path_levels (plan : Plan) (side : Side) :
    (plan.path side).shape.repetitions = 2 ∧
      (plan.path side).shape.definitions = plan.sharedDefinition + (plan.child side).1.nullable.toNat ∧
      ListPath.Chunk.wrappers (plan.path side) =
        [plan.outer.site.nullable.toNat, plan.listDefinition - 1] :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.path_levels plan side

/-- Both child paths use the original Struct site for the shared absence step. -/
theorem Plan.optional_step (plan : Plan) (side : Side) (optional : plan.element.nullable = true) :
    ((plan.path side).shape.steps {})[plan.listDefinition]? =
      some (.optional plan.element.location .element) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.optional_step plan side optional

theorem readColumn_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : ListPath.Chunk.Observation} (read : readColumn limits binding = .ok out) :
    ColumnWire limits binding out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.column_wire read

theorem ColumnBinding.codec_exact {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} (binding : ColumnBinding schema bound side) :
    RecursiveSchema.Repeated.Chunk.ColumnCodec.ofId binding.column.metadata.codec = some binding.codec.column :=
  ListPath.Chunk.Codec.column_ofId binding.originalCodec

/-- Recover the original V1 frame and the full-body wire witness for its codec. -/
theorem ColumnWire.v1_page {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : RecursiveSchema.ListPath.Chunk.Observation} {page : RecursiveSchema.ListPath.Chunk.ObservedPage}
    {info : Page.DataV1} (wire : ColumnWire limits binding out) (member : page ∈ out.pages)
    (version : page.frame.value.kind = .dataV1 info) :
    let carrier := carrierOf binding
    Page.readPage limits.framing carrier.source carrier.span page.frame.header.start = .ok page.frame ∧
    RecursiveSchema.ListPath.Chunk.PageWire limits carrier.plan (RecursiveSchema.ListPath.Chunk.wrappers carrier.plan)
      carrier.source page.frame page.start (carrier.slots - page.start.slots) carrier.rows page.decoded
      carrier.codec .plain :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.column_v1_page wire member version

/-- Recover the original V2 header and the shared wire witness for its
raw level lengths, slot, row and null counts, and closed boundaries. -/
theorem ColumnWire.v2_page {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : RecursiveSchema.ListPath.Chunk.Observation} {page : RecursiveSchema.ListPath.Chunk.ObservedPage}
    {info : Page.DataV2} (wire : ColumnWire limits binding out) (member : page ∈ out.pages)
    (version : page.frame.value.kind = .dataV2 info) :
    let carrier := carrierOf binding
    Page.readPage limits.framing carrier.source carrier.span page.frame.header.start = .ok page.frame ∧
    RecursiveSchema.ListPath.Chunk.V2PageWire limits carrier.plan (RecursiveSchema.ListPath.Chunk.wrappers carrier.plan)
      carrier.source page.frame page.start (carrier.slots - page.start.slots) carrier.rows page.decoded
      carrier.codec .plain :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.column_v2_page wire member version

theorem readColumn_page_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat}
    {start : ListPath.Chunk.State} {cause : ListPath.Chunk.PageCause}
    (refused : readColumn limits binding = .error (.page address ordinal byte start cause)) :
    ListPath.Chunk.PageFailureWire limits (carrierOf binding) address ordinal byte start cause :=
  ListPath.Chunk.readCarrier_page_failure refused

/-- Successful reconstruction agrees on all shared ancestors and
projects each child back to its exact original signed slot trace. -/
theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits} {out : Observation}
    (read : readGroup limits schema group = .ok out) : GroupWire limits schema group out :=
  (Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.group_checked read).1

theorem readGroup_typed {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits} {out : Observation}
    (read : readGroup limits schema group = .ok out) :
    ∀ row ∈ out.rows, RowFits schema.plan.arrow.fields row :=
  (Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.group_checked read).2

/-- A topology refusal has two independently checked original chunks
and reaches the first unmatched slot after their common prefix. -/
theorem readGroup_topology_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {cause : Rows.TopologyError} (read : readGroup limits schema group = .error (.topology cause)) :
    GroupTopologyFailure limits schema group cause :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.group_topology_failure read

theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {limits : Limits} {out : List Observation}
    (read : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.all_wire read

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader
