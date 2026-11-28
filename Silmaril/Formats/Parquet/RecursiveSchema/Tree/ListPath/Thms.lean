module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.ListPath

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree

public section

/-- Projection preserves the signed leaf and all level thresholds used by
the existing scanner. The carrier keeps the original positional binding. -/
theorem LeafPath.projected_levels {path : LeafPath} {plan : ListPath.Plan}
    (projected : path.listPlan = some plan) :
    plan.shape.leaf = (path.site, path.kind) ∧ plan.shape.steps {} = path.steps ∧
      plan.shape.definitions = path.maxDefinition ∧ plan.shape.repetitions = path.maxRepetition ∧
      ListPath.Chunk.wrappers plan = path.repeated.map (·.emptyLevel) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.projected_levels projected

/-- The checked scanner keeps the complete original signed path and
every ordered definition transition and repetition threshold. -/
theorem LeafPath.scan_levels {path : LeafPath} {plan : ListPath.Shape} (projected : plan = path.shape) :
    plan.leaf = (path.site, path.kind) ∧ plan.steps {} = path.steps ∧
      plan.definitions = path.maxDefinition ∧ plan.repetitions = path.maxRepetition ∧
      ListPath.Chunk.wrappers plan = path.repeated.map (·.emptyLevel) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.scan_levels projected

theorem LeafBinding.read_wire {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits snapshot} {group column : Nat} {bound : LeafBinding compiled group column}
    {caps : ListPath.Chunk.Limits} {out : ListPath.Chunk.Observation} (read : bound.read caps = .ok out) :
    ListPath.Chunk.Wire caps bound.carrier out :=
  (ListPath.Chunk.readCarrier_wire read).1

/-- An observed V1 or V2 page retains its original absolute header
and the shared physical witness over the complete signed path. -/
theorem LeafBinding.original_page {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits snapshot} {group column : Nat} {bound : LeafBinding compiled group column}
    {caps : ListPath.Chunk.Limits} {out : ListPath.Chunk.Observation} {page : ListPath.Chunk.ObservedPage}
    (read : bound.read caps = .ok out) (member : page ∈ out.pages) :
    Page.readPage caps.framing bound.carrier.source bound.span page.frame.header.start = .ok page.frame ∧
      ListPath.Chunk.DataPageWire caps bound.plan (ListPath.Chunk.wrappers bound.plan) bound.carrier.source
        page.frame page.start (bound.carrier.slots - page.start.slots) bound.carrier.rows page.decoded
        bound.codec out.dictionary := by
  have wire := bound.read_wire read
  exact ⟨wire.originalHeader (List.mem_append_right _ (List.mem_map_of_mem member)),
    wire.checked.page_of_mem member⟩

theorem LeafBinding.read_page_failure {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits snapshot} {group column : Nat} {bound : LeafBinding compiled group column}
    {caps : ListPath.Chunk.Limits} {address : RecursiveSchema.Chunk.Address}
    {ordinal byte : Nat} {start : ListPath.Chunk.State} {cause : ListPath.Chunk.PageCause}
    (refused : bound.read caps = .error (.page address ordinal byte start cause)) :
    ListPath.Chunk.PageFailureWire caps bound.carrier address ordinal byte start cause :=
  ListPath.Chunk.readCarrier_page_failure refused

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree
