module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Read

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader

open Arrow.RecursiveSchema.Batch.Rows (Observation)

public section

/-- The original group and its checked native frames supply exactly the
ordered rows of the canonical LIST path. -/
theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Chunk.Limits} {out : Observation}
    (accepted : readGroup limits schema group = .ok out) :
    GroupWire limits schema group out :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.group_wire accepted

/-- Exactly one successful observation per original group, in footer order. -/
theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {limits : Chunk.Limits} {out : List Observation}
    (accepted : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.all_wire accepted

/-- Changing page boundaries in an accepted V1 chunk preserves the
reconstruction when the original plan and ordered trace agree. -/
theorem reconstruct_reframe {limits : Chunk.Limits} {left right : Chunk.Carrier}
    {before after : Chunk.Observation}
    (first : Chunk.Wire limits left before) (second : Chunk.Wire limits right after)
    (samePlan : left.plan = right.plan) (sameTrace : before.atoms = after.atoms) :
    Rows.reconstruct limits.logical left.plan left.rows before.atoms =
      Rows.reconstruct limits.logical right.plan right.rows after.atoms :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.reframe first second samePlan sameTrace

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader
