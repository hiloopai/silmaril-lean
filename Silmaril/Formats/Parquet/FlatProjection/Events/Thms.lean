module

public import Silmaril.Formats.Parquet.FlatProjection.Events.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Events.Read
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Events.Trace

public section

namespace Silmaril.Formats.Parquet.FlatProjection.Events

open Silmaril.Relational

/-- All successful bindings refer to the same checked snapshot, in request order. -/
theorem openFile_exact {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.primitive.column.snapshot input = .ok checked.snapshot ∧
      ∃ width : checked.width = ordinals.size, ∀ i : Fin checked.width,
        bindOrdinal limits.primitive.column.snapshot.footer checked.snapshot ordinals[i.cast width] =
          .ok (checked.bindings i) ∧ (checked.bindings i).ordinal = ordinals[i.cast width] :=
  Proofs.Formats.Parquet.FlatProjection.Events.openFile_exact opened

/-- The opened schema and checked group trace are the complete Events result. -/
theorem readAll_opened {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    readAll limits input ordinals = .ok ⟨checked.schema, checked.trace limits⟩ := by
  simp [readAll, opened, Except.map]

/-- Each batch position returns the exact typed result of its original bound column. -/
theorem readGroup_columns {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Cell} :
    checked.readGroup limits group = .ok batch ↔
      checked.groupRows limits group = .ok batch.rowCount ∧
      ∀ i, (checked.bindings i).read limits group = .ok (batch.values i) :=
  Proofs.Formats.Parquet.FlatProjection.Events.readGroup_ok_iff

/-- Every successful batch has the original footer row count, even at width zero. -/
theorem readGroup_footer {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Cell} (read : checked.readGroup limits group = .ok batch) :
    ∃ original, checked.snapshot.groupAt group = some original ∧
      batch.rowCount = original.numRows.toNat ∧ batch.rowCount ≤ limits.primitive.column.column.maxRows :=
  Proofs.Formats.Parquet.FlatProjection.Events.readGroup_footer read

/-- The selected branch's cause retains the group, request position and original ordinal. -/
theorem readColumn_failure {checked : Checked} {limits : Limits} {group rows : Nat}
    {position : Fin checked.width} {cause : ColumnError}
    (failed : (checked.bindings position).read limits group = .error cause) :
    checked.readColumn limits group rows position =
      .error (.column group position.val (checked.bindings position).ordinal cause) := by
  simp [Checked.readColumn, failed, Except.mapError, Bind.bind, Except.bind]

/-- Earlier columns must succeed. The first column failure prevents a partial batch. -/
theorem readGroup_first_column_error {checked : Checked} {limits : Limits} {group rows : Nat}
    {before after : List (Fin checked.width)} {position : Fin checked.width}
    {done : List Unit} {cause : Error}
    (rowOk : checked.groupRows limits group = .ok rows)
    (split : List.finRange checked.width = before ++ position :: after)
    (earlier : before.mapM (fun i => (checked.readColumn limits group rows i).map (fun _ => ())) = .ok done)
    (failed : checked.readColumn limits group rows position = .error cause) :
    checked.readGroup limits group = .error cause :=
  Proofs.Formats.Parquet.FlatProjection.Events.readGroup_first_column_error rowOk split earlier failed

/-- Every earlier group is retained, and the original first group error ends the trace. -/
theorem trace_first_error {checked : Checked} {limits : Limits} {before after : List Nat}
    {group : Nat} {batches : List (Scan.Columns checked.schema Cell)} {cause : Error}
    (split : checked.indices = before ++ group :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches)
    (failed : checked.readGroup limits group = .error cause) :
    checked.trace limits = ⟨batches, .readError cause⟩ :=
  Proofs.Formats.Parquet.FlatProjection.Events.trace_first_error split earlier failed

/-- Narrowing or reordering a successful batch agrees with projecting its typed columns. -/
theorem readGroup_project (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) {group : Nat}
    {batch : Scan.Columns checked.schema Cell} (read : checked.readGroup limits group = .ok batch) :
    (checked.project p).readGroup limits group = .ok (checked.projectBatch p batch) :=
  Proofs.Formats.Parquet.FlatProjection.Events.readGroup_project checked limits p read

/-- Every complete wider group projects exactly. The narrower physical read
determines its own remaining groups and terminal outcome. -/
theorem trace_project_prefix {checked : Checked} {limits : Limits} (p : Scan.Projection checked.schema)
    {before rest : List Nat} {batches : List (Scan.Columns checked.schema Cell)}
    (split : checked.indices = before ++ rest)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches) :
    (checked.project p).trace limits =
      ⟨batches.map (checked.projectBatch p) ++ ((checked.project p).traceGroups limits rest).batches,
        ((checked.project p).traceGroups limits rest).termination⟩ :=
  Proofs.Formats.Parquet.FlatProjection.Events.trace_project_prefix p split earlier

/-- Wider EOS implies exact logical and physical projection agreement, including batch boundaries. -/
theorem trace_scan (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    (checked.trace limits).scan p (fun _ => some true) = (checked.project p).trace limits :=
  Proofs.Formats.Parquet.FlatProjection.Events.trace_scan checked limits p eos

/-- Completed reads agree under the common Arrow Events observation. -/
theorem trace_scan_equivalent (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    Arrow.Events.EventStream.Equivalent (Id := String)
      (.ok ⟨p.schema, (checked.trace limits).scan p (fun _ => some true)⟩)
      (.ok ⟨(checked.project p).schema, (checked.project p).trace limits⟩) := by
  rw [trace_scan checked limits p eos]
  rfl

end Silmaril.Formats.Parquet.FlatProjection.Events
