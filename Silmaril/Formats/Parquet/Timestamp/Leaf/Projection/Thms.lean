module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection.Read
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection.Trace

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Projection

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Leaf.ScalarAndDictionary.WithV1

/-- Successful admission emits the checked schema and runs only that plan. -/
theorem readAll_opened {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    readAll limits input ordinals = .ok ⟨checked.schema, checked.trace limits⟩ := by
  simp [readAll, opened, Except.map]

/-- The earliest requested binding failure reports the original ordinal and projection position. -/
theorem bindOrdinals_first_error {snapshot : Snapshot.Checked} {limits : Footer.Limits}
    {ordinals : Array Nat} {before after : List (Fin ordinals.size)} {position : Fin ordinals.size}
    {bounds : List (BoundTo snapshot)} {cause : Leaf.Error}
    (split : List.finRange ordinals.size = before ++ position :: after)
    (earlier : before.mapM (fun i => bindAt snapshot limits i.val ordinals[i.val]) = .ok bounds)
    (failed : Leaf.bind limits snapshot ordinals[position.val] = .error cause) :
    bindOrdinals snapshot limits ordinals = .error (.bind position.val ordinals[position.val] cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.bindOrdinals_first_error split earlier failed

/-- Each output position is the corresponding modern bind into the single checked snapshot. -/
theorem openFile_bound {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.input.snapshot input = .ok checked.snapshot ∧
      ∃ width : checked.width = ordinals.size, ∀ i : Fin checked.width,
        Leaf.bind limits.input.snapshot.footer checked.snapshot ordinals[(i.cast width).val] = .ok (checked.column i) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.openFile_bound opened

/-- The selected original schema entries retain their nonzero ordinals and shared source. -/
theorem openFile_selected {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    ∃ width : checked.width = ordinals.size, ∀ i : Fin checked.width,
      (checked.column i).snapshot = checked.snapshot ∧
      (checked.column i).ordinal = ordinals[(i.cast width).val] ∧
      (checked.column i).ordinal ≠ 0 ∧
      checked.snapshot.metadata.schema[(checked.column i).ordinal]? = some (checked.column i).binding.leaf :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.openFile_selected opened

/-- A selected column forwards its exact AllCodecs failure with original group and ordinal. -/
theorem readCounts_failure {checked : Checked} {limits : Limits} {group rows : Nat}
    {position : Fin checked.width} {cause : AllCodecs.GroupError}
    (failed : AllCodecs.readGroup limits.codec limits.input.leaf (checked.column position) group = .error cause) :
    checked.readCounts limits group rows position =
      .error (.read group position.val (checked.column position).ordinal cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.readCounts_failure failed

/-- The first failed column in request order ends the group before emitting a batch. -/
theorem readGroup_first_column_error {checked : Checked} {limits : Limits} {group rows : Nat}
    {before after : List (Fin checked.width)} {position : Fin checked.width} {values : List (Counts rows)}
    {cause : Leaf.Projection.Error}
    (rowOk : checked.groupRows limits group = .ok rows)
    (split : List.finRange checked.width = before ++ position :: after)
    (earlier : before.mapM (checked.readCounts limits group rows) = .ok values)
    (failed : checked.readCounts limits group rows position = .error cause) :
    checked.readGroup limits group = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.readGroup_first_column_error rowOk split earlier failed

/-- Every successful batch retains the original footer row count, including at width zero. -/
theorem readGroup_footer {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} (read : checked.readGroup limits group = .ok batch) :
    ∃ original, checked.snapshot.groupAt group = some original ∧
      batch.rowCount = original.numRows.toNat ∧ batch.rowCount ≤ limits.input.leaf.maxRows :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.readGroup_footer read

/-- A successful typed column agrees with its independent AllCodecs leaf read. -/
theorem readGroup_column {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} (read : checked.readGroup limits group = .ok batch)
    (position : Fin checked.width) :
    ∃ slots, AllCodecs.readGroup limits.codec limits.input.leaf (checked.column position) group = .ok slots ∧
      batch.values position = cells (checked.schema.kind position).2 (slots.map (Option.map Ticks.ticks)) ∧
      (batch.values position).map (Option.map Ticks.ticks) = slots.map (Option.map Ticks.ticks) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.readGroup_column read position

/-- Reordering or narrowing a successful group agrees with logical column projection. -/
theorem readGroup_project (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} (read : checked.readGroup limits group = .ok batch) :
    (checked.project p).readGroup limits group = .ok (checked.projectBatch p batch) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.readGroup_project checked limits p read

/-- Physical projection reads only the selected columns after the shared group checks. -/
theorem projected_group_succeeds_iff (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) (group : Nat) :
    (∃ batch, (checked.project p).readGroup limits group = .ok batch) ↔
      ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∀ position : Fin p.width, ∃ counts, checked.readCounts limits group rows (p.index position) = .ok counts :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.projected_group_succeeds_iff checked limits p group

/-- The original first failed group retains exactly the complete earlier batches. -/
theorem trace_first_error {checked : Checked} {limits : Limits} {before after : List Nat}
    {group : Nat} {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)} {cause : Leaf.Projection.Error}
    (split : checked.indices = before ++ group :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches)
    (failed : checked.readGroup limits group = .error cause) :
    checked.trace limits = ⟨batches, .readError cause⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.trace_first_error split earlier failed

/-- The selected source reaches EOS exactly when every original group succeeds. -/
theorem trace_eos_iff (checked : Checked) (limits : Limits) :
    (checked.trace limits).termination = .eos ↔
      ∀ group ∈ checked.indices, ∃ batch, checked.readGroup limits group = .ok batch :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.trace_eos_iff checked limits

/-- The projected source retains the logical projection of every completed earlier group. -/
theorem trace_project_prefix {checked : Checked} {limits : Limits} (p : Scan.Projection checked.schema)
    {before rest : List Nat} {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)}
    (split : checked.indices = before ++ rest)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches) :
    (checked.project p).trace limits =
      ⟨batches.map (checked.projectBatch p) ++ ((checked.project p).traceGroups limits rest).batches,
        ((checked.project p).traceGroups limits rest).termination⟩ :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.trace_project_prefix p split earlier

/-- After wider EOS, logical Arrow projection and physical selection have equal traces. -/
theorem trace_scan (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    (checked.trace limits).scan p (fun _ => some true) = (checked.project p).trace limits :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.trace_scan checked limits p eos

/-- The two completed Event streams are observationally equivalent. -/
theorem trace_scan_equivalent (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    Arrow.Events.EventStream.Equivalent (Id := String)
      (.ok ⟨p.schema, (checked.trace limits).scan p (fun _ => some true)⟩)
      (.ok ⟨(checked.project p).schema, (checked.project p).trace limits⟩) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.trace_scan_equivalent checked limits p eos

/-- Physical projection can reach EOS while the wider source fails exactly under the selected-read and omitted-fault conditions. -/
theorem projected_eos_but_full_fails_iff (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema) :
    ((checked.project p).trace limits).termination = .eos ∧ (checked.trace limits).termination ≠ .eos ↔
      (∀ group ∈ checked.indices, ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∀ i : Fin p.width, ∃ counts, checked.readCounts limits group rows (p.index i) = .ok counts) ∧
      ∃ group ∈ checked.indices, ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∃ position : Fin checked.width, (∀ i : Fin p.width, p.index i ≠ position) ∧
          ∃ cause, checked.readCounts limits group rows position = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Projection.projected_eos_but_full_fails_iff checked limits p

end Silmaril.Formats.Parquet.Timestamp.Leaf.Projection
