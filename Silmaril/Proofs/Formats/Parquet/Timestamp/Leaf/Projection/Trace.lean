module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection.Read
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection

theorem traceGroups_append {checked : Checked} {limits : Limits} {before rest : List Nat}
    {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)}
    (earlier : before.mapM (checked.readGroup limits) = .ok batches) :
    checked.traceGroups limits (before ++ rest) =
      ⟨batches ++ (checked.traceGroups limits rest).batches, (checked.traceGroups limits rest).termination⟩ := by
  induction before generalizing batches with
  | nil =>
    cases earlier
    cases exactTrace : checked.traceGroups limits rest
    simp [exactTrace]
  | cons group tail ih =>
    cases head : checked.readGroup limits group with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at earlier
    | ok batch =>
      cases later : tail.mapM (checked.readGroup limits) with
      | error cause => simp [List.mapM_cons, head, later, Bind.bind, Except.bind] at earlier
      | ok outputs =>
        simp [List.mapM_cons, head, later, Bind.bind, Except.bind, pure, Except.pure] at earlier
        subst batches
        simp [Checked.traceGroups, head, ih later]

theorem trace_first_error {checked : Checked} {limits : Limits} {before after : List Nat}
    {group : Nat} {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)} {cause : Leaf.Projection.Error}
    (split : checked.indices = before ++ group :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches)
    (failed : checked.readGroup limits group = .error cause) :
    checked.trace limits = ⟨batches, .readError cause⟩ := by
  rw [Checked.trace, split, traceGroups_append earlier]
  simp [Checked.traceGroups, failed]

private theorem traceGroups_eos_iff (checked : Checked) (limits : Limits) (groups : List Nat) :
    (checked.traceGroups limits groups).termination = .eos ↔
      ∀ group ∈ groups, ∃ batch, checked.readGroup limits group = .ok batch := by
  induction groups with
  | nil => simp [Checked.traceGroups]
  | cons group tail ih =>
    cases read : checked.readGroup limits group <;>
      simp [Checked.traceGroups, read, ih]

theorem trace_eos_iff (checked : Checked) (limits : Limits) :
    (checked.trace limits).termination = .eos ↔
      ∀ group ∈ checked.indices, ∃ batch, checked.readGroup limits group = .ok batch :=
  traceGroups_eos_iff checked limits checked.indices

private theorem traceGroups_project (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) (groups : List Nat)
    (eos : (checked.traceGroups limits groups).termination = .eos) :
    (checked.project p).traceGroups limits groups =
      ⟨(checked.traceGroups limits groups).batches.map (checked.projectBatch p), .eos⟩ := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    obtain ⟨batch, read⟩ := (traceGroups_eos_iff checked limits _).mp eos group (by simp)
    have tailEos : (checked.traceGroups limits rest).termination = .eos := by
      simpa [Checked.traceGroups, read] using eos
    simp [Checked.traceGroups, read, readGroup_project checked limits p read, ih tailEos, List.map_cons]

theorem trace_project (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    (checked.project p).trace limits = ⟨(checked.trace limits).batches.map (checked.projectBatch p), .eos⟩ :=
  traceGroups_project checked limits p checked.indices eos

theorem trace_project_prefix {checked : Checked} {limits : Limits} (p : Scan.Projection checked.schema)
    {before rest : List Nat} {batches : List (Scan.Columns checked.schema Leaf.Events.Cell)}
    (split : checked.indices = before ++ rest)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches) :
    (checked.project p).trace limits =
      ⟨batches.map (checked.projectBatch p) ++ ((checked.project p).traceGroups limits rest).batches,
        ((checked.project p).traceGroups limits rest).termination⟩ := by
  have projected : before.mapM ((checked.project p).readGroup limits) = .ok (batches.map (checked.projectBatch p)) := by
    rw [List.mapM_eq_ok_iff_forall₂, List.forall₂_map_right_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp earlier).imp fun _ _ => readGroup_project checked limits p
  change (checked.project p).traceGroups limits checked.indices = _
  rw [split, traceGroups_append projected]

/-- Logical Arrow projection agrees with reading only the selected positions when the wider trace reaches EOS. -/
theorem trace_scan (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    (checked.trace limits).scan p (fun _ => some true) = (checked.project p).trace limits := by
  rw [trace_project checked limits p eos]
  simp only [Arrow.Events.Trace.scan, eos]
  apply congrArg (fun batches => (⟨batches, .eos⟩ : Arrow.Events.Trace p.schema Leaf.Events.Cell Leaf.Projection.Error))
  apply List.map_congr_left
  intro batch _
  have rows : (p.projectColumns batch).toRows = p.project batch.toRows :=
    p.rowsEquiv_projectColumns batch
  calc
    _ = AlignedColumns.ofRows (p.projectColumns batch).toRows := by
      rw [rows]
      simp [Scan.Projection.scan, Scan.select]
    _ = _ := AlignedColumns.ofRows_toRows _

theorem trace_scan_equivalent (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    Arrow.Events.EventStream.Equivalent (Id := String)
      (.ok ⟨p.schema, (checked.trace limits).scan p (fun _ => some true)⟩)
      (.ok ⟨(checked.project p).schema, (checked.project p).trace limits⟩) := by
  rw [trace_scan checked limits p eos]
  rfl

/-- Physical projection can reach EOS while the wider read fails exactly when
all shared group checks and selected reads pass, and an omitted column fails. -/
theorem projected_eos_but_full_fails_iff (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema) :
    ((checked.project p).trace limits).termination = .eos ∧ (checked.trace limits).termination ≠ .eos ↔
      (∀ group ∈ checked.indices, ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∀ i : Fin p.width, ∃ counts, checked.readCounts limits group rows (p.index i) = .ok counts) ∧
      ∃ group ∈ checked.indices, ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∃ position : Fin checked.width, (∀ i : Fin p.width, p.index i ≠ position) ∧
          ∃ cause, checked.readCounts limits group rows position = .error cause := by
  classical
  simp only [ne_eq, trace_eos_iff]
  change ((∀ group ∈ checked.indices, ∃ batch, (checked.project p).readGroup limits group = .ok batch) ∧ _) ↔ _
  simp only [projected_group_succeeds_iff]
  constructor
  · rintro ⟨selected, bad⟩
    refine ⟨selected, ?_⟩
    push Not at bad
    obtain ⟨group, member, failed⟩ := bad
    obtain ⟨rows, rowOk, columns⟩ := selected group member
    have missing : ∃ position : Fin checked.width,
        ∃ cause, checked.readCounts limits group rows position = .error cause := by
      by_contra! noneFailed
      have succeeds : ∃ batch, checked.readGroup limits group = .ok batch := by
        apply (readGroup_succeeds_iff checked limits group).mpr
        refine ⟨rows, rowOk, fun position => ?_⟩
        cases read : checked.readCounts limits group rows position with
        | ok value => exact ⟨value, rfl⟩
        | error cause => exact False.elim (noneFailed position cause read)
      obtain ⟨batch, read⟩ := succeeds
      exact failed batch read
    obtain ⟨position, cause, read⟩ := missing
    refine ⟨group, member, rows, rowOk, position, ?_, cause, read⟩
    intro i projected
    obtain ⟨counts, success⟩ := columns i
    rw [projected, read] at success
    contradiction
  · rintro ⟨selected, group, member, rows, rowOk, position, _, cause, failed⟩
    refine ⟨selected, fun whole => ?_⟩
    obtain ⟨batch, decoded⟩ := whole group member
    obtain ⟨rows', columns⟩ := readGroup_ok_iff.mp decoded
    have same : batch.rowCount = rows := Except.ok.inj (rows'.symm.trans rowOk)
    obtain ⟨counts, read, _⟩ := columns position
    have failure : checked.readCounts limits group batch.rowCount position = .error cause := same.symm ▸ failed
    rw [failure] at read
    contradiction

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection
