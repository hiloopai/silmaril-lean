module

public import Silmaril.Formats.Parquet.FlatProjection.Events.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Events.Read
import Silmaril.Semantics.Relational.Scan.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Events

open Silmaril.Formats.Parquet.FlatProjection.Events
open Silmaril.Formats Silmaril.Relational

private theorem traceGroups_append {checked : Checked} {limits : Limits} {before rest : List Nat}
    {batches : List (Scan.Columns checked.schema Cell)}
    (earlier : before.mapM (checked.readGroup limits) = .ok batches) :
    checked.traceGroups limits (before ++ rest) =
      ⟨batches ++ (checked.traceGroups limits rest).batches, (checked.traceGroups limits rest).termination⟩ := by
  induction before generalizing batches with
  | nil =>
    cases earlier
    cases observed : checked.traceGroups limits rest
    simp [observed]
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
    {group : Nat} {batches : List (Scan.Columns checked.schema Cell)} {cause : Error}
    (split : checked.indices = before ++ group :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok batches)
    (failed : checked.readGroup limits group = .error cause) :
    checked.trace limits = ⟨batches, .readError cause⟩ := by
  rw [Checked.trace, split, traceGroups_append earlier]
  simp [Checked.traceGroups, failed]

theorem trace_project_prefix {checked : Checked} {limits : Limits} (p : Scan.Projection checked.schema)
    {before rest : List Nat} {batches : List (Scan.Columns checked.schema Cell)}
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

private theorem traceGroups_eos {checked : Checked} {limits : Limits} (groups : List Nat)
    (eos : (checked.traceGroups limits groups).termination = .eos) :
    groups.mapM (checked.readGroup limits) = .ok (checked.traceGroups limits groups).batches := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    cases read : checked.readGroup limits group with
    | error cause => simp [Checked.traceGroups, read] at eos
    | ok batch =>
      have tail : (checked.traceGroups limits rest).termination = .eos := by
        simpa [Checked.traceGroups, read] using eos
      simp [Checked.traceGroups, read, List.mapM_cons, ih tail, Bind.bind, Except.bind, pure, Except.pure]

theorem trace_scan (checked : Checked) (limits : Limits) (p : Scan.Projection checked.schema)
    (eos : (checked.trace limits).termination = .eos) :
    (checked.trace limits).scan p (fun _ => some true) = (checked.project p).trace limits := by
  have projected := trace_project_prefix (limits := limits) p (rest := [])
    (List.append_nil _).symm (traceGroups_eos checked.indices eos)
  rw [projected]
  simp only [Checked.traceGroups, List.append_nil, Arrow.Events.Trace.scan, eos]
  apply congrArg (fun batches => (⟨batches, .eos⟩ : Arrow.Events.Trace p.schema Cell Error))
  apply List.map_congr_left
  intro batch _
  have rows : (p.projectColumns batch).toRows = p.project batch.toRows := p.rowsEquiv_projectColumns batch
  calc
    _ = AlignedColumns.ofRows (p.projectColumns batch).toRows := by
      rw [rows]
      simp [Scan.Projection.scan, Scan.select]
    _ = _ := AlignedColumns.ofRows_toRows _

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Events
