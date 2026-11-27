module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Defs
import Silmaril.Semantics.Relational.Scan.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events

open Silmaril.Relational
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events

theorem projectTrace_counts {source : Signature} (projection : Scan.Projection source)
    (trace : Trace source) :
    (projectTrace projection trace).batches.map (·.rowCount) =
      trace.batches.map (·.rowCount) := by
  simp only [projectTrace, List.map_map]
  rfl

theorem projectTrace_rows {source : Signature} (projection : Scan.Projection source)
    (trace : Trace source) :
    (projectTrace projection trace).rows = projection.project trace.rows := by
  have rows (batch : BatchEvent source) :
      (projection.projectColumns batch).toRows = projection.project batch.toRows :=
    projection.rowsEquiv_projectColumns batch
  simp only [projectTrace, Formats.Arrow.Events.Trace.rows, List.flatMap_map, Function.comp_def,
    rows, Scan.Projection.project, List.map_flatMap]
  rfl

theorem projectTrace_id {source : Signature} (trace : Trace source) :
    projectTrace (Scan.Projection.id source) trace = trace := by
  cases trace with
  | mk batches termination =>
    have each (batch : BatchEvent source) : (Scan.Projection.id source).projectColumns batch = batch := by
      cases batch
      rfl
    have same : (Scan.Projection.id source).projectColumns = id := funext each
    simp only [projectTrace, same]
    exact congrArg (fun columns : List (BatchEvent source) =>
      (⟨columns, termination⟩ : Trace source)) (List.map_id batches)

theorem projectTrace_comp {source : Signature} (first : Scan.Projection source)
    (second : Scan.Projection first.schema) (trace : Trace source) :
    projectTrace (first.comp second) trace = projectTrace second (projectTrace first trace) := by
  simp only [projectTrace, List.map_map]
  rfl

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Events
