module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Events.Shape

public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events

open Silmaril.Relational

/-- Every declared column yields one ordered nullable slot per row. -/
theorem batch_shape {limits : MixedFlat.Limits} {body : KBytes}
    {fields : List Field} {metadata : MixedFlat.Metadata} {observed : Observed}
    (wire : BatchWire limits fields metadata body observed) :
    observed.columns.map Prod.fst = fields ∧
      ∀ pair ∈ observed.columns, (cells pair.1.kind pair.2).length = observed.rowCount :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Events.batch_shape wire

theorem ofObserved_agrees (fields : List Field) (observed : Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.1.kind pair.2).length = observed.rowCount) :
    Agrees (schema fields) observed (ofObserved fields observed ordered aligned) :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Events.ofObserved_agrees fields observed ordered aligned

/-- Positional projection preserves the native row count and the selected
declarations and slots, including repeated positions and width zero. -/
theorem Agrees.project {signature : Signature} {observed : Observed} {event : Batch signature}
    (agrees : Agrees signature observed event) (projection : Scan.Projection signature) :
    Projects projection observed (projection.projectColumns event) :=
  ⟨agrees.1, fun i => agrees.2.2 (projection.index i)⟩

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events
