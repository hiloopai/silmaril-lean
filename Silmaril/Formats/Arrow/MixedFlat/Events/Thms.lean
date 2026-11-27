module

public import Silmaril.Formats.Arrow.MixedFlat.Events.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Events.Shape

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Events

/-- Every decoded column has one nullable slot per declared row. -/
theorem readGroup_length {limits : BinaryView.Column.Limits} {body : KBytes} {rows : Nat}
    {group : Group rows} {column : MixedFlat.Column}
    (read : readGroup limits body group = .ok column) : (cells column).length = rows :=
  Proofs.Formats.Arrow.MixedFlat.Events.readGroup_length read

/-- The decoder's successful output is in schema order with exactly one
nullable slot per row at every field. -/
theorem readParsed_shape {limits : MixedFlat.Limits} {body : KBytes}
    {fields : List MixedFlat.Field} {metadata : MixedFlat.Metadata} {observed : MixedFlat.Observed}
    (parsed : MixedFlat.readParsed limits fields metadata body = .ok observed) :
    observed.columns.map Prod.fst = fields ∧
      ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount :=
  Proofs.Formats.Arrow.MixedFlat.Events.readParsed_shape parsed

theorem ofObserved_agrees (fields : List MixedFlat.Field) (observed : MixedFlat.Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount) :
    Agrees (schema fields) observed (ofObserved fields observed ordered aligned) :=
  Proofs.Formats.Arrow.MixedFlat.Events.ofObserved_agrees fields observed ordered aligned

end Silmaril.Formats.Arrow.MixedFlat.Events
