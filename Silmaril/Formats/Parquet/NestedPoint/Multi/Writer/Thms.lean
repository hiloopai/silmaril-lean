module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Writer.Correctness

public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi.Writer

/-- The emitted level pairs classify exactly as the original required
and optional leaf bindings. -/
theorem levelPair_contract (row : NestedPoint.Row) :
    let (left, right) := PageEncoding.levelPair row
    left ≤ Multi.Kind.signed.child.maxDefinition ∧
    right ≤ Multi.Kind.wide.child.maxDefinition ∧
    NestedPresence.classify Multi.Kind.signed.child left =
      (if row.isSome then .value else .parentAbsent) ∧
    NestedPresence.classify Multi.Kind.wide.child right =
      (match row with | none => .parentAbsent | some (_, none) => .childNull | some (_, some _) => .value) :=
  Proofs.Formats.Parquet.NestedPoint.Multi.Writer.levelPair_contract row

/-- Successful native output recovers the exact footer, original ordered
logical groups and complete typed NestedPoint Events. -/
theorem emit_readback {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) : Readback limits input output :=
  Proofs.Formats.Parquet.NestedPoint.Multi.Writer.emit_readback written

end Silmaril.Formats.Parquet.NestedPoint.Multi.Writer
