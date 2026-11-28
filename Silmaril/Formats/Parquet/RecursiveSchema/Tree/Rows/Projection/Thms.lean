module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Typing

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection

open Arrow.RecursiveSchema.Batch.Rows (Row RowFits)

public section

/-- An accepted physical projection certifies the recursive Arrow cells
against the same schema from which it derives the signed leaf traces. -/
theorem trace_typed {widths : Array Nat} {fieldCount depth : Nat} {schema : List Repeated.Field}
    {rows : List Row} {out : Traces} (accepted : trace widths fieldCount depth schema rows = some out) :
    ∀ row ∈ rows, RowFits (schema.map Repeated.Field.arrow) row :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.trace_typed accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection
