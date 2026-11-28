module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Schema

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath

public section

theorem Source.bytes_exact {limits : Snapshot.Limits} {input : Bytes} (source : Source limits input) :
    source.snapshot.bytes = input :=
  Snapshot.check_bytes source.original

/-- The original preorder consumes two entries per LIST and one per leaf
after the single root entry. -/
theorem PathWire.extent {reader : ThriftCompact.Traversal.Reader}
    {original : Array RecursiveSchema.Entry} {fuel ordinal stop : Nat}
    {ctx : Repeated.Context} {shape : Shape} (wire : PathWire reader original fuel ctx ordinal shape stop) :
    stop = ordinal + 2 * shape.repetitions + 1 ∧ 2 * shape.repetitions + 1 ≤ fuel :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.path_extent wire

theorem Shape.steps_length (shape : Shape) (ctx : Repeated.Context) :
    (shape.steps ctx).length = ctx.steps.length + shape.definitions :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.steps_length shape ctx

/-- These are the same thresholds used by the logical projection. A
required LIST lacks the optional step, while every wrapper has an empty level. -/
theorem Shape.list_stops (node : TwoList.ListSite) (child : Shape) (ctx : Repeated.Context) :
    let all := (Shape.list node child).steps ctx
    all[ctx.steps.length + node.site.nullable.toNat]? = some (.emptyList node.site.location node.wrapper) ∧
      (node.site.nullable = true →
        all[ctx.steps.length]? = some (.optional node.site.location .list)) :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.list_stops node child ctx

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath
