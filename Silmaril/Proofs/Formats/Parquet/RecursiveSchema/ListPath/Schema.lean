module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath

open Silmaril.Formats
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.Repeated (Context Step)

public theorem path_extent {reader : ThriftCompact.Traversal.Reader}
    {original : Array Parquet.RecursiveSchema.Entry} {fuel ordinal stop : Nat}
    {ctx : Context} {shape : Shape} (wire : PathWire reader original fuel ctx ordinal shape stop) :
    stop = ordinal + 2 * shape.repetitions + 1 ∧ 2 * shape.repetitions + 1 ≤ fuel := by
  induction wire with
  | signed => simp [Shape.repetitions]
  | list _ _ ih =>
    simp only [Shape.repetitions]
    omega

public theorem steps_length (shape : Shape) (ctx : Context) :
    (shape.steps ctx).length = ctx.steps.length + shape.definitions := by
  induction shape generalizing ctx with
  | signed site kind =>
    cases h : site.nullable <;> simp [Shape.steps, Shape.definitions, Context.enter, h]
  | list node child ih =>
    rw [Shape.steps, ih]
    cases h : node.site.nullable <;>
      simp [Shape.definitions, Parquet.RecursiveSchema.TwoList.ListSite.enter, Context.enterList, h, Nat.add_assoc]

public theorem steps_prefix (shape : Shape) (ctx : Context) :
    ctx.steps <+: shape.steps ctx := by
  induction shape generalizing ctx with
  | signed site kind =>
    cases h : site.nullable <;> simp [Shape.steps, Context.enter, h]
  | list node child ih =>
    rw [Shape.steps]
    have parent : ctx.steps <+: (node.enter ctx).steps := by
      cases h : node.site.nullable <;>
        simp [Parquet.RecursiveSchema.TwoList.ListSite.enter, Context.enterList, h, List.append_assoc]
    exact parent.trans (ih _)

public theorem list_stops (node : Parquet.RecursiveSchema.TwoList.ListSite) (child : Shape) (ctx : Context) :
    let all := (Shape.list node child).steps ctx
    all[ctx.steps.length + node.site.nullable.toNat]? = some (.emptyList node.site.location node.wrapper) ∧
      (node.site.nullable = true →
        all[ctx.steps.length]? = some (.optional node.site.location .list)) := by
  obtain ⟨tail, more⟩ := steps_prefix child (node.enter ctx)
  simp only [Shape.steps]
  rw [← more]
  cases h : node.site.nullable <;>
    simp [Parquet.RecursiveSchema.TwoList.ListSite.enter, Context.enterList, h, List.append_assoc]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath
