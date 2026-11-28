module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList

open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Context)

public theorem thresholds (plan : Plan) :
    plan.outerEmpty = plan.outer.site.nullable.toNat ∧
    plan.innerEmpty = plan.outerEmpty + 1 + plan.inner.site.nullable.toNat ∧
    plan.maxDefinition = plan.innerEmpty + 1 + plan.leaf.nullable.toNat := by
  cases outer : plan.outer.site.nullable <;> cases inner : plan.inner.site.nullable <;>
    cases leaf : plan.leaf.nullable <;>
    simp [Plan.outerEmpty, Plan.innerEmpty, Plan.maxDefinition, Plan.steps, Plan.innerContext,
      Plan.outerContext, ListSite.enter, Context.enterList, Context.enter, outer, inner, leaf]

public theorem wrapper_steps (plan : Plan) :
    plan.steps[plan.outerEmpty]? = some (.emptyList plan.outer.site.location plan.outer.wrapper) ∧
    plan.steps[plan.innerEmpty]? = some (.emptyList plan.inner.site.location plan.inner.wrapper) := by
  cases outer : plan.outer.site.nullable <;> cases inner : plan.inner.site.nullable <;>
    cases leaf : plan.leaf.nullable <;>
    simp [Plan.outerEmpty, Plan.innerEmpty, Plan.steps, Plan.innerContext, Plan.outerContext,
      ListSite.enter, Context.enterList, Context.enter, outer, inner, leaf]

public theorem presence_iff {plan : Plan} {definition : Nat} {presence : Presence} :
    plan.presence definition = some presence ↔ DefinitionWire plan definition presence := by
  obtain ⟨outerEq, innerEq, maximumEq⟩ := thresholds plan
  cases outer : plan.outer.site.nullable <;> cases inner : plan.inner.site.nullable <;>
    cases leaf : plan.leaf.nullable <;> cases presence <;>
    simp [Plan.presence, DefinitionWire, maximumEq, innerEq, outerEq, outer, inner, leaf] <;>
    (repeat' split) <;> simp_all <;> omega

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList
