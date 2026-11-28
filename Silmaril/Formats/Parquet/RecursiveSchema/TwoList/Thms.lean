module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Levels

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList

public section

/-- The empty levels come from the two canonical repeated wrappers in order.
Each original OPTIONAL marker adds one definition step. -/
theorem Plan.thresholds (plan : Plan) :
    plan.outerEmpty = plan.outer.site.nullable.toNat ∧
    plan.innerEmpty = plan.outerEmpty + 1 + plan.inner.site.nullable.toNat ∧
    plan.maxDefinition = plan.innerEmpty + 1 + plan.leaf.nullable.toNat :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.thresholds plan

theorem Source.bytes_exact {limits : Snapshot.Limits} {bytes : Bytes} (source : Source limits bytes) :
    source.snapshot.bytes = bytes :=
  Snapshot.check_bytes source.original

theorem Plan.wrapperSteps (plan : Plan) :
    plan.steps[plan.outerEmpty]? = some (.emptyList plan.outer.site.location plan.outer.wrapper) ∧
    plan.steps[plan.innerEmpty]? = some (.emptyList plan.inner.site.location plan.inner.wrapper) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.wrapper_steps plan

theorem Plan.presence_iff {plan : Plan} {definition : Nat} {presence : Presence} :
    plan.presence definition = some presence ↔ DefinitionWire plan definition presence :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.presence_iff

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList
