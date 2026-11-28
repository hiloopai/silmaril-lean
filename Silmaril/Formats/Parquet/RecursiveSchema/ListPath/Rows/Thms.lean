module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.Projection
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.Reconstruct

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows

open Arrow.RecursiveSchema.Batch.Rows (Observation Row RowFits)

public section

theorem Relation.typedWords {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) :
    (∀ row ∈ rows, RowFits plan.arrow.fields row) ∧
      rows.flatMap (rowWords plan) = input.filterMap Atom.word :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.relation_sound relation

theorem project_wire {limits : Limits} {plan : Plan} {rows : List Row} {input : List Atom}
    (accepted : project limits plan rows = .ok input) :
    Relation plan input rows ∧ rows.length ≤ limits.maxRows ∧ input.length ≤ limits.maxSlots :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.project_wire accepted

/-- Successful reconstruction certifies the exact original repetition,
definition, and aligned-word trace and the checked original row count. -/
theorem reconstruct_wire {limits : Limits} {plan : Plan} {expected : Nat}
    {input : List Atom} {out : Observation}
    (accepted : reconstruct limits plan expected input = .ok out) :
    ObservationWire limits plan input expected out :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.reconstruct_wire accepted

/-- An independently projected trace determines its original rows. The
decoder recovers them under the corresponding row and slot budgets. -/
theorem reconstruct_of_relation {limits : Limits} {plan : Plan} {input : List Atom} {rows : List Row}
    (original : Relation plan input rows) (budgetRows : rows.length ≤ limits.maxRows)
    (budgetSlots : input.length ≤ limits.maxSlots) :
    reconstruct limits plan rows.length input = .ok ⟨rows.length, rows⟩ :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.reconstruct_of_relation original budgetRows budgetSlots

theorem Relation.slotDemand {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) : slotDemand plan rows = input.length :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.relation_demand relation

theorem project_of_relation {limits : Limits} {plan : Plan} {input : List Atom} {rows : List Row}
    (original : Relation plan input rows) (budgetRows : rows.length ≤ limits.maxRows)
    (budgetSlots : input.length ≤ limits.maxSlots) : project limits plan rows = .ok input :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.project_of_relation original budgetRows budgetSlots

theorem project_reconstruct {limits : Limits} {plan : Plan} {rows : List Row} {input : List Atom}
    (accepted : project limits plan rows = .ok input) :
    reconstruct limits plan rows.length input = .ok ⟨rows.length, rows⟩ := by
  obtain ⟨original, rowBudget, slotBudget⟩ := project_wire accepted
  exact reconstruct_of_relation original rowBudget slotBudget

theorem reconstruct_project {limits : Limits} {plan : Plan} {expected : Nat} {input : List Atom}
    {out : Observation} (accepted : reconstruct limits plan expected input = .ok out) :
    project limits plan out.rows = .ok input := by
  have wire := reconstruct_wire accepted
  exact project_of_relation wire.original (wire.count ▸ wire.rowBudget) wire.slotBudget

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows
