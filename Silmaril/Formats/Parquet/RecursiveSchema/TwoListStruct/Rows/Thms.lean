module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Alignment
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Typing

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows

open Arrow.RecursiveSchema.Batch.Rows (Row RowFits)

public section

theorem addressed_atoms (address : RecursiveSchema.Chunk.Address) (observed : ListPath.Chunk.Observation) :
    (addressed address observed).map Addressed.atom = observed.atoms :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.addressed_atoms address observed

theorem addressed_slot {address : RecursiveSchema.Chunk.Address}
    {observed : ListPath.Chunk.Observation} {slot : Addressed}
    (member : slot ∈ addressed address observed) :
    ∃ page ordinal indexInPage,
      observed.pages[ordinal]? = some page ∧ page.decoded.atoms[indexInPage]? = some slot.atom ∧
      slot.point = ⟨address, observed.dictionary.isSome.toNat + ordinal, page.frame.header.start,
        page.start.slots + indexInPage⟩ :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.addressed_slot member

theorem checkTopology_wire {ceiling start : Nat} {left right : RecursiveSchema.Chunk.Address}
    {lhs rhs : List Addressed} (read : checkTopology ceiling left right lhs rhs start = .ok ()) :
    TopologyWire ceiling lhs rhs :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.topology_wire read

theorem checkTopology_failure {ceiling start : Nat} {left right : RecursiveSchema.Chunk.Address}
    {lhs rhs : List Addressed} {cause : TopologyError}
    (read : checkTopology ceiling left right lhs rhs start = .error cause) :
    TopologyFailure ceiling left right lhs rhs start cause :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.topology_failure read

theorem mergeRows_wire {optional : Bool} {lhs rhs out : List Row}
    (read : mergeRows lhs rhs optional = some out) :
    ∀ side, projectRows side out optional = some (side.select lhs rhs) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.mergeRows_wire read

theorem mergeRows_typed {plan : Plan} {lhs rhs out : List Row}
    (merged : mergeRows lhs rhs plan.element.nullable = some out)
    (first : ∀ row ∈ lhs, RowFits (plan.path .left).arrow.fields row)
    (other : ∀ row ∈ rhs, RowFits (plan.path .right).arrow.fields row) :
    ∀ row ∈ out, RowFits plan.arrow.fields row :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.mergeRows_typed merged first other

theorem projectRows_count {side : Side} {optional : Bool} {rows out : List Row}
    (read : projectRows side rows optional = some out) : out.length = rows.length :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.projectRows_count read

theorem projectRows_demand {plan : Plan} {side : Side} {rows projected : List Row}
    (read : projectRows side rows plan.element.nullable = some projected) :
    ListPath.Rows.slotDemand (plan.path side) projected = slotDemand rows :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.projectRows_demand read

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
