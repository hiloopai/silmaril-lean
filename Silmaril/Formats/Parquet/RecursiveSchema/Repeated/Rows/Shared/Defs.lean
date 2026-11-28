module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

/-! Common topology for two signed physical leaves under one LIST of Structs. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows

open RecursiveSchema (Location Site)
open Repeated (Compiled Step)
open Arrow.RecursiveSchema.Batch.Rows (Row Observation)

@[expose] public section

/-- The definition steps owned by the common LIST and its element Struct. -/
def sharedSteps (outer : Site) (wrapper : Location) (element : Site) : List Step :=
  (if outer.nullable then [.optional outer.location .list] else []) ++
    [.emptyList outer.location wrapper] ++
    (if element.nullable then [.optional element.location .element] else [])

def childSteps (child : Site) : List Step :=
  if child.nullable then [.optional child.location .descendant] else []

/-- Keep repetition and every shared absence. A definition at or above
the ceiling reaches the shared Struct, irrespective of child presence. -/
def commonLevels (ceiling : Nat) (slot : Atom) : Nat × Nat :=
  (slot.levels.repetition, min slot.levels.definition ceiling)

def SharedTopology (ceiling : Nat) (left right : List Atom) : Prop :=
  left.map (commonLevels ceiling) = right.map (commonLevels ceiling)

structure SharedRowWire (depth : Nat) (position : Position) (fields : List Repeated.Field)
    (ceiling : Nat) (left right : Column) (row : Row) : Prop where
  original : ∃ lhs rhs, left.at position = .ok lhs ∧ right.at position = .ok rhs ∧
    Projection.row depth fields row = some [lhs.atoms, rhs.atoms] ∧
    SharedTopology ceiling lhs.atoms rhs.atoms

/-- Both physical columns retain their independent original chunk and row
witnesses. Their slices agree at the shared ceiling and keep the full
per-child levels and signed words in the exact projection. -/
structure ListStructWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group ceiling : Nat)
    (result : Observation) : Prop where
  original : ∃ rowGroup left right,
    snapshot.groupAt group = some rowGroup ∧ result.rowCount = rowGroup.numRows.toNat ∧
    ColumnWire limits.chunk schema group 0 left ∧ ColumnWire limits.chunk schema group 1 right ∧
    List.Forall₂ (fun index row => SharedRowWire (schemaLimits.maxSchemaDepth - 1)
      ⟨group, index, none⟩ schema.fields ceiling left right row)
      (List.range rowGroup.numRows.toNat) result.rows

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
