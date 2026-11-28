module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

/-! Align original slots across both repeated ancestors before assembling
a required Struct from the independently checked signed child rows. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows

open ListPath.Rows (Atom)
open RecursiveSchema.Chunk (Address)
open Repeated.Rows (Point)
open Arrow.RecursiveSchema.Batch.Rows (Cell Row)

@[expose] public section

structure Addressed where
  point : Point
  atom : Atom
  deriving Repr

def addressed (address : Address) (observed : ListPath.Chunk.Observation) : List Addressed :=
  observed.pages.zipIdx.flatMap fun (page, ordinal) =>
    page.decoded.atoms.zipIdx page.start.slots |>.map fun (atom, slot) =>
      ⟨⟨address, ordinal, page.frame.header.start, slot⟩, atom⟩

def commonLevels (ceiling : Nat) (slot : Addressed) : Nat × Nat :=
  (slot.atom.repetition, min slot.atom.definition ceiling)

inductive TopologyError where
  | missing (slot : Nat) (column : Address) (counterpart : Point)
  | conflict (slot : Nat) (left right : Point) (leftLevels rightLevels : Nat × Nat)
  deriving DecidableEq, Repr

/-- Compare only shared definition steps while keeping exact repetition.
Check the complete ordered traces, independent of the original page cuts. -/
def checkTopology (ceiling : Nat) (left right : Address) :
    List Addressed → List Addressed → Nat → Except TopologyError Unit
  | [], [], _ => .ok ()
  | [], other :: _, slot => .error (.missing slot left other.point)
  | first :: _, [], slot => .error (.missing slot right first.point)
  | first :: moreLeft, other :: moreRight, slot =>
    if commonLevels ceiling first = commonLevels ceiling other then
      checkTopology ceiling left right moreLeft moreRight (slot + 1)
    else .error (.conflict slot first.point other.point
      (commonLevels ceiling first) (commonLevels ceiling other))

def TopologyWire (ceiling : Nat) (left right : List Addressed) : Prop :=
  List.Forall₂ (fun first other => commonLevels ceiling first = commonLevels ceiling other) left right

/-- The matched prefix is checked in wire order. A refusal carries the
exact reached coordinate of each available original slot. -/
inductive TopologyFailure (ceiling : Nat) (left right : Address) :
    List Addressed → List Addressed → Nat → TopologyError → Prop where
  | missingLeft {other rest slot} :
      TopologyFailure ceiling left right [] (other :: rest) slot (.missing slot left other.point)
  | missingRight {first rest slot} :
      TopologyFailure ceiling left right (first :: rest) [] slot (.missing slot right first.point)
  | conflict {first other lhs rhs slot} :
      commonLevels ceiling first ≠ commonLevels ceiling other →
      TopologyFailure ceiling left right (first :: lhs) (other :: rhs) slot
        (.conflict slot first.point other.point (commonLevels ceiling first) (commonLevels ceiling other))
  | next {first other lhs rhs slot cause} :
      commonLevels ceiling first = commonLevels ceiling other →
      TopologyFailure ceiling left right lhs rhs (slot + 1) cause →
      TopologyFailure ceiling left right (first :: lhs) (other :: rhs) slot cause

def pairMap {α β γ : Type} (f : α → β → Option γ) (left : List α) (right : List β) :
    Option (List γ) :=
  if left.length = right.length then List.zipWithM f left right else none

/-- Both paths have two LIST layers and a common required Struct.
Retain null and empty LISTs at each layer when merging the signed rows. -/
def mergeCell : Nat → Cell → Cell → Option Cell
  | 0, first, other => some (some (.struct [first, other]))
  | _ + 1, none, none => some none
  | depth + 1, some (.list left), some (.list right) =>
    (pairMap (mergeCell depth) left right).map (fun cells => some (.list cells))
  | _, _, _ => none

def projectCell (side : Side) : Nat → Cell → Option Cell
  | 0, some (.struct [first, other]) => some (side.select first other)
  | _ + 1, none => some none
  | depth + 1, some (.list values) =>
    (values.mapM (projectCell side depth)).map (fun cells => some (.list cells))
  | _, _ => none

def mergeRow : Row → Row → Option Row
  | [first], [other] => (mergeCell 2 first other).map (fun cell => [cell])
  | _, _ => none

def projectRow (side : Side) : Row → Option Row
  | [value] => (projectCell side 2 value).map (fun cell => [cell])
  | _ => none

def mergeRows (left right : List Row) : Option (List Row) := pairMap mergeRow left right

def projectRows (side : Side) (rows : List Row) : Option (List Row) := rows.mapM (projectRow side)

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
