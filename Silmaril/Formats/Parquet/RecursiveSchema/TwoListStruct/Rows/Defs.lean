module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

/-! Align original slots across both repeated ancestors before assembling
a Struct from the independently checked signed child rows. -/

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

/-- Data-page slots carry their ordinal in the original chunk, including a leading dictionary. -/
def addressed (address : Address) (observed : ListPath.Chunk.Observation) : List Addressed :=
  (observed.pages.zipIdx observed.dictionary.isSome.toNat).flatMap fun (page, ordinal) =>
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

/-- For an optional element the two unary child projections carry
presence independently of the nullability of their signed values. -/
def mergeElement (optional : Bool) (left right : Cell) : Option Cell :=
  if optional then
    match left, right with
    | none, none => some none
    | some (.struct [first]), some (.struct [other]) => some (some (.struct [first, other]))
    | _, _ => none
  else some (some (.struct [left, right]))

def projectElement (side : Side) : Bool → Cell → Option Cell
  | false, some (.struct [first, other]) => some (side.select first other)
  | true, some (.struct [first, other]) => some (some (.struct [side.select first other]))
  | true, none => some none
  | _, _ => none

def mergeCell (optional : Bool) : Nat → Cell → Cell → Option Cell
  | 0, first, other => mergeElement optional first other
  | _ + 1, none, none => some none
  | depth + 1, some (.list left), some (.list right) =>
    (pairMap (mergeCell optional depth) left right).map (fun cells => some (.list cells))
  | _, _, _ => none

def projectCell (side : Side) (optional : Bool) : Nat → Cell → Option Cell
  | 0, value => projectElement side optional value
  | _ + 1, none => some none
  | depth + 1, some (.list values) =>
    (values.mapM (projectCell side optional depth)).map (fun cells => some (.list cells))
  | _, _ => none

def mergeRow (optional : Bool) : Row → Row → Option Row
  | [first], [other] => (mergeCell optional 2 first other).map (fun cell => [cell])
  | _, _ => none

def projectRow (side : Side) (optional : Bool) : Row → Option Row
  | [value] => (projectCell side optional 2 value).map (fun cell => [cell])
  | _ => none

def mergeRows (left right : List Row) (optional : Bool := false) : Option (List Row) :=
  pairMap (mergeRow optional) left right

def projectRows (side : Side) (rows : List Row) (optional : Bool := false) : Option (List Row) :=
  rows.mapM (projectRow side optional)

/-- Every null or empty LIST marker and every Struct element, including
a null Struct, contributes one slot to each physical column. -/
def cellDemand : Nat → Cell → Nat
  | depth + 1, some (.list (first :: rest)) =>
    cellDemand depth first + ListPath.Rows.sumDemand (cellDemand depth) rest
  | _, _ => 1

def rowDemand : Row → Nat
  | [value] => cellDemand 2 value
  | _ => 0

def slotDemand (rows : List Row) : Nat := ListPath.Rows.sumDemand rowDemand rows

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
