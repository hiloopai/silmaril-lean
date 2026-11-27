module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs

/-! Project a logical row into original leaf order using the compiled
schema. The projection does not consume observations or source addresses. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows

open Arrow.RecursiveSchema.Batch.Rows (Cell Row)
open RecursiveSchema (Site)
open Repeated (Field Leaf Step Absence Presence)

@[expose] public section

structure Atom where
  levels : Chunk.LevelSlot
  word : Option Chunk.Word
  deriving DecidableEq, Repr

instance : BEq Atom where
  beq a b := decide (a = b)

instance : LawfulBEq Atom where
  eq_of_beq := of_decide_eq_true
  rfl := decide_eq_true rfl

namespace Projection

/-- The element cursor determines the original repetition bit and the
role of an optional declaration within the single repeated ancestor. -/
structure Position where
  repetition : Nat := 0
  role : Absence := .node

def Position.child (position : Position) : Position :=
  if position.role = .element then { position with role := .descendant } else position

def atom (position : Position) (definition : Nat) (presence : Presence) (word : Option Chunk.Word) :
    Atom :=
  let boundary := if position.repetition = 0 then Repeated.Position.rowStart else .continuation
  ⟨⟨position.repetition, definition, ⟨boundary, presence⟩⟩, word⟩

def absent (position : Position) (step : Step) (leaves : List Leaf) : Option (List (List Atom)) :=
  leaves.mapM fun leaf => do
    let level ← leaf.steps.findIdx? (fun original => decide (original = step))
    return [atom position level (.absent step) none]

def missing (position : Position) (site : Site) (leaves : List Leaf) : Option (List (List Atom)) :=
  if site.nullable then absent position (.optional site.location position.role) leaves else none

def fields (project : Field → Cell → Option (List (List Atom))) :
    List Field → Row → Option (List (List Atom))
  | [], [] => some []
  | field :: rest, cell :: cells => do
    let first ← project field cell
    let tail ← fields project rest cells
    return first ++ tail
  | _, _ => none

/-- Accumulate in reverse within each physical column. Each element's
projection is appended in positional leaf order, including null slots. -/
def elements (project : Position → Cell → Option (List (List Atom))) (width : Nat)
    (cells : List Cell) : Option (List (List Atom)) := do
  let reversed ← (cells.zipIdx).foldlM (fun columns (cell, index) => do
    let next ← project ⟨if index = 0 then 0 else 1, .element⟩ cell
    if next.length = width then
      return List.zipWith (fun accumulated slots => slots.reverse ++ accumulated) columns next
    else none) (List.replicate width [])
  return reversed.map List.reverse

def cell : Nat → Position → Field → Cell → Option (List (List Atom))
  | 0, _, _, _ => none
  | depth + 1, position, field, value =>
    match field, value with
    | .leaf plan, none => missing position plan.site [plan]
    | .leaf plan, some (.int32 word) =>
      if plan.kind = .int32 then some [[atom position plan.maxDefinition .value (some (.int32 word))]]
      else none
    | .leaf plan, some (.int64 word) =>
      if plan.kind = .int64 then some [[atom position plan.maxDefinition .value (some (.int64 word))]]
      else none
    | .group site children, none => missing position site (children.flatMap Field.leaves)
    | .group _ children, some (.struct row) =>
      fields (cell depth position.child) children row
    | .list site _ element, none =>
      missing { position with role := .list } site element.leaves
    | .list site wrapper element, some (.list []) =>
      absent position (.emptyList site.location wrapper) element.leaves
    | .list _ _ element, some (.list (first :: rest)) =>
      elements (fun pos => cell depth pos element) element.leaves.length (first :: rest)
    | _, _ => none

/-- Independently restore the original per-column slot sequences for a
logical row, including both level words and the original signed values. -/
def row (depth : Nat) (schema : List Field) (value : Row) : Option (List (List Atom)) :=
  fields (cell depth {}) schema value

end Projection

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
