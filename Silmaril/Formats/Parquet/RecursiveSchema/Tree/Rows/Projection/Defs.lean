module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Occurrences.Defs

/-! Project logical rows to canonical physical leaf traces. Column
accumulators append in reverse to keep projection linear in emitted slots. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection

open RecursiveSchema.ListPath.Rows (Atom signedWord)
open Arrow.RecursiveSchema.Batch.Rows (Cell Row)
open Occurrences (width)

@[expose] public section

structure Levels where
  definition : Nat := 0
  repetition : Nat := 0
  depth : Nat := 0

abbrev Traces := Array (List Atom)
abbrev Push (State : Type) := State → Nat → Atom → Option State

end

public def emit (columns : Traces) (atColumn : Nat) (atom : Atom) : Option Traces :=
  if atColumn < columns.size then some (columns.modify atColumn (atom :: ·)) else none

public def markers {State : Type} (append : Push State) (atom : Atom) :
    Nat → Nat → State → Option State
  | 0, _, columns => some columns
  | count + 1, atColumn, columns => do
    markers append atom count (atColumn + 1) (← append columns atColumn atom)

@[expose] public def fields {State : Type}
    (project : Repeated.Field → Nat → Cell → State → Option State)
    (widths : Array Nat) : List Repeated.Field → List Cell → Nat → State → Option State
  | [], [], _, columns => some columns
  | field :: tail, value :: rest, atColumn, columns => do
    let projected ← project field atColumn value columns
    fields project widths tail rest (atColumn + width widths field) projected
  | _, _, _, _ => none

@[expose] public def cell {State : Type} (append : Push State) (widths : Array Nat) :
    Nat → Levels → Repeated.Field → Nat → Cell → State → Option State
  | 0, _, _, _, _, _ => none
  | fuel + 1, levels, field, atColumn, value, columns => do
    match field with
    | .leaf plan =>
      match value with
      | none =>
        if plan.site.nullable then append columns atColumn ⟨levels.repetition, levels.definition, none⟩ else none
      | some _ =>
        let word ← signedWord plan.kind value
        append columns atColumn ⟨levels.repetition, levels.definition + plan.site.nullable.toNat, some word⟩
    | .group site children =>
      match value with
      | none =>
        if site.nullable then
          markers append ⟨levels.repetition, levels.definition, none⟩ (width widths field) atColumn columns
        else none
      | some (.struct values) =>
        let inside := { levels with definition := levels.definition + site.nullable.toNat }
        fields (cell append widths fuel inside) widths children values atColumn columns
      | _ => none
    | .list site _ element =>
      let empty := levels.definition + site.nullable.toNat
      match value with
      | none =>
        if site.nullable then
          markers append ⟨levels.repetition, levels.definition, none⟩ (width widths field) atColumn columns
        else none
      | some (.list []) => markers append ⟨levels.repetition, empty, none⟩ (width widths field) atColumn columns
      | some (.list (first :: tail)) =>
        let inside : Levels := ⟨empty + 1, levels.repetition, levels.depth + 1⟩
        let head ← cell append widths fuel inside element atColumn first columns
        let later := { inside with repetition := inside.depth }
        tail.foldlM (fun traced value => cell append widths fuel later element atColumn value traced) head
      | _ => none

@[expose] public def fold {State : Type} (append : Push State) (widths : Array Nat)
    (depth : Nat) (schema : List Repeated.Field) (rows : List Row) (initial : State) : Option State :=
  rows.foldlM (fun columns row => fields (cell append widths depth {}) widths schema row 0 columns) initial

/-- Count the physical demand on each original leaf before retaining any slot
arrays. The count uses the same traversal and cell checks as the trace. -/
public def counts (widths : Array Nat) (fieldCount depth : Nat) (schema : List Repeated.Field)
    (rows : List Row) : Option (Array Nat) :=
  fold (fun slots column _ =>
    if column < slots.size then some (slots.modify column (· + 1)) else none)
    widths depth schema rows (Array.replicate fieldCount 0)

/-- Regenerate every leaf trace from the logical shape and cells alone.
The original decoder's atoms and addresses are absent from this input. -/
@[expose] public def trace (widths : Array Nat) (fieldCount depth : Nat) (schema : List Repeated.Field)
    (rows : List Row) : Option Traces := do
  let reversed ← fold emit widths depth schema rows (Array.replicate fieldCount [])
  return reversed.map List.reverse

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection
