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

end

public def emit (columns : Traces) (atColumn : Nat) (atom : Atom) : Option Traces :=
  if atColumn < columns.size then some (columns.modify atColumn (atom :: ·)) else none

public def markers (atom : Atom) : Nat → Nat → Traces → Option Traces
  | 0, _, columns => some columns
  | count + 1, atColumn, columns => do
    markers atom count (atColumn + 1) (← emit columns atColumn atom)

@[expose] public def fields (project : Repeated.Field → Nat → Cell → Traces → Option Traces)
    (widths : Array Nat) : List Repeated.Field → List Cell → Nat → Traces → Option Traces
  | [], [], _, columns => some columns
  | field :: tail, value :: rest, atColumn, columns => do
    let projected ← project field atColumn value columns
    fields project widths tail rest (atColumn + width widths field) projected
  | _, _, _, _ => none

@[expose] public def cell (widths : Array Nat) :
    Nat → Levels → Repeated.Field → Nat → Cell → Traces → Option Traces
  | 0, _, _, _, _, _ => none
  | fuel + 1, levels, field, atColumn, value, columns => do
    match field with
    | .leaf plan =>
      match value with
      | none =>
        if plan.site.nullable then emit columns atColumn ⟨levels.repetition, levels.definition, none⟩ else none
      | some _ =>
        let word ← signedWord plan.kind value
        emit columns atColumn ⟨levels.repetition, levels.definition + plan.site.nullable.toNat, some word⟩
    | .group site children =>
      match value with
      | none =>
        if site.nullable then
          markers ⟨levels.repetition, levels.definition, none⟩ (width widths field) atColumn columns
        else none
      | some (.struct values) =>
        let inside := { levels with definition := levels.definition + site.nullable.toNat }
        fields (cell widths fuel inside) widths children values atColumn columns
      | _ => none
    | .list site _ element =>
      let empty := levels.definition + site.nullable.toNat
      match value with
      | none =>
        if site.nullable then
          markers ⟨levels.repetition, levels.definition, none⟩ (width widths field) atColumn columns
        else none
      | some (.list []) => markers ⟨levels.repetition, empty, none⟩ (width widths field) atColumn columns
      | some (.list (first :: tail)) =>
        let inside : Levels := ⟨empty + 1, levels.repetition, levels.depth + 1⟩
        let head ← cell widths fuel inside element atColumn first columns
        let later := { inside with repetition := inside.depth }
        tail.foldlM (fun traced value => cell widths fuel later element atColumn value traced) head
      | _ => none

/-- Regenerate every leaf trace from the logical shape and cells alone.
The original decoder's atoms and addresses are absent from this input. -/
@[expose] public def trace (widths : Array Nat) (fieldCount depth : Nat) (schema : List Repeated.Field)
    (rows : List Row) : Option Traces := do
  let reversed ← rows.foldlM
    (fun columns row => fields (cell widths depth {}) widths schema row 0 columns)
    (Array.replicate fieldCount [])
  return reversed.map List.reverse

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection
