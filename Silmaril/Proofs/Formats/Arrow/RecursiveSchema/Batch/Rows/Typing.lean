module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows

open Silmaril.Formats.Arrow.RecursiveSchema (Field)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics (Column ColumnWire ColumnsWire)

private def BoundColumn (body : KBytes) (column : Column) (field : Field) : Prop :=
  ∃ visible layout, ColumnWire body visible field layout column

private theorem boundColumns {body : KBytes} {visible fields layouts columns}
    (wire : ColumnsWire body visible fields layouts columns) :
    List.Forall₂ (BoundColumn body) columns fields := by
  induction fields generalizing layouts columns with
  | nil => cases wire; exact .nil
  | cons field fields ih =>
    cases wire with
    | cons head tail => exact .cons ⟨_, _, head⟩ (ih tail)

private theorem cells_length {positions : List (Column × Nat)} {values : Row}
    (wire : CellsWire positions values) : values.length = positions.length := by
  induction positions generalizing values with
  | nil => cases wire; rfl
  | cons _ _ ih =>
    cases wire with
    | cons _ tail => simp [ih tail]

private theorem repeated {body : KBytes} {column : Column} {field : Field}
    (bound : BoundColumn body column field) (indices : List Nat) :
    List.Forall₂ (fun entry : Column × Nat => BoundColumn body entry.1)
      (indices.map fun i => (column, i)) (List.replicate indices.length field) := by
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons bound ih

theorem cells_typed {body : KBytes} {visible fields layouts columns row slot}
    (physical : ColumnsWire body visible fields layouts columns)
    (logical : CellsWire (columns.map fun column => (column, slot)) row) :
    RowFits fields row := by
  apply CellsWire.rec
    (motive_1 := fun column _ value _ => ∀ field, BoundColumn body column field → CellFits field value)
    (motive_2 := fun positions values _ =>
      ∀ fields, List.Forall₂ (fun entry : Column × Nat => BoundColumn body entry.1) positions fields →
      RowFits fields values) _ _ _ _ _ _ _ logical fields ?_
  · intro presence payload children slot reached invalid field aligned
    obtain ⟨name, nullable, kind, fields⟩ := field
    obtain ⟨visible, layout, physical⟩ := aligned
    cases physical with
    | node bits payload children =>
      cases nullable with
      | true => exact .null
      | false =>
        obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp reached
        rw [bits.fromAncestors, bits.visibilityLength] at bound
        have admitted := bits.required_at bound reached
        rw [invalid] at admitted
        contradiction
  · intro presence words children slot word present original field aligned
    obtain ⟨visible, layout, physical⟩ := aligned
    cases physical with
    | node bits payload children =>
      cases payload
      exact .int32
  · intro presence words children slot word present original field aligned
    obtain ⟨visible, layout, physical⟩ := aligned
    cases physical with
    | node bits payload children =>
      cases payload
      exact .int64
  · intro presence children slot values present cellWire ih field aligned
    obtain ⟨visible, layout, physical⟩ := aligned
    cases physical with
    | node bits payload childrenWire =>
      cases payload
      apply CellFits.struct
      apply ih
      rw [List.forall₂_map_left_iff]
      exact boundColumns childrenWire
  · intro presence offsets child slot lo hi values present left right order cells ih field aligned
    obtain ⟨visible, layout, physical⟩ := aligned
    cases physical with
    | node bits payload childrenWire =>
      cases payload
      cases childrenWire with
      | cons head tail =>
        cases tail
        apply CellFits.list
        apply ih
        rw [cells_length cells, List.length_map]
        exact repeated ⟨_, _, head⟩ _
  · intro fields bound
    cases bound
    exact .nil
  · intro column slot positions cell cells first rest head tail fields bound
    cases bound with
    | cons current later => exact .cons (head _ current) (tail _ later)
  · rw [List.forall₂_map_left_iff]
    exact boundColumns physical

theorem row_length {fields : List Field} {row : Row} (fits : RowFits fields row) :
    row.length = fields.length := by
  induction fields generalizing row with
  | nil => cases fits; rfl
  | cons _ _ ih =>
    cases fits with
    | cons _ tail => simp [ih tail]

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows
