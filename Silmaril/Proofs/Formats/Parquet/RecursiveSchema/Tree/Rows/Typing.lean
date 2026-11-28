module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows

open Silmaril.Formats.Parquet.RecursiveSchema
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Cell CellFits RowFits Row)
open Tree.Rows.Projection

private theorem fold_typed {α β : Type} {typed : α → Prop} {fold : β → α → Option β}
    (step : ∀ state item out, fold state item = some out → typed item)
    {items : List α} {initial result : β}
    (accepted : items.foldlM fold initial = some result) :
    ∀ item ∈ items, typed item := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldlM_cons] at accepted
    cases done : fold initial head with
    | none => simp [done, bind, Option.bind] at accepted
    | some next =>
      simp only [done, bind, Option.bind] at accepted
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact step _ _ _ done
      · exact ih accepted _ member

private theorem fit_elements {field : Silmaril.Formats.Arrow.RecursiveSchema.Field}
    {elements : List Cell} (fits : ∀ element ∈ elements, CellFits field element) :
    RowFits (List.replicate elements.length field) elements := by
  induction elements with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (fits first (by simp)) (ih (fun value member => fits value (by simp [member])))

private theorem fields_typed {project : Repeated.Field → Nat → Cell → Traces → Option Traces}
    (one : ∀ field atColumn value input output,
      project field atColumn value input = some output → CellFits field.arrow value)
    {widths : Array Nat} {shape : List Repeated.Field} {row : Row}
    {atColumn : Nat} {input output : Traces}
    (accepted : fields project widths shape row atColumn input = some output) :
    RowFits (shape.map Repeated.Field.arrow) row := by
  induction shape generalizing row atColumn input with
  | nil =>
    cases row with
    | nil => exact .nil
    | cons _ _ => simp [fields] at accepted
  | cons field tail ih =>
    cases row with
    | nil => simp [fields] at accepted
    | cons value rest =>
      rw [fields] at accepted
      cases done : project field atColumn value input with
      | none => simp [done, bind, Option.bind] at accepted
      | some next =>
        simp only [done, bind, Option.bind] at accepted
        exact .cons (one _ _ _ _ _ done) (ih accepted)

private theorem leaf_typed {plan : Repeated.Leaf} {value : Cell}
    (signed : (ListPath.Rows.signedWord plan.kind value).isSome = true) :
    CellFits (Repeated.Field.leaf plan).arrow value := by
  cases plan with
  | mk site kind steps =>
    cases kind <;> cases value with
    | none => contradiction
    | some value =>
      cases value <;> simp [ListPath.Rows.signedWord] at signed
      rw [Repeated.Field.arrow, Kind.arrow]
      first | exact .int32 | exact .int64

private theorem cell_typed (widths : Array Nat) (depth : Nat) (levels : Levels)
    (field : Repeated.Field) (atColumn : Nat) (value : Cell) (input output : Traces)
    (accepted : cell widths depth levels field atColumn value input = some output) :
    CellFits field.arrow value := by
  induction depth generalizing levels field atColumn value input output with
  | zero => simp [cell] at accepted
  | succ depth ih =>
    cases field with
    | leaf plan =>
      cases value with
      | none =>
        by_cases nullable : plan.site.nullable = true
        · rw [Repeated.Field.arrow, nullable]
          exact .null
        · simp [cell, nullable] at accepted
      | some value =>
        apply leaf_typed
        cases word : ListPath.Rows.signedWord plan.kind (some value) with
        | none => simp [cell, word, bind, Option.bind] at accepted
        | some word => simp
    | group site children =>
      cases value with
      | none =>
        by_cases nullable : site.nullable = true
        · rw [Repeated.Field.arrow, nullable]
          exact .null
        · simp [cell, nullable] at accepted
      | some value =>
        cases value <;> simp only [cell] at accepted
        any_goals contradiction
        rw [Repeated.Field.arrow]
        exact .struct (fields_typed (fun _ _ _ _ _ read => ih _ _ _ _ _ _ read) accepted)
    | list site wrapper element =>
      cases value with
      | none =>
        by_cases nullable : site.nullable = true
        · rw [Repeated.Field.arrow, nullable]
          exact .null
        · simp [cell, nullable] at accepted
      | some value =>
        cases value <;> simp only [cell] at accepted
        any_goals contradiction
        rename_i values
        rw [Repeated.Field.arrow]
        cases values with
        | nil => exact CellFits.list (elements := []) .nil
        | cons first tail =>
          let inside : Levels := ⟨levels.definition + site.nullable.toNat + 1, levels.repetition, levels.depth + 1⟩
          change ((cell widths depth inside element atColumn first input).bind fun initial =>
            tail.foldlM (fun traced value =>
              cell widths depth { inside with repetition := inside.depth } element atColumn value traced) initial) =
              some output at accepted
          cases head : cell widths depth inside element atColumn first input with
          | none => simp [head, Option.bind] at accepted
          | some initial =>
            simp only [head, Option.bind] at accepted
            exact CellFits.list (elements := first :: tail) (.cons (ih _ _ _ _ _ _ head) (fit_elements
              (fold_typed (fun _ _ _ got => ih _ _ _ _ _ _ got) accepted)))

public theorem trace_typed {widths : Array Nat} {fieldCount depth : Nat} {schema : List Repeated.Field}
    {rows : List Row} {out : Traces} (accepted : trace widths fieldCount depth schema rows = some out) :
    ∀ row ∈ rows, RowFits (schema.map Repeated.Field.arrow) row := by
  unfold trace at accepted
  cases folded : rows.foldlM (fun columns row => fields (cell widths depth {}) widths schema row 0 columns)
      (Array.replicate fieldCount []) with
  | none => simp [folded, bind, Option.bind] at accepted
  | some traces =>
    exact fold_typed (fun _ _ _ read => fields_typed
      (fun _ _ _ _ _ projected => cell_typed _ _ _ _ _ _ _ _ projected) read) folded

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows
