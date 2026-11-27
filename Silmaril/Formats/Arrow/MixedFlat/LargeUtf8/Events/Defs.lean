module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Events.Defs

/-! Dependent column observations for the opt-in mixed LargeUtf8 reader. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events

open Silmaril.Relational

def Cell : Kind → Type
  | .existing _ => MixedFlat.Events.Cell
  | .largeUtf8 => String

abbrev Signature := Scan.Schema Field Kind
abbrev Batch (signature : Signature) := Arrow.Events.Batch signature Cell

def schema (fields : List Field) : Signature :=
  ⟨fields.length, fun i =>
    let field := fields[i.val]'i.isLt
    (field, field.kind)⟩

/-- Interpret a column paired with its checked declaration. Successful
decoding supplies the matching constructor for each declared kind. -/
def cells : (kind : Kind) → Column → List (Option (Cell kind))
  | .existing _, .existing values => MixedFlat.Events.cells values
  | .largeUtf8, .largeUtf8 values => values
  | _, _ => []

/-- Preserve the original column observation at each schema position. -/
def Agrees (signature : Signature) (observed : Observed) (event : Batch signature) : Prop :=
  observed.rowCount = event.rowCount ∧ observed.columns.length = signature.width ∧
    ∀ i : Fin signature.width, ∃ column,
      observed.columns[i.val]? = some ((signature.kind i).1, column) ∧
      event.values i = cells (signature.kind i).2 column

/-- The position selected by the projection determines both the exact
declaration and the type of each nullable slot. -/
def Projects {source : Signature} (projection : Scan.Projection source) (observed : Observed)
    (event : Batch projection.schema) : Prop :=
  observed.rowCount = event.rowCount ∧
    ∀ i : Fin projection.width, ∃ column,
      observed.columns[(projection.index i).val]? = some ((projection.schema.kind i).1, column) ∧
      event.values i = cells (projection.schema.kind i).2 column

def ofObserved (fields : List Field) (observed : Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.1.kind pair.2).length = observed.rowCount) :
    Batch (schema fields) :=
  have width : observed.columns.length = fields.length := by
    simpa using congrArg List.length ordered
  let atPosition (i : Fin fields.length) :=
    observed.columns[i.val]'(Nat.lt_of_lt_of_eq i.isLt width.symm)
  have labels (i : Fin fields.length) : (atPosition i).1 = fields[i.val]'i.isLt := by
    have bound : i.val < observed.columns.length := Nat.lt_of_lt_of_eq i.isLt width.symm
    have label := congrArg (fun fs : List Field => fs[i.val]?) ordered
    simpa only [List.getElem?_map, List.getElem?_eq_getElem bound, List.getElem?_eq_getElem i.isLt,
      Option.map_some, Option.some.injEq, atPosition] using label
  ⟨observed.rowCount, fun i => cells (schema fields |>.kind i).2 (atPosition i).2, by
    intro i
    have h := aligned (atPosition i) (List.getElem_mem _)
    rw [labels i] at h
    exact h⟩

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events
