module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows

open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Cell CellFits Row RowFits)

private theorem bind_some {α β : Type} {first : Option α} {next : α → Option β} {result : β}
    (accepted : (first >>= next) = some result) :
    ∃ value, first = some value ∧ next value = some result := by
  cases first with
  | none => contradiction
  | some value => exact ⟨value, rfl, accepted⟩

private theorem collect {α : Type} {emit : α → Option (List Atom)} {typed : α → Prop}
    {words : α → List Chunk.Word} (sound : ∀ item trace, emit item = some trace →
      typed item ∧ trace.filterMap Atom.word = words item)
    {items : List α} {parts : List (List Atom)} (accepted : items.mapM emit = some parts) :
    (∀ item ∈ items, typed item) ∧ parts.flatten.filterMap Atom.word = items.flatMap words := by
  induction items generalizing parts with
  | nil =>
    cases Option.some.inj accepted
    simp
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, firstRead, accepted⟩ := bind_some accepted
    obtain ⟨rest, restRead, out⟩ := bind_some accepted
    cases Option.some.inj out
    obtain ⟨hTyped, hWords⟩ := sound head first firstRead
    obtain ⟨tTyped, tWords⟩ := ih restRead
    simp [hTyped, hWords, tWords]
    exact tTyped

private theorem replicate_fits {field : Silmaril.Formats.Arrow.RecursiveSchema.Field} {cells : List Cell}
    (typed : ∀ cell ∈ cells, CellFits field cell) :
    RowFits (List.replicate cells.length field) cells := by
  induction cells with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (typed first (by simp)) (ih (fun cell member => typed cell (by simp [member])))

private theorem children_sound {field : Silmaril.Formats.Arrow.RecursiveSchema.Field}
    {emit : Nat → Cell → Option (List Atom)} {words : Cell → List Chunk.Word}
    (sound : ∀ rep cell trace, emit rep cell = some trace →
      CellFits field cell ∧ trace.filterMap Atom.word = words cell)
    {headRep tailRep : Nat} {head : Cell} {tail : List Cell} {trace : List Atom}
    (accepted : Projection.children emit headRep tailRep head tail = some trace) :
    RowFits (List.replicate (head :: tail).length field) (head :: tail) ∧
      trace.filterMap Atom.word = (head :: tail).flatMap words := by
  unfold Projection.children at accepted
  obtain ⟨first, firstRead, accepted⟩ := bind_some accepted
  obtain ⟨rest, restRead, out⟩ := bind_some accepted
  cases Option.some.inj out
  obtain ⟨hTyped, hWords⟩ := sound headRep head first firstRead
  obtain ⟨tTyped, tWords⟩ := collect (sound tailRep) restRead
  exact ⟨.cons hTyped (replicate_fits tTyped), by simp [hWords, tWords]⟩

private theorem leaf_sound {plan : Plan} (rep : Nat) (cell : Cell) (trace : List Atom)
    (accepted : Projection.leaf plan rep cell = some trace) :
    CellFits (leafField plan) cell ∧ trace.filterMap Atom.word = (cellWord cell).toList := by
  cases cell with
  | none =>
    simp only [Projection.leaf] at accepted
    split at accepted
    · rename_i nullable
      cases Option.some.inj accepted
      exact ⟨by rw [leafField, nullable]; exact .null, rfl⟩
    · contradiction
  | some value =>
    cases value with
    | int32 word =>
      simp only [Projection.leaf] at accepted
      split at accepted
      · rename_i kind
        cases Option.some.inj accepted
        exact ⟨by rw [leafField, kind]; exact .int32, rfl⟩
      · contradiction
    | int64 word =>
      simp only [Projection.leaf] at accepted
      split at accepted
      · rename_i kind
        cases Option.some.inj accepted
        exact ⟨by rw [leafField, kind]; exact .int64, rfl⟩
      · contradiction
    | struct fields => contradiction
    | list values => contradiction

private theorem inner_sound {plan : Plan} (rep : Nat) (cell : Cell) (trace : List Atom)
    (accepted : Projection.inner plan rep cell = some trace) :
    CellFits (innerField plan) cell ∧ trace.filterMap Atom.word = innerWords cell := by
  cases cell with
  | none =>
    simp only [Projection.inner] at accepted
    split at accepted
    · rename_i nullable
      cases Option.some.inj accepted
      exact ⟨by rw [innerField, nullable]; exact .null, rfl⟩
    · contradiction
  | some value =>
    cases value with
    | list cells =>
      cases cells with
      | nil =>
        cases Option.some.inj accepted
        exact ⟨.list .nil, rfl⟩
      | cons head tail =>
        obtain ⟨typed, words⟩ := children_sound (leaf_sound (plan := plan)) accepted
        exact ⟨.list typed, by simpa [innerWords, elements] using words⟩
    | int32 word => contradiction
    | int64 word => contradiction
    | struct fields => contradiction

private theorem outer_sound {plan : Plan} {cell : Cell} {trace : List Atom}
    (accepted : Projection.outer plan cell = some trace) :
    CellFits (outerField plan) cell ∧ trace.filterMap Atom.word = outerWords cell := by
  cases cell with
  | none =>
    simp only [Projection.outer] at accepted
    split at accepted
    · rename_i nullable
      cases Option.some.inj accepted
      exact ⟨by rw [outerField, nullable]; exact .null, rfl⟩
    · contradiction
  | some value =>
    cases value with
    | list cells =>
      cases cells with
      | nil =>
        cases Option.some.inj accepted
        exact ⟨.list .nil, rfl⟩
      | cons head tail =>
        obtain ⟨typed, words⟩ := children_sound (inner_sound (plan := plan)) accepted
        exact ⟨.list typed, words⟩
    | int32 word => contradiction
    | int64 word => contradiction
    | struct fields => contradiction

public theorem row_sound {plan : Plan} (row : Row) (trace : List Atom)
    (accepted : Projection.row plan row = some trace) :
    RowFits (arrowSchema plan).fields row ∧ trace.filterMap Atom.word = rowWords row := by
  match row with
  | [cell] =>
    obtain ⟨typed, words⟩ := outer_sound accepted
    exact ⟨.cons typed .nil, by simpa [rowWords] using words⟩
  | [] | _ :: _ :: _ => contradiction

public theorem relation_sound {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) :
    (∀ row ∈ rows, RowFits (arrowSchema plan).fields row) ∧
      rows.flatMap rowWords = input.filterMap Atom.word := by
  unfold Relation Projection.trace at relation
  cases decoded : rows.mapM (Projection.row plan) with
  | none => simp [decoded] at relation
  | some parts =>
    have same : parts.flatten = input := by simpa [decoded] using relation
    obtain ⟨typed, words⟩ := collect (row_sound (plan := plan)) decoded
    exact ⟨typed, same ▸ words.symm⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows
