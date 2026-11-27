module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs
import all Silmaril.Formats.Parquet.FlatProjection.Defs
import Silmaril.Formats.Parquet.FlatProjection.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition

open Silmaril.Formats Silmaril.Formats.Parquet FlatProjection
open FlatProjection.Composition
open Arrow.MixedFlat

private theorem select_cons {α : Type} (position : Nat) (rest : List Nat) (values : List α) :
    select (position :: rest) values = (do
      let value ← values[position]?
      let tail ← select rest values
      pure (value :: tail)) := by
  simp [select, List.mapM_cons]

theorem select_map {α β : Type} (f : α → β) (positions : List Nat) (values : List α) :
    select positions (values.map f) = (select positions values).map (List.map f) := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
    rw [select_cons, select_cons, ih, List.getElem?_map]
    cases value : values[position]? <;> cases tail : select rest values <;>
      simp [Bind.bind, Option.bind, pure]

private theorem lookup_related {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (related : List.Forall₂ R xs ys)
    {position : Nat} {chosen : α} (found : xs[position]? = some chosen) :
    ∃ value, ys[position]? = some value ∧ R chosen value := by
  induction related generalizing position with
  | nil => simp at found
  | @cons x y xs ys head tail ih =>
    cases position with
    | zero =>
      simp at found
      subst chosen
      exact ⟨y, rfl, head⟩
    | succ index =>
      obtain ⟨value, foundRight, relation⟩ := ih (by simpa using found)
      exact ⟨value, by simpa using foundRight, relation⟩

private theorem select_related {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (related : List.Forall₂ R xs ys)
    {positions : List Nat} {selected : List α} (picked : select positions xs = some selected) :
    ∃ values, select positions ys = some values ∧ List.Forall₂ R selected values := by
  induction positions generalizing selected with
  | nil => cases picked; exact ⟨[], rfl, .nil⟩
  | cons position rest ih =>
    cases first : xs[position]? with
    | none => simp [select_cons, first, Bind.bind, Option.bind] at picked
    | some chosen =>
      cases tail : select rest xs with
      | none => simp [select_cons, first, tail, Bind.bind, Option.bind] at picked
      | some remaining =>
        simp [select_cons, first, tail, Bind.bind, Option.bind, pure] at picked
        subst selected
        obtain ⟨value, atPosition, head⟩ := lookup_related related first
        obtain ⟨values, atRest, next⟩ := ih tail
        exact ⟨value :: values, by simp [select_cons, atPosition, atRest, Bind.bind, Option.bind, pure],
          .cons head next⟩

private theorem same_results {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {left right : List β}
    (original : List.Forall₂ (fun x y => f x = .ok y) xs left)
    (direct : List.Forall₂ (fun x y => f x = .ok y) xs right) : left = right := by
  induction original generalizing right with
  | nil => cases direct; rfl
  | cons head tail ih =>
    cases direct with
    | cons value rest =>
      exact congrArg₂ List.cons (Except.ok.inj (head.symm.trans value)) (ih rest)

private theorem change_read_policy {snapshot : Snapshot.Checked} {left right : FlatProjection.Limits}
    {index : Nat} (same : left.column = right.column)
    {bindings : List (Bound snapshot)} {columns : List OrderedWriter.Column}
    (read : List.Forall₂ (fun bound value => bound.read left index = .ok value) bindings columns) :
    List.Forall₂ (fun bound value => bound.read right index = .ok value) bindings columns := by
  induction read with
  | nil => exact .nil
  | @cons bound value _ _ head tail ih =>
    exact .cons ((bound_read_congr same bound index).symm.trans head) ih

private theorem project_batch_of_columns {positions : List Nat} {original direct : OrderedWriter.BatchInput}
    (sameRows : original.rowCount = direct.rowCount)
    (columns : select positions original.columns = some direct.columns) :
    projectBatch positions original.observe = some direct.observe := by
  simp [projectBatch, OrderedWriter.BatchInput.observe, select_map, columns, sameRows, Bind.bind, Option.bind, pure]

private theorem project_batches {positions : List Nat} {left right : Nat → Except SourceError OrderedWriter.BatchInput}
    (step : ∀ index original direct, left index = .ok original → right index = .ok direct →
      projectBatch positions original.observe = some direct.observe)
    {indices : List Nat} {original direct : List OrderedWriter.BatchInput}
    (wide : List.Forall₂ (fun index batch => left index = .ok batch) indices original)
    (narrow : List.Forall₂ (fun index batch => right index = .ok batch) indices direct) :
    (original.map OrderedWriter.BatchInput.observe).mapM (projectBatch positions) =
      some (direct.map OrderedWriter.BatchInput.observe) := by
  induction wide generalizing direct with
  | nil => cases narrow; rfl
  | @cons index first _ _ head tail ih =>
    cases narrow with
    | @cons _ second _ rest next later =>
      simp [List.mapM_cons, step index first second head next, ih later, Bind.bind, Option.bind, pure]

theorem select_bound {snapshot : Snapshot.Checked} {ordinals positions composed : List Nat}
    {original direct : List (Bound snapshot)}
    (composition : composeOrdinals ordinals positions = some composed)
    (originalBind : bindProjection snapshot ordinals = .ok original)
    (directBind : bindProjection snapshot composed = .ok direct) :
    select positions original = some direct := by
  obtain ⟨chosen, selected, lookup⟩ := select_related (bindProjection_lookup originalBind) composition
  rw [same_results lookup (bindProjection_lookup directBind)] at selected
  exact selected

theorem project_compose {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked}
    {wide narrow : List OrderedWriter.BatchInput}
    (sameColumnPolicy : originalLimits.column = directLimits.column)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (directOpen : openFile directLimits input composed = .ok direct)
    (originalRead : original.readAll originalLimits = .ok wide)
    (directRead : direct.readAll directLimits = .ok narrow) :
    project positions (observe original wide) = some (observe direct narrow) := by
  obtain ⟨snapshot, originalColumns⟩ := original
  obtain ⟨other, directColumns⟩ := direct
  obtain ⟨originalCheck, originalBind, _⟩ := open_bindings originalOpen
  obtain ⟨directCheck, directBind, _⟩ := open_bindings directOpen
  rw [sameColumnPolicy] at originalCheck
  have sameSnapshot : snapshot = other := Except.ok.inj (originalCheck.symm.trans directCheck)
  subst other
  have chosenOk := select_bound composition originalBind directBind
  have selectedFields :
      select positions (Checked.fields ⟨snapshot, originalColumns⟩) =
        some (Checked.fields ⟨snapshot, directColumns⟩) := by
    simp [Checked.fields, select_map, chosenOk]
  have selectedBatches :=
    project_batches
      (left := fun index => Checked.readGroup originalLimits index ⟨snapshot, originalColumns⟩)
      (right := fun index => Checked.readGroup directLimits index ⟨snapshot, directColumns⟩)
      (fun index first second firstRead secondRead => by
      obtain ⟨group, found, count, lookup⟩ := group_lookup firstRead
      obtain ⟨otherGroup, foundOther, otherCount, otherLookup⟩ := group_lookup secondRead
      have sameGroup : group = otherGroup := Option.some.inj (found.symm.trans foundOther)
      obtain ⟨values, selected, reads⟩ := select_related lookup chosenOk
      have equalColumns : values = second.columns :=
        same_results (change_read_policy sameColumnPolicy reads) otherLookup
      exact project_batch_of_columns (count.trans (congrArg (·.numRows.toNat) sameGroup |>.trans otherCount.symm))
        (equalColumns ▸ selected)) (readAll_indexed originalRead) (readAll_indexed directRead)
  simp [project, observe, selectedFields, selectedBatches, Bind.bind, Option.bind, pure]

theorem project_rowCounts {positions : List Nat} {original direct : Observation}
    (projected : project positions original = some direct) :
    direct.batches.map Prod.fst = original.batches.map Prod.fst := by
  have preserve {batches selected : List StreamWriter.BatchObservation}
      (read : batches.mapM (projectBatch positions) = some selected) :
      selected.map Prod.fst = batches.map Prod.fst := by
    induction batches generalizing selected with
    | nil => cases read; rfl
    | cons batch rest ih =>
      cases columns : batch.2 with
      | none => simp [List.mapM_cons, projectBatch, columns, Bind.bind, Option.bind] at read
      | some available =>
        cases selectedColumns : select positions available with
        | none => simp [List.mapM_cons, projectBatch, columns, selectedColumns, Bind.bind, Option.bind] at read
        | some values =>
          cases tail : rest.mapM (projectBatch positions) with
          | none => simp [List.mapM_cons, projectBatch, columns, selectedColumns, tail, Bind.bind, Option.bind, pure]
              at read
          | some later =>
            simp [List.mapM_cons, projectBatch, columns, selectedColumns, tail, Bind.bind, Option.bind, pure] at read
            subst selected
            simp [ih tail]
  cases fields : select positions original.fields with
  | none => simp [project, fields, Bind.bind, Option.bind] at projected
  | some selectedFields =>
    cases batches : original.batches.mapM (projectBatch positions) with
    | none => simp [project, fields, batches, Bind.bind, Option.bind] at projected
    | some selected =>
      simp [project, fields, batches, Bind.bind, Option.bind, pure] at projected
      subst direct
      exact preserve batches

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition
