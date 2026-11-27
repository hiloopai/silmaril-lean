module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs
import all Silmaril.Formats.Parquet.FlatProjection.Defs
import Silmaril.Formats.Parquet.FlatProjection.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms

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

private theorem read_policy_congr {snapshot : Snapshot.Checked} {left right : FlatProjection.Limits}
    (same : SameColumnPolicy left right) (bound : Bound snapshot) (index : Nat) :
    bound.read left index = bound.read right index := by
  cases bound with
  | int32 name layout binding =>
    have decode := (Int32ByteArrayGroup.decoders_congr same.page same.valueBytes layout).1
    simp [Bound.read, same.page, decode]
  | byteArray name layout binding =>
    have decode := (Int32ByteArrayGroup.decoders_congr same.page same.valueBytes layout).2
    simp [Bound.read, same.page, decode]

private theorem change_read_policy {snapshot : Snapshot.Checked} {left right : FlatProjection.Limits}
    {index : Nat} (same : SameColumnPolicy left right)
    {bindings : List (Bound snapshot)} {columns : List OrderedWriter.Column}
    (read : List.Forall₂ (fun bound value => bound.read left index = .ok value) bindings columns) :
    List.Forall₂ (fun bound value => bound.read right index = .ok value) bindings columns := by
  induction read with
  | nil => exact .nil
  | @cons bound value _ _ head tail ih =>
    exact .cons ((read_policy_congr same bound index).symm.trans head) ih

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

private theorem project_compose_policy {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked}
    {wide narrow : List OrderedWriter.BatchInput}
    (sameColumnPolicy : SameColumnPolicy originalLimits directLimits)
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
  rw [sameColumnPolicy.snapshot] at originalCheck
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

theorem project_compose {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked}
    {wide narrow : List OrderedWriter.BatchInput}
    (sameColumnPolicy : originalLimits.column = directLimits.column)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (directOpen : openFile directLimits input composed = .ok direct)
    (originalRead : original.readAll originalLimits = .ok wide)
    (directRead : direct.readAll directLimits = .ok narrow) :
    project positions (observe original wide) = some (observe direct narrow) :=
  project_compose_policy
    ⟨congrArg Int32ByteArrayGroup.Limits.snapshot sameColumnPolicy,
      congrArg Int32ByteArrayGroup.Limits.column sameColumnPolicy,
      congrArg Int32ByteArrayGroup.Limits.maxValueBytes sameColumnPolicy⟩
    composition originalOpen directOpen originalRead directRead

private theorem mapM_of_success {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (read : List.Forall₂ (fun x y => f x = .ok y) xs ys) :
    xs.mapM f = .ok ys := by
  induction read with
  | nil => rfl
  | cons head _ ih => simp [List.mapM_cons, head, ih, Bind.bind, Except.bind, pure, Except.pure]

private theorem indexed_mapM_of_success {α β ε : Type} {R : α → β → Prop}
    {f : α × Nat → Except ε β} {xs : List α} {ys : List β} (start : Nat)
    (step : ∀ {x y}, R x y → ∀ position, f (x, position) = .ok y)
    (read : List.Forall₂ R xs ys) :
    (xs.zipIdx start).mapM f = .ok ys := by
  induction read generalizing start with
  | nil => rfl
  | cons head _ ih => simp [List.mapM_cons, step head, ih, Bind.bind, Except.bind, pure, Except.pure]

private theorem bindProjection_of_lookup {snapshot : Snapshot.Checked} {ordinals : List Nat}
    {columns : List (Bound snapshot)}
    (lookup : List.Forall₂ (fun ordinal column => bindOrdinal snapshot ordinal = .ok column) ordinals columns) :
    bindProjection snapshot ordinals = .ok columns := by
  apply indexed_mapM_of_success 0 _ lookup
  intro ordinal column bound position
  change (bindOrdinal snapshot ordinal).mapError (SourceError.bind position ordinal) = .ok column
  simp [bound, Except.mapError]

theorem open_compose {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original : Checked}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (fileBytes : input.length ≤ directLimits.column.maxFileBytes)
    (rows : original.snapshot.metadata.numRows.toNat ≤ directLimits.maxFileRows)
    (fields : composed.length ≤ directLimits.maxFields) :
    ∃ direct, openFile directLimits input composed = .ok direct := by
  obtain ⟨snapshot, bound, _⟩ := open_bindings originalOpen
  obtain ⟨columns, _, lookup⟩ := select_related (bindProjection_lookup bound) composition
  have selected := bindProjection_of_lookup lookup
  rw [same.snapshot] at snapshot
  refine ⟨⟨original.snapshot, columns⟩, ?_⟩
  simp [openFile, Nat.not_lt.mpr fileBytes, Nat.not_lt.mpr fields, snapshot, Nat.not_lt.mpr rows, selected,
    Bind.bind, Except.bind, Except.mapError, pure, Except.pure]

private theorem readColumns_of_lookup {snapshot : Snapshot.Checked} {limits : FlatProjection.Limits}
    {index : Nat} {bindings : List (Bound snapshot)} {columns : List OrderedWriter.Column}
    (lookup : List.Forall₂ (fun bound column => bound.read limits index = .ok column) bindings columns) :
    readColumns limits index bindings = .ok columns := by
  apply indexed_mapM_of_success 0 _ lookup
  intro bound column decoded position
  change (bound.read limits index).mapError (SourceError.read index position bound.ordinal) = .ok column
  simp [decoded, Except.mapError]

private theorem group_select_success {snapshot : Snapshot.Checked}
    {originalLimits directLimits : FlatProjection.Limits} {positions : List Nat} {index : Nat}
    {originalColumns directColumns : List (Bound snapshot)} {batch : OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (selected : select positions originalColumns = some directColumns)
    (read : (Checked.mk snapshot originalColumns).readGroup originalLimits index = .ok batch) :
    ∃ direct, (Checked.mk snapshot directColumns).readGroup directLimits index = .ok direct := by
  obtain ⟨group, found, count, lookup⟩ := group_lookup read
  change snapshot.groupAt index = some group at found
  by_cases rows : originalLimits.column.column.maxRows < group.numRows.toNat
  · simp [Checked.readGroup, found, rows, Bind.bind, Except.bind, throw] at read
  obtain ⟨columns, _, selectedReads⟩ := select_related lookup selected
  have decoded := readColumns_of_lookup (change_read_policy same selectedReads)
  have directRows : ¬ directLimits.column.column.maxRows < group.numRows.toNat := by simpa [same.page] using rows
  refine ⟨⟨batch.rowCount, columns⟩, ?_⟩
  simp [Checked.readGroup, found, directRows, decoded, count, Bind.bind, Except.bind, pure, Except.pure]

private theorem carry_success {α β γ ε δ : Type} {left : α → Except ε β} {right : α → Except δ γ}
    {indices : List α} {wide : List β}
    (step : ∀ index batch, left index = .ok batch → ∃ direct, right index = .ok direct)
    (success : List.Forall₂ (fun index batch => left index = .ok batch) indices wide) :
    ∃ narrow, List.Forall₂ (fun index batch => right index = .ok batch) indices narrow := by
  induction success with
  | nil => exact ⟨[], .nil⟩
  | cons head _ ih =>
    obtain ⟨first, read⟩ := step _ _ head
    obtain ⟨rest, later⟩ := ih
    exact ⟨first :: rest, .cons read later⟩

private theorem composed_read_succeeds {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (directOpen : openFile directLimits input composed = .ok direct)
    (originalRead : original.readAll originalLimits = .ok wide) :
    ∃ narrow, direct.readAll directLimits = .ok narrow := by
  obtain ⟨snapshot, originalColumns⟩ := original
  obtain ⟨other, directColumns⟩ := direct
  obtain ⟨originalCheck, originalBind, _⟩ := open_bindings originalOpen
  obtain ⟨directCheck, directBind, _⟩ := open_bindings directOpen
  rw [same.snapshot] at originalCheck
  have sameSnapshot : snapshot = other := Except.ok.inj (originalCheck.symm.trans directCheck)
  subst other
  have selected := select_bound composition originalBind directBind
  obtain ⟨narrow, read⟩ := carry_success
    (right := fun index => (Checked.mk snapshot directColumns).readGroup directLimits index)
    (fun _ _ batch => group_select_success same selected batch) (readAll_indexed originalRead)
  exact ⟨narrow, mapM_of_success read⟩

theorem project_compose_success {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (directOpen : openFile directLimits input composed = .ok direct)
    (originalRead : original.readAll originalLimits = .ok wide) :
    ∃ narrow, direct.readAll directLimits = .ok narrow ∧
      project positions (observe original wide) = some (observe direct narrow) := by
  obtain ⟨narrow, read⟩ := composed_read_succeeds same composition originalOpen directOpen originalRead
  exact ⟨narrow, read, project_compose_policy same composition originalOpen directOpen originalRead read⟩

theorem project_compose_of_caps {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (originalRead : original.readAll originalLimits = .ok wide)
    (fileBytes : input.length ≤ directLimits.column.maxFileBytes)
    (rows : original.snapshot.metadata.numRows.toNat ≤ directLimits.maxFileRows)
    (fields : composed.length ≤ directLimits.maxFields) :
    ∃ direct narrow, openFile directLimits input composed = .ok direct ∧ direct.readAll directLimits = .ok narrow ∧
      project positions (observe original wide) = some (observe direct narrow) := by
  obtain ⟨direct, opened⟩ := open_compose same composition originalOpen fileBytes rows fields
  obtain ⟨narrow, read, observation⟩ := project_compose_success same composition originalOpen opened originalRead
  exact ⟨direct, narrow, opened, read, observation⟩

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
