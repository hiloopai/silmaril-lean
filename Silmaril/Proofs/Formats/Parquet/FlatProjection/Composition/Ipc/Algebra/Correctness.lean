module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra

open Silmaril.Formats Silmaril.Formats.Parquet.FlatProjection.Composition
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private theorem select_cons {α : Type} (i : Nat) (rest : List Nat) (values : List α) :
    select (i :: rest) values =
      (do
        let head ← values[i]?
        let tail ← select rest values
        pure (head :: tail)) := by
  simp [select, List.mapM_cons]

private theorem select_some_iff {α : Type} (positions : List Nat) (values : List α) :
    (∃ picked, select positions values = some picked) ↔ ∀ i ∈ positions, i < values.length := by
  induction positions with
  | nil => simp [select]
  | cons i rest ih =>
    cases head : values[i]? with
    | none =>
      have outside := List.getElem?_eq_none_iff.mp head
      simp [select_cons, Bind.bind, Option.bind, Nat.not_lt.mpr outside]
    | some value =>
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp head
      cases tail : select rest values with
      | none =>
        have invalid : ¬ ∀ j ∈ rest, j < values.length := by simpa [tail] using not_congr ih
        simp [select_cons, tail, Bind.bind, Option.bind, inside, invalid]
      | some remaining =>
        have valid := ih.mp ⟨remaining, tail⟩
        simpa [select_cons, tail, Bind.bind, Option.bind, pure, inside] using valid

private theorem select_identity {α : Type} (values : List α) :
    select (List.range values.length) values = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp [List.range_succ_eq_map, select, List.mapM_map, Function.comp_def,
      Bind.bind, Option.bind, pure] at ih ⊢
    rw [ih]

private theorem select_range {positions : List Nat} {width : Nat}
    (valid : ∀ i ∈ positions, i < width) : select positions (List.range width) = some positions := by
  induction positions with
  | nil => rfl
  | cons i tail ih =>
    have head := List.getElem?_range (valid i (by simp))
    have rest := ih (fun j h => valid j (by simp [h]))
    simp [select_cons, head, rest, Bind.bind, Option.bind, pure]

private theorem select_lookup {α : Type} {positions : List Nat} {values chosen : List α}
    (picked : select positions values = some chosen) (i : Nat) :
    chosen[i]? = (positions[i]?).bind (fun position => values[position]?) := by
  induction positions generalizing chosen i with
  | nil =>
    have empty : [] = chosen := by simpa [select] using picked
    subst chosen
    rfl
  | cons position rest ih =>
    cases head : values[position]? with
    | none => simp [select_cons, head, Bind.bind, Option.bind] at picked
    | some value =>
      cases tail : select rest values with
      | none => simp [select_cons, head, tail, Bind.bind, Option.bind] at picked
      | some trailing =>
        have same : value :: trailing = chosen := by
          simpa [select_cons, head, tail, Bind.bind, Option.bind, pure] using picked
        subst chosen
        cases i with
        | zero => simpa using head.symm
        | succ index => simpa using ih tail index

private theorem select_comp {α : Type} {first second : List Nat} {values chosen : List α}
    (picked : select first values = some chosen) :
    select second chosen = (select second first).bind (fun composed => select composed values) := by
  induction second with
  | nil => rfl
  | cons i rest ih =>
    rw [select_cons, select_lookup picked, ih, select_cons]
    cases first[i]? <;> cases select rest first <;> simp [select_cons, Bind.bind, pure]

theorem readEvents_aligned {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {observed : EventObservation}
    (read : readEvents limits wire = some observed) : observed.AlignedWidth := by
  unfold readEvents at read
  cases native : Arrow.MixedFlat.Stream.Events.readAll limits wire with
  | error error => simp [complete, native] at read
  | ok events =>
    obtain ⟨schema, trace⟩ := events
    cases termination : trace.termination <;> simp [complete, native, termination] at read
    subst observed
    intro batch h
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp h
    simp [observeBatch]

private theorem mapM_of_map {α β : Type} {f : α → Option β} {g : α → β} {xs : List α}
    (step : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons, step head (by simp), ih (fun x h => step x (by simp [h]))]
    rfl

theorem projectEvents_id {observed : EventObservation} (aligned : observed.AlignedWidth) :
    projectEvents (List.range observed.fields.length) observed = some observed := by
  have batches : observed.batches.mapM (projectEventBatch (List.range observed.fields.length)) =
      some observed.batches := by
    have all := mapM_of_map (xs := observed.batches) (f := projectEventBatch (List.range observed.fields.length))
      (g := id) fun batch h => by
      simp [projectEventBatch, ← aligned batch h, select_identity]
    simpa using all
  simp [projectEvents, select_identity, batches, Bind.bind, Option.bind, pure]

theorem projectEvents_none_iff {positions : List Nat} {observed : EventObservation}
    (aligned : observed.AlignedWidth) :
    projectEvents positions observed = none ↔ ∃ i ∈ positions, observed.fields.length ≤ i := by
  have success : (∃ output, projectEvents positions observed = some output) ↔
      ∀ i ∈ positions, i < observed.fields.length := by
    constructor
    · rintro ⟨output, projected⟩
      cases fields : select positions observed.fields with
      | none => simp [projectEvents, fields, Bind.bind, Option.bind] at projected
      | some chosen => exact (select_some_iff _ _).mp ⟨chosen, fields⟩
    · intro valid
      obtain ⟨fields, selectedFields⟩ := (select_some_iff _ _).mpr valid
      have batches : ∃ selected, observed.batches.mapM (projectEventBatch positions) = some selected := by
        have perBatch (batch : BatchObservation) (h : batch ∈ observed.batches) :
            ∃ selected, projectEventBatch positions batch = some selected := by
          obtain ⟨columns, selected⟩ := (select_some_iff positions batch.2).mpr (by
            simpa [aligned batch h] using valid)
          exact ⟨(batch.1, columns), by simp [projectEventBatch, selected]⟩
        generalize observed.batches = original at perBatch
        induction original with
        | nil => exact ⟨[], rfl⟩
        | cons head tail ih =>
          obtain ⟨batch, batchOk⟩ := perBatch head (by simp)
          obtain ⟨remaining, restOk⟩ := ih fun b h => perBatch b (by simp [h])
          exact ⟨batch :: remaining, by
            simp [List.mapM_cons, batchOk, restOk, Bind.bind, Option.bind, pure]⟩
      obtain ⟨selected, selectedBatches⟩ := batches
      exact ⟨⟨fields, selected⟩, by
        simp [projectEvents, selectedFields, selectedBatches, Bind.bind, Option.bind, pure]⟩
  have rejected := not_congr success
  simpa [Option.eq_none_iff_forall_ne_some, Nat.not_lt] using rejected

private theorem mapM_shape {α β : Type} {f : α → Option β}
    {source : List α} {output : List β} {valid : β → Prop}
    (selected : source.mapM f = some output)
    (check : ∀ x y, f x = some y → valid y) :
    output.length = source.length ∧ ∀ y ∈ output, valid y := by
  induction source generalizing output with
  | nil =>
    have empty : [] = output := by simpa using selected
    simp [← empty]
  | cons head rest ih =>
    cases headPick : f head with
    | none => simp [List.mapM_cons, headPick, Bind.bind, Option.bind] at selected
    | some first =>
      cases tailPick : rest.mapM f with
      | none => simp [List.mapM_cons, headPick, tailPick, Bind.bind, Option.bind] at selected
      | some tail =>
        have same : first :: tail = output := by
          simpa [List.mapM_cons, headPick, tailPick, Bind.bind, Option.bind, pure] using selected
        subst output
        obtain ⟨length, validTail⟩ := ih tailPick
        simp only [List.length_cons, length, true_and, List.mem_cons]
        intro value member
        rcases member with rfl | member
        · exact check head _ headPick
        · exact validTail value member

private theorem select_length {α : Type} {positions : List Nat} {values chosen : List α}
    (picked : select positions values = some chosen) : chosen.length = positions.length :=
  (mapM_shape (valid := fun _ => True) (by simpa only [select] using picked) (fun _ _ _ => trivial)).1

theorem projectEvents_aligned {positions : List Nat} {observed output : EventObservation}
    (projected : projectEvents positions observed = some output) : output.AlignedWidth := by
  cases fields : select positions observed.fields with
  | none => simp [projectEvents, fields, Bind.bind, Option.bind] at projected
  | some chosen =>
    cases batches : observed.batches.mapM (projectEventBatch positions) with
    | none => simp [projectEvents, fields, batches, Bind.bind, Option.bind] at projected
    | some chosenBatches =>
      have same : (⟨chosen, chosenBatches⟩ : EventObservation) = output := by
        simpa [projectEvents, fields, batches, Bind.bind, Option.bind, pure] using projected
      subst output
      exact (mapM_shape batches fun batch output read => by
        cases columns : select positions batch.2 with
        | none => simp [projectEventBatch, columns] at read
        | some selected =>
          have pair : (batch.1, selected) = output := by
            simpa [projectEventBatch, columns] using read
          subst output
          exact (select_length columns).trans (select_length fields).symm).2

private theorem mapM_fusion {α β γ : Type} {f : α → Option β} {g : β → Option γ}
    {h : α → Option γ} {xs : List α} {ys : List β}
    (first : xs.mapM f = some ys) (step : ∀ x y, f x = some y → g y = h x) :
    ys.mapM g = xs.mapM h := by
  induction xs generalizing ys with
  | nil =>
    have empty : [] = ys := by simpa using first
    subst ys
    rfl
  | cons head tail ih =>
    cases mapped : f head with
    | none => simp [List.mapM_cons, mapped, Bind.bind, Option.bind] at first
    | some value =>
      cases remaining : tail.mapM f with
      | none => simp [List.mapM_cons, mapped, remaining, Bind.bind, Option.bind] at first
      | some rest =>
        have same : value :: rest = ys := by
          simpa [List.mapM_cons, mapped, remaining, Bind.bind, Option.bind, pure] using first
        subst ys
        simp only [List.mapM_cons, step head value mapped, ih remaining]

private theorem projectEvents_comp_of {first second : List Nat} {observed middle : EventObservation}
    (initial : projectEvents first observed = some middle) :
    projectEvents second middle = (select second first).bind (projectEvents · observed) := by
  cases fields : select first observed.fields with
  | none => simp [projectEvents, fields, Bind.bind, Option.bind] at initial
  | some chosen =>
    cases batches : observed.batches.mapM (projectEventBatch first) with
    | none => simp [projectEvents, fields, batches, Bind.bind, Option.bind] at initial
    | some chosenBatches =>
      have same : (⟨chosen, chosenBatches⟩ : EventObservation) = middle := by
        simpa [projectEvents, fields, batches, Bind.bind, Option.bind, pure] using initial
      subst middle
      have fieldComp := select_comp (second := second) fields
      cases composed : select second first with
      | none => simp [projectEvents, fieldComp, composed, Bind.bind, Option.bind]
      | some positions =>
        have batchComp : chosenBatches.mapM (projectEventBatch second) =
            observed.batches.mapM (projectEventBatch positions) := by
          apply mapM_fusion batches
          intro batch selected read
          cases picked : select first batch.2 with
          | none => simp [projectEventBatch, picked] at read
          | some columns =>
            have equal : (batch.1, columns) = selected := by simpa [projectEventBatch, picked] using read
            subst selected
            simp [projectEventBatch, select_comp (second := second) picked, composed]
        simp [projectEvents, fieldComp, composed, batchComp, Bind.bind, Option.bind]

theorem projectEvents_comp {first second : List Nat} {observed : EventObservation}
    (aligned : observed.AlignedWidth) :
    (projectEvents first observed).bind (projectEvents second) =
      (composePositions observed.fields.length first second).bind (projectEvents · observed) := by
  cases initial : projectEvents first observed with
  | none =>
    obtain ⟨i, member, outside⟩ := (projectEvents_none_iff aligned).mp initial
    cases indices : select first (List.range observed.fields.length) with
    | none => simp [composePositions, indices]
    | some list =>
      have inside := (select_some_iff _ _).mp ⟨list, indices⟩ i member
      simp at inside
      exact (Nat.not_lt.mpr outside inside).elim
  | some middle =>
    have valid : ∀ i ∈ first, i < observed.fields.length := by
      intro i member
      by_contra! outside
      have invalid := (projectEvents_none_iff aligned).mpr ⟨i, member, outside⟩
      rw [initial] at invalid
      contradiction
    simp [composePositions, select_range valid, projectEvents_comp_of (second := second) initial]

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Algebra
