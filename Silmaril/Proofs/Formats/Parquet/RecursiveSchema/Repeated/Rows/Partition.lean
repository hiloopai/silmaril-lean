module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows

open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows

private theorem extend_row {row : List Addressed} {slot : Addressed}
    (wire : RowSlice row) (continued : startsRow slot = false) : RowSlice (row ++ [slot]) := by
  obtain ⟨first, rest, rfl, starts, later⟩ := wire
  refine ⟨first, rest ++ [slot], rfl, starts, ?_⟩
  intro item found
  rcases List.mem_append.mp found with prior | added
  · exact later item prior
  · simpa only [List.mem_singleton.mp added] using continued

private theorem partitionFrom_wire {input : List Addressed} {closed : List (List Addressed)}
    {active : List Addressed} {rows : List (List Addressed)}
    (closedRows : ∀ row ∈ closed, RowSlice row)
    (opened : active = [] ∨ RowSlice active.reverse)
    (accepted : partitionFrom input closed active = .ok rows) :
    PartitionWire (closed.reverse.flatten ++ active.reverse ++ input) rows := by
  induction input generalizing closed active rows with
  | nil =>
    cases active with
    | nil =>
      simp only [partitionFrom, Except.ok.injEq] at accepted
      subst rows
      exact ⟨by simp, fun row member => closedRows row (List.mem_reverse.mp member)⟩
    | cons first rest =>
      simp only [partitionFrom, Except.ok.injEq, List.reverse_cons] at accepted
      subst rows
      refine ⟨by simp, ?_⟩
      intro row member
      rcases List.mem_append.mp member with earlier | last
      · exact closedRows row (List.mem_reverse.mp earlier)
      · obtain rfl := List.mem_singleton.mp last
        simpa only [List.reverse_cons] using (opened.resolve_left (by simp))
  | cons slot input ih =>
    by_cases starts : startsRow slot = true
    · have singleton : RowSlice [slot] := ⟨slot, [], rfl, starts, by simp⟩
      cases active with
      | nil =>
        have wire := ih (active := [slot]) closedRows (.inr (by simpa using singleton))
          (by simpa [partitionFrom, starts] using accepted)
        simpa [List.append_assoc] using wire
      | cons first rest =>
        have current := opened.resolve_left (by simp)
        have complete : ∀ row ∈ (first :: rest).reverse :: closed, RowSlice row := by
          intro row member
          rcases List.mem_cons.mp member with rfl | previous
          · exact current
          · exact closedRows row previous
        have wire := ih (active := [slot]) complete (.inr (by simpa using singleton))
          (by simpa [partitionFrom, starts] using accepted)
        simpa [List.reverse_cons, List.flatten_append, List.append_assoc] using wire
    · have continued : startsRow slot = false := by cases h : startsRow slot <;> simp_all
      cases active with
      | nil => simp [partitionFrom, continued] at accepted
      | cons first rest =>
        have current := opened.resolve_left (by simp)
        have advanced : RowSlice (slot :: first :: rest).reverse := by
          rw [List.reverse_cons]
          exact extend_row current continued
        have wire := ih closedRows (.inr advanced)
          (by simpa [partitionFrom, continued] using accepted)
        simpa [List.reverse_cons, List.append_assoc] using wire

public theorem partition_wire {slots : List Addressed} {rows : List (List Addressed)}
    (accepted : partition slots = .ok rows) : PartitionWire slots rows := by
  have wire := partitionFrom_wire (by simp) (.inl rfl) accepted
  simpa using wire

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows
