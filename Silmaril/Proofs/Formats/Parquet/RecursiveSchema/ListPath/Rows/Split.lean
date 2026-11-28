module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows

open Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows

private theorem splitFrom_inside (depth : Nat) (part : List Atom)
    (internal : ∀ atom ∈ part, depth < atom.repetition)
    (tail active : List Atom) (closed : List (List Atom)) :
    splitFrom depth (part ++ tail) active closed =
      splitFrom depth tail (part.reverse ++ active) closed := by
  induction part generalizing active with
  | nil => rfl
  | cons first rest ih =>
    have after := internal first (by simp)
    simp only [List.cons_append, splitFrom, ite_eq_right (Nat.not_le_of_gt after), List.reverse_cons, List.append_assoc]
    exact ih (fun atom found => internal atom (by simp [found])) _

private theorem splitFrom_segments (depth : Nat) (parts : List Segment)
    (starts : ∀ part ∈ parts, part.first.repetition ≤ depth)
    (continues : ∀ part ∈ parts, ∀ atom ∈ part.rest, depth < atom.repetition)
    (active : List Atom) (closed : List (List Atom)) :
    splitFrom depth (parts.flatMap Segment.atoms) active closed =
      (active.reverse :: closed).reverse ++ parts.map Segment.atoms := by
  induction parts generalizing active closed with
  | nil => simp [splitFrom]
  | cons part rest ih =>
    have first := starts part (by simp)
    simp only [List.flatMap_cons, Segment.atoms, List.cons_append, splitFrom, ite_eq_left first, List.map_cons]
    rw [splitFrom_inside depth part.rest (continues part (by simp))]
    rw [ih (fun p found => starts p (by simp [found])) (fun p found => continues p (by simp [found]))]
    simp [List.reverse_cons, List.reverse_append, List.append_assoc]

public theorem split_segments (depth : Nat) (parts : List Segment)
    (starts : ∀ part ∈ parts, part.first.repetition ≤ depth)
    (continues : ∀ part ∈ parts, ∀ atom ∈ part.rest, depth < atom.repetition) :
    split depth (parts.flatMap Segment.atoms) = parts.map Segment.atoms := by
  cases parts with
  | nil => rfl
  | cons part rest =>
    simp only [List.flatMap_cons, Segment.atoms, List.cons_append, split, List.map_cons]
    rw [splitFrom_inside depth part.rest (continues part (by simp))]
    rw [splitFrom_segments depth rest (fun p found => starts p (by simp [found]))
      (fun p found => continues p (by simp [found]))]
    simp [List.reverse_append]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows
