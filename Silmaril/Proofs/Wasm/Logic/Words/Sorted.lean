module

public import Silmaril.Wasm.Logic.Words.Defs
public import Mathlib.Data.List.Sort

/-!
# Sortedness of word lists (`SortedS`)

Facts about `Silmaril.Wasm.Logic.Words.SortedS` (signed `i32` order) used by the sorting and
searching entries: by positions (`sortedS_iff_getElem`), prefixes extended by one element
(`sortedS_take_succ`), a descent refutes sortedness (`not_sortedS_of_desc`), appends and
singletons.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Words

/-- `getD` inside the list is `getElem`. -/
theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem sortedS_iff_getElem {l : List (BitVec 32)} :
    SortedS l ↔ ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i < j →
      l[i].toInt ≤ l[j].toInt :=
  List.pairwise_iff_getElem

@[simp] theorem sortedS_nil : SortedS [] := List.Pairwise.nil

@[simp] theorem sortedS_single (x : BitVec 32) : SortedS [x] := List.pairwise_singleton _ _

theorem sortedS_append {l₁ l₂ : List (BitVec 32)} :
    SortedS (l₁ ++ l₂) ↔ SortedS l₁ ∧ SortedS l₂ ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, a.toInt ≤ b.toInt :=
  List.pairwise_append

theorem sortedS_cons {x : BitVec 32} {l : List (BitVec 32)} :
    SortedS (x :: l) ↔ (∀ b ∈ l, x.toInt ≤ b.toInt) ∧ SortedS l :=
  List.pairwise_cons

/-- A sorted prefix of length `i ≥ 1` whose last element is at most the next one extends to a
sorted prefix of length `i + 1`. -/
theorem sortedS_take_succ {l : List (BitVec 32)} {i : Nat} (hs : SortedS (l.take i))
    (h1 : 1 ≤ i) (hi : i < l.length) (hle : l[i - 1].toInt ≤ l[i].toInt) :
    SortedS (l.take (i + 1)) := by
  rw [← List.take_concat_get' l i hi, sortedS_append]
  refine ⟨hs, sortedS_single _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb
  subst hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk' : k < i := by simp [List.length_take] at hk; omega
  rw [List.getElem_take]
  rcases Nat.lt_or_ge k (i - 1) with hlt | hge
  · have hpair := sortedS_iff_getElem.1 hs k (i - 1) (by simp; omega) (by simp; omega) hlt
    simp only [List.getElem_take] at hpair
    omega
  · have hk'' : k = i - 1 := by omega
    subst hk''
    exact hle

/-- A descent between adjacent positions refutes sortedness. -/
theorem not_sortedS_of_desc {l : List (BitVec 32)} {i : Nat} (h1 : 1 ≤ i) (hi : i < l.length)
    (hlt : l[i].toInt < l[i - 1].toInt) : ¬ SortedS l := fun hs =>
  absurd (sortedS_iff_getElem.1 hs (i - 1) i (by omega) hi (by omega)) (by omega)

/-- A prefix of length at least the length is the list. -/
theorem sortedS_of_take {l : List (BitVec 32)} {i : Nat} (hs : SortedS (l.take i))
    (hi : l.length ≤ i) : SortedS l := by
  rwa [List.take_of_length_le hi] at hs

theorem sortedS_take_one (l : List (BitVec 32)) : SortedS (l.take 1) := by
  cases l <;> simp

end Silmaril.Wasm.Logic.Words
