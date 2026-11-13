module

public import Init.Data.Array.Perm
public import Init.Data.Vector.Perm
import all Init.Data.Array.QSort.Basic

/-! # `Array.qsort` permutes its input

Core proves nothing about `Array.qsort`; its workers `qsort.sort` and `qpartition.loop` are
private, so this file reads them with `import all`. Every step is a swap, so the result is a
permutation of the input (`Array.qsort_perm`).
-/

@[expose] public section

namespace Array

private theorem qpartition_loop_perm {α : Type _} {n : Nat} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot : α) :
    ∀ (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi),
      (qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.Perm as := by
  intro as i k ilo ik w
  induction as, i, k, ilo, ik, w using qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    rw [qpartition.loop]
    simp only [h, ↓reduceDIte, hlt, ↓reduceIte]
    exact ih.trans (Vector.swap_perm _ _)
  | case2 as i k ilo ik w h hlt ih =>
    rw [qpartition.loop]
    simp only [h, ↓reduceDIte, hlt, Bool.false_eq_true, ↓reduceIte]
    exact ih
  | case3 as i k ilo ik w h =>
    rw [qpartition.loop]
    simp only [h, ↓reduceDIte]
    exact Vector.swap_perm _ _

private theorem ite_swap_perm {α : Type _} {n : Nat} (c : Prop) [Decidable c] (bs : Vector α n)
    (i j : Nat) (h₁ : i < n) (h₂ : j < n) : (if c then bs.swap i j h₁ h₂ else bs).Perm bs := by
  split
  · exact Vector.swap_perm _ _
  · exact Vector.Perm.refl _

theorem qpartition_perm {α : Type _} {n : Nat} (as : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (qpartition as lt lo hi w hlo hhi).2.Perm as := by
  unfold qpartition
  exact (qpartition_loop_perm _ _ _ _ _ _ _ _ _ _ _).trans
    ((ite_swap_perm _ _ _ _ _ _).trans ((ite_swap_perm _ _ _ _ _ _).trans (ite_swap_perm _ _ _ _ _ _)))

private theorem qsort_sort_perm {α : Type _} (lt : α → α → Bool) {n : Nat} (as : Vector α n)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (qsort.sort lt as lo hi w hlo hhi).Perm as := by
  induction as, lo, hi, w, hlo, hhi using qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as' hp hge =>
    rw [qsort.sort]
    simp only [h, ↓reduceDIte, hp, hge]
    have := qpartition_perm as lt lo hi w hlo hhi
    rwa [hp] at this
  | case2 as lo hi w hlo hhi h mid hmid as' hp hge ih₁ _ ih₂ =>
    rw [qsort.sort]
    simp only [h, ↓reduceDIte, hp, hge]
    have := qpartition_perm as lt lo hi w hlo hhi
    rw [hp] at this
    exact ih₂.trans (ih₁.trans this)
  | case3 as lo hi w hlo hhi h =>
    rw [qsort.sort]
    simp only [h, ↓reduceDIte]
    exact Vector.Perm.refl _

/-- `Array.qsort` returns a permutation of its input. -/
theorem qsort_perm {α : Type _} (as : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (as.qsort lt lo hi).Perm as := by
  unfold qsort
  split
  · exact Array.Perm.refl _
  · exact (Vector.perm_iff_toArray_perm.mp (qsort_sort_perm _ _ _ _ _ _ _)).trans (by simp)

/-- An array of at most one element is its own sort. -/
theorem qsort_of_size_le_one {α : Type _} (as : Array α) (lt : α → α → Bool) (lo hi : Nat)
    (h : as.size ≤ 1) : as.qsort lt lo hi = as := by
  have hp := Array.perm_iff_toList_perm.mp (qsort_perm as lt lo hi)
  rcases as with ⟨_ | ⟨x, _ | ⟨y, l⟩⟩⟩
  · exact Array.toList_inj.mp hp.eq_nil
  · exact Array.toList_inj.mp (List.perm_singleton.mp hp)
  · simp at h

end Array
