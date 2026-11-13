module

public import Silmaril.Wasm.Logic.Words.Thms

/-!
# Merge sort: list lemmas

The merge loop's invariant, as lists: the merged prefix `T` is sorted, a permutation of
`take i L ++ take j R`, and below every element still to merge (`Cross`). `merge_left` and
`merge_right` are the two steps; `take_set_succ` and `copy_set` describe the writes of the
merge and copy loops on the buffer and the array.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.MergeSort

open Silmaril.Wasm.Logic.Words

/-- Every element of `T` is at most every element of `U`. -/
def Cross (T U : List (BitVec 32)) : Prop := ∀ x ∈ T, ∀ y ∈ U, x.toInt ≤ y.toInt

theorem getD_append_left {l₁ l₂ : List (BitVec 32)} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l₁ l₂ : List (BitVec 32)} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- In a sorted list, element `i` is at most everything from position `i` on. -/
theorem le_of_mem_drop {L : List (BitVec 32)} (hL : SortedS L) {i : Nat} (hi : i < L.length)
    {y : BitVec 32} (hy : y ∈ L.drop i) : (L.getD i 0).toInt ≤ y.toInt := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  have hk' : i + k < L.length := by simp at hk; omega
  rw [List.getElem_drop, getD_of_lt _ hi]
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    exact le_refl _
  · exact sortedS_iff_getElem.1 hL i (i + k) hi hk' (by omega)

theorem drop_cons {L : List (BitVec 32)} {i : Nat} (hi : i < L.length) :
    L.drop i = L.getD i 0 :: L.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi, getD_of_lt _ hi]

theorem take_succ_getD {L : List (BitVec 32)} {i : Nat} (hi : i < L.length) :
    L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [getD_of_lt _ hi, List.take_concat_get' L i hi]

/-- **Taking the left element.** -/
theorem merge_left {L R T : List (BitVec 32)} {i j : Nat} (hL : SortedS L) (hR : SortedS R)
    (hT : SortedS T) (hc : Cross T (L.drop i ++ R.drop j)) (hp : T.Perm (L.take i ++ R.take j))
    (hi : i < L.length) (hle : R.length ≤ j ∨ (L.getD i 0).toInt ≤ (R.getD j 0).toInt) :
    SortedS (T ++ [L.getD i 0]) ∧ (T ++ [L.getD i 0]).Perm (L.take (i + 1) ++ R.take j) ∧
      Cross (T ++ [L.getD i 0]) (L.drop (i + 1) ++ R.drop j) := by
  have hd : L.drop i = L.getD i 0 :: L.drop (i + 1) := drop_cons hi
  have hx : ∀ a ∈ T, a.toInt ≤ (L.getD i 0).toInt := fun a ha =>
    hc a ha _ (List.mem_append_left _ (by rw [hd]; exact List.mem_cons_self))
  have hxR : ∀ y ∈ R.drop j, (L.getD i 0).toInt ≤ y.toInt := by
    intro y hy
    rcases hle with hj | hle'
    · simp [List.drop_eq_nil_of_le hj] at hy
    · have hj : j < R.length := by
        by_contra hc'
        simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt hc')] at hy
      exact le_trans hle' (le_of_mem_drop hR hj hy)
  refine ⟨sortedS_append.2 ⟨hT, sortedS_single _, fun a ha b hb => ?_⟩, ?_, ?_⟩
  · rw [List.mem_singleton.1 hb]
    exact hx a ha
  · rw [take_succ_getD hi, List.append_assoc]
    have h₁ : (T ++ [L.getD i 0]).Perm (L.take i ++ R.take j ++ [L.getD i 0]) := hp.append_right _
    rw [List.append_assoc] at h₁
    exact h₁.trans (List.Perm.append_left _ List.perm_append_comm)
  · show Cross (T ++ [L.getD i 0]) (L.drop (i + 1) ++ R.drop j)
    intro a ha y hy
    rcases List.mem_append.1 ha with ha' | ha'
    · rcases List.mem_append.1 hy with hy' | hy'
      · exact hc a ha' y (List.mem_append_left _ (by rw [hd]; exact List.mem_cons_of_mem _ hy'))
      · exact hc a ha' y (List.mem_append_right _ hy')
    · rw [List.mem_singleton.1 ha']
      rcases List.mem_append.1 hy with hy' | hy'
      · exact le_of_mem_drop hL hi (by rw [hd]; exact List.mem_cons_of_mem _ hy')
      · exact hxR y hy'

/-- **Taking the right element.** -/
theorem merge_right {L R T : List (BitVec 32)} {i j : Nat} (hL : SortedS L) (hR : SortedS R)
    (hT : SortedS T) (hc : Cross T (L.drop i ++ R.drop j)) (hp : T.Perm (L.take i ++ R.take j))
    (hj : j < R.length) (hlt : L.length ≤ i ∨ (R.getD j 0).toInt < (L.getD i 0).toInt) :
    SortedS (T ++ [R.getD j 0]) ∧ (T ++ [R.getD j 0]).Perm (L.take i ++ R.take (j + 1)) ∧
      Cross (T ++ [R.getD j 0]) (L.drop i ++ R.drop (j + 1)) := by
  have hd : R.drop j = R.getD j 0 :: R.drop (j + 1) := drop_cons hj
  have hx : ∀ a ∈ T, a.toInt ≤ (R.getD j 0).toInt := fun a ha =>
    hc a ha _ (List.mem_append_right _ (by rw [hd]; exact List.mem_cons_self))
  have hxL : ∀ y ∈ L.drop i, (R.getD j 0).toInt ≤ y.toInt := by
    intro y hy
    rcases hlt with hi | hlt'
    · simp [List.drop_eq_nil_of_le hi] at hy
    · have hi : i < L.length := by
        by_contra hc'
        simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt hc')] at hy
      exact le_trans (le_of_lt hlt') (le_of_mem_drop hL hi hy)
  refine ⟨sortedS_append.2 ⟨hT, sortedS_single _, fun a ha b hb => ?_⟩, ?_, ?_⟩
  · rw [List.mem_singleton.1 hb]
    exact hx a ha
  · rw [take_succ_getD hj, ← List.append_assoc]
    exact hp.append_right _
  · show Cross (T ++ [R.getD j 0]) (L.drop i ++ R.drop (j + 1))
    intro a ha y hy
    rcases List.mem_append.1 ha with ha' | ha'
    · rcases List.mem_append.1 hy with hy' | hy'
      · exact hc a ha' y (List.mem_append_left _ hy')
      · exact hc a ha' y (List.mem_append_right _ (by rw [hd]; exact List.mem_cons_of_mem _ hy'))
    · rw [List.mem_singleton.1 ha']
      rcases List.mem_append.1 hy with hy' | hy'
      · exact hxL y hy'
      · exact le_of_mem_drop hR hj (by rw [hd]; exact List.mem_cons_of_mem _ hy')

/-- Writing position `k` and taking `k + 1`. -/
theorem take_set_succ {W : List (BitVec 32)} {k : Nat} (v : BitVec 32) (hk : k < W.length) :
    (W.set k v).take (k + 1) = W.take k ++ [v] := by
  have hk' : k < (W.set k v).length := by simpa using hk
  rw [take_succ_getD hk', List.take_set_of_le (le_refl k), getD_of_lt _ hk', List.getElem_set_self]

/-- One step of the copy loop: `a[k] := W[k]`. -/
theorem copy_set {W A : List (BitVec 32)} {k : Nat} (hk : k < W.length)
    (hl : W.length = A.length) :
    (W.take k ++ A.drop k).set k (W.getD k 0) = W.take (k + 1) ++ A.drop (k + 1) := by
  have hlen : (W.take k).length = k := by simp; omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, drop_cons (by omega),
    List.set_cons_zero, take_succ_getD hk, List.append_assoc, List.singleton_append]

end Silmaril.WasmSpec.MergeSort
