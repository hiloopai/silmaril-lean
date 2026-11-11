module

public import Silmaril.Wasm.Logic.Words.Thms

/-!
# Insertion sort: list lemmas

The array during the inner loop of insertion sort, as a list. With `ys` the array at the start
of outer iteration `i` (`key = ys[i]`) and `j ≤ i` the hole, the array is
`hole ys i j = take (j + 1) ys ++ drop j (take i ys) ++ drop (i + 1) ys`:
`ys[0..j]`, then `ys[j..i)` shifted one place up. `hole_self` (`j = i`: nothing shifted yet),
`hole_shift` (one shift: `set j ys[j - 1]` moves the hole down), `getElem_hole_pred` (the element
below the hole), and `hole_place` (storing `key` at the hole: a permutation of `ys` whose prefix
of length `i + 1` is sorted).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.InsertionSort

open Silmaril.Wasm.Logic.Words

/-- The array with the hole at `j`. -/
def hole (ys : List (BitVec 32)) (i j : Nat) : List (BitVec 32) :=
  ys.take (j + 1) ++ (ys.take i).drop j ++ ys.drop (i + 1)

theorem length_hole {ys : List (BitVec 32)} {i j : Nat} (hj : j ≤ i) (hi : i < ys.length) :
    (hole ys i j).length = ys.length := by
  simp only [hole, List.length_append, List.length_take, List.length_drop]
  omega

theorem hole_self (ys : List (BitVec 32)) (i : Nat) : hole ys i i = ys := by
  simp [hole, List.take_append_drop]

/-- The element below the hole is the original one. -/
theorem getElem_hole_pred {ys : List (BitVec 32)} {i j : Nat} (h1 : 1 ≤ j) (hj : j ≤ i)
    (hi : i < ys.length) :
    (hole ys i j)[j - 1]'(by rw [length_hole hj hi]; omega) = ys[j - 1] := by
  have hlt : j - 1 < (ys.take (j + 1)).length := by simp; omega
  simp only [hole, List.append_assoc]
  rw [List.getElem_append_left hlt, List.getElem_take]

/-- **One shift**: copying `ys[j - 1]` into the hole moves the hole to `j - 1`. -/
theorem hole_shift {ys : List (BitVec 32)} {i j : Nat} (h1 : 1 ≤ j) (hj : j ≤ i)
    (hi : i < ys.length) : (hole ys i j).set j ys[j - 1] = hole ys i (j - 1) := by
  have htj : ys.take (j + 1) = ys.take j ++ [ys[j]] :=
    (List.take_concat_get' ys j (by omega)).symm
  have hdj : (ys.take i).drop (j - 1) = ys[j - 1] :: (ys.take i).drop j := by
    rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_take]
    congr 2
    omega
  have hj' : j - 1 + 1 = j := by omega
  have hlen : (ys.take j).length = j := by simp; omega
  simp only [hole, htj, hdj, hj', List.append_assoc, List.cons_append]
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.set_cons_zero,
    List.nil_append]

/-- The prefix of length `i` splits at `j`. -/
theorem take_split (ys : List (BitVec 32)) {i j : Nat} (hj : j ≤ i) :
    ys.take i = ys.take j ++ (ys.take i).drop j := by
  have h : (ys.take i).take j = ys.take j := by rw [List.take_take, Nat.min_eq_left hj]
  rw [← h, List.take_append_drop]

/-- In a sorted prefix, the elements before position `j` are at most `ys[j - 1]`. -/
theorem le_pred_of_sorted {ys : List (BitVec 32)} {i j : Nat} (hs : SortedS (ys.take i))
    (h1 : 1 ≤ j) (hj : j ≤ i) (hi : i < ys.length) {a : BitVec 32} (ha : a ∈ ys.take j) :
    a.toInt ≤ (ys[j - 1]'(by omega)).toInt := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hkj : k < j := by simp at hk; omega
  rw [List.getElem_take]
  rcases Nat.lt_or_ge k (j - 1) with hlt | hge
  · have hp := sortedS_iff_getElem.1 hs k (j - 1) (by simp; omega) (by simp; omega) hlt
    simpa only [List.getElem_take] using hp
  · have hk' : k = j - 1 := by omega
    subst hk'
    exact le_refl _

/-- Storing `key` at the hole. -/
theorem hole_set {ys : List (BitVec 32)} {i j : Nat} (hj : j ≤ i) (hi : i < ys.length) :
    (hole ys i j).set j ys[i] =
      ys.take j ++ ys[i] :: ((ys.take i).drop j ++ ys.drop (i + 1)) := by
  have htj : ys.take (j + 1) = ys.take j ++ [ys[j]] :=
    (List.take_concat_get' ys j (by omega)).symm
  have hlen : (ys.take j).length = j := by simp; omega
  simp only [hole, htj, List.append_assoc, List.cons_append]
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.set_cons_zero,
    List.nil_append]

/-- The placed array is a permutation of `ys`. -/
theorem hole_place_perm {ys : List (BitVec 32)} {i j : Nat} (hj : j ≤ i) (hi : i < ys.length) :
    ((hole ys i j).set j ys[i]).Perm ys := by
  have hys : ys = ys.take j ++ ((ys.take i).drop j ++ ys[i] :: ys.drop (i + 1)) := by
    conv_lhs => rw [← List.take_append_drop i ys, List.drop_eq_getElem_cons hi, take_split ys hj]
    simp only [List.append_assoc]
  rw [hole_set hj hi]
  conv_rhs => rw [hys]
  exact List.Perm.append_left _ List.perm_middle.symm

/-- **Placing `key`** at the hole when everything below it is at most `key` and everything
shifted is above it: the prefix of length `i + 1` is sorted. -/
theorem hole_place_sorted {ys : List (BitVec 32)} {i j : Nat} (hj : j ≤ i) (hi : i < ys.length)
    (hs : SortedS (ys.take i)) (hgt : ∀ x ∈ (ys.take i).drop j, ys[i].toInt < x.toInt)
    (hle : j = 0 ∨ (ys[j - 1]'(by omega)).toInt ≤ ys[i].toInt) :
    SortedS (((hole ys i j).set j ys[i]).take (i + 1)) := by
  have hs' : SortedS (ys.take j ++ (ys.take i).drop j) := take_split ys hj ▸ hs
  obtain ⟨hA, hD, hAD⟩ := sortedS_append.1 hs'
  have hlen : (ys.take j ++ ys[i] :: (ys.take i).drop j).length = i + 1 := by simp; omega
  have hkD : SortedS (ys[i] :: (ys.take i).drop j) :=
    sortedS_cons.2 ⟨fun b hb => le_of_lt (hgt b hb), hD⟩
  have hcross : ∀ a ∈ ys.take j, ∀ b ∈ ys[i] :: (ys.take i).drop j, a.toInt ≤ b.toInt := by
    intro a ha b hb
    rcases List.mem_cons.1 hb with rfl | hb'
    · rcases hle with h0 | hle'
      · subst h0
        simp at ha
      · exact le_trans (le_pred_of_sorted hs (List.length_pos_of_mem ha |>.trans_le
          (by simp)) hj hi ha) hle'
    · exact hAD a ha b hb'
  rw [hole_set hj hi, ← List.cons_append, ← List.append_assoc, List.take_left' hlen]
  exact sortedS_append.2 ⟨hA, hkD, hcross⟩

end Silmaril.WasmSpec.InsertionSort
