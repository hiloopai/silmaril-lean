module

public import Silmaril.Wasm.Tools.Meta.Fast.Defs
public import Silmaril.Wasm.Tools.Meta.Leb.Thms

/-!
# Raw proofs: the `ByteArray` readers agree with the list readers

Restated in `Silmaril.Wasm.Tools.Meta.FastCmd.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Tools.Meta

open Silmaril.Wasm.Tools.Meta

theorem length_data (ba : ByteArray) : ba.data.toList.length = ba.size := by
  cases ba; simp [ByteArray.size]

theorem get!_eq (ba : ByteArray) (i : Nat) (h : i < ba.size) :
    ba.get! i = ba.data.toList[i]'(by rw [length_data]; exact h) := by
  cases ba with
  | mk d =>
    have h' : i < d.size := by simpa [ByteArray.size] using h
    simp [ByteArray.get!, getElem!_pos d i h']

theorem toList_loop (ba : ByteArray) : ∀ (k i : Nat) (r : List UInt8), ba.size - i = k →
    ByteArray.toList.loop ba i r = r.reverse ++ ba.data.toList.drop i
  | 0, i, r, h => by
    unfold ByteArray.toList.loop
    have h1 : ¬ i < ba.size := by omega
    have h2 : ba.data.toList.drop i = [] := List.drop_eq_nil_of_le (by rw [length_data]; omega)
    simp only [h1, ↓reduceIte, h2, List.append_nil]
  | k + 1, i, r, h => by
    unfold ByteArray.toList.loop
    have hi : i < ba.size := by omega
    simp only [hi, ↓reduceIte]
    rw [toList_loop ba k (i + 1) _ (by omega)]
    have hl : i < ba.data.toList.length := by rw [length_data]; exact hi
    rw [List.drop_eq_getElem_cons hl, get!_eq ba i hi]
    simp

/-- `ByteArray.toList` lists the data. -/
theorem toList_eq (ba : ByteArray) : ba.toList = ba.data.toList := by
  unfold ByteArray.toList
  rw [toList_loop ba _ 0 [] rfl]
  simp

/-- `sl` in terms of the data. -/
theorem sl_eq (ba : ByteArray) (i j : Nat) : sl ba i j = (ba.data.toList.drop i).take (j - i) := by
  simp only [sl, toList_eq, ByteArray.data_extract, Array.toList_extract]

theorem byteAt_eq (ba : ByteArray) (i : Nat) (h : i < ba.size) :
    byteAt ba i = ba.data.toList[i]'(by rw [length_data]; exact h) :=
  get!_eq ba i h

/-- A non-empty slice starts with its first byte. -/
theorem sl_cons (ba : ByteArray) (i j : Nat) (h : i < j) (hj : j ≤ ba.size) :
    sl ba i j = byteAt ba i :: sl ba (i + 1) j := by
  have hl : i < ba.data.toList.length := by rw [length_data]; omega
  rw [sl_eq, sl_eq, List.drop_eq_getElem_cons hl, byteAt_eq ba i (by omega)]
  rw [show j - i = (j - (i + 1)) + 1 by omega, List.take_succ_cons]

/-- An empty slice. -/
theorem sl_nil (ba : ByteArray) (i j : Nat) (h : j ≤ i) : sl ba i j = [] := by
  rw [sl_eq, show j - i = 0 by omega, List.take_zero]

/-- Dropping from a slice. -/
theorem sl_drop (ba : ByteArray) (i j n : Nat) : (sl ba i j).drop n = sl ba (i + n) j := by
  rw [sl_eq, sl_eq, List.drop_take, List.drop_drop, Nat.sub_sub]

/-- Taking from a slice. -/
theorem sl_take (ba : ByteArray) (i j n : Nat) : (sl ba i j).take n = sl ba i (min j (i + n)) := by
  rw [sl_eq, sl_eq, List.take_take, show min n (j - i) = min j (i + n) - i by omega]

/-- The length of a slice within the array. -/
theorem sl_length (ba : ByteArray) (i j : Nat) (hj : j ≤ ba.size) : (sl ba i j).length = j - i := by
  rw [sl_eq, List.length_take, List.length_drop, length_data]; omega

/-! ## `var_u32` -/

theorem rdU32Go_spec (ba : ByteArray) (j : Nat) (hj : j ≤ ba.size) :
    ∀ (k acc shift i : Nat), j - i = k →
      (match rdU32Go ba j acc shift i with
       | .ok (n, p) => readU32Go acc shift (sl ba i j) = .ok (n, sl ba p j) ∧ i < p ∧ p ≤ j
       | .error _ => ∃ e, readU32Go acc shift (sl ba i j) = .error e)
  | 0, acc, shift, i, h => by
    rw [rdU32Go, sl_nil ba i j (by omega)]
    simp only [show ¬ i < j by omega, ↓reduceDIte, readU32Go]
    exact ⟨_, rfl⟩
  | k + 1, acc, shift, i, h => by
    have hi : i < j := by omega
    rw [rdU32Go, sl_cons ba i j hi hj]
    simp only [hi, ↓reduceDIte, readU32Go]
    by_cases hc : 25 ≤ shift ∧ (byteAt ba i).toNat / 2 ^ (32 - shift) ≠ 0
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      exact ⟨_, rfl⟩
    · simp only [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      by_cases hb : (byteAt ba i).toNat < 128
      · simp only [ite_eq_left_of_eq_true _ _ (eq_true hb)]
        exact ⟨by first | rfl | trivial, by omega, by omega⟩
      · simp only [ite_eq_right_of_eq_false _ _ (eq_false hb)]
        have := rdU32Go_spec ba j hj k (acc + (byteAt ba i).toNat % 128 * 2 ^ shift) (shift + 7)
          (i + 1) (by omega)
        split at this
        · exact ⟨this.1, by omega, this.2.2⟩
        · exact this

/-- **`rdU32` reads what `readU32` reads**, ending inside the slice. -/
theorem rdU32_spec (ba : ByteArray) (j i : Nat) (hj : j ≤ ba.size) :
    match rdU32 ba j i with
    | .ok (n, p) => readU32 (sl ba i j) = .ok (n, sl ba p j) ∧ i < p ∧ p ≤ j
    | .error _ => ∃ e, readU32 (sl ba i j) = .error e := by
  by_cases hi : i < j
  · rw [rdU32, sl_cons ba i j hi hj]
    simp only [hi, ↓reduceIte, readU32]
    by_cases hb : (byteAt ba i).toNat < 128
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true hb)]
      exact ⟨by first | rfl | trivial, by omega, by omega⟩
    · simp only [ite_eq_right_of_eq_false _ _ (eq_false hb)]
      have := rdU32Go_spec ba j hj (j - (i + 1)) ((byteAt ba i).toNat % 128) 7 (i + 1) rfl
      split at this
      · exact ⟨this.1, by omega, this.2.2⟩
      · exact this
  · rw [rdU32, sl_nil ba i j (by omega)]
    simp only [hi, ↓reduceIte, readU32]
    exact ⟨_, rfl⟩


/-! ## The limit of a read -/

/-- A continuation read at limit `j` that succeeds succeeds at any larger limit. -/
theorem rdU32Go_up (ba : ByteArray) (j k : Nat) (hjk : j ≤ k) :
    ∀ (f acc sh i n p : Nat), j - i = f → rdU32Go ba j acc sh i = .ok (n, p) →
      rdU32Go ba k acc sh i = .ok (n, p)
  | 0, acc, sh, i, n, p, hf, h => by
    rw [rdU32Go] at h
    simp only [show ¬ i < j by omega, ↓reduceDIte] at h
    cases h
  | f + 1, acc, sh, i, n, p, hf, h => by
    rw [rdU32Go] at h
    rw [rdU32Go]
    simp only [show i < j by omega, show i < k by omega, ↓reduceDIte] at h ⊢
    split at h
    · cases h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      split at h
      · rename_i hb
        simp only [hb, ↓reduceIte]
        exact h
      · rename_i hb
        simp only [hb, ↓reduceIte]
        exact rdU32Go_up ba j k hjk f _ _ _ n p (by omega) h

/-- A continuation read ends after its start. -/
theorem rdU32Go_lt (ba : ByteArray) (k : Nat) :
    ∀ (f acc sh i n p : Nat), k - i = f → rdU32Go ba k acc sh i = .ok (n, p) → i < p
  | 0, acc, sh, i, n, p, hf, h => by
    rw [rdU32Go] at h
    simp only [show ¬ i < k by omega, ↓reduceDIte] at h
    cases h
  | f + 1, acc, sh, i, n, p, hf, h => by
    rw [rdU32Go] at h
    simp only [show i < k by omega, ↓reduceDIte] at h
    split at h
    · cases h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        omega
      · have := rdU32Go_lt ba k f _ _ _ n p (by omega) h
        omega

/-- A continuation read that succeeds at limit `k` ending at `p ≤ j` succeeds at `j`. -/
theorem rdU32Go_down (ba : ByteArray) (j k : Nat) :
    ∀ (f acc sh i n p : Nat), k - i = f → rdU32Go ba k acc sh i = .ok (n, p) → p ≤ j →
      rdU32Go ba j acc sh i = .ok (n, p)
  | 0, acc, sh, i, n, p, hf, h, _ => by
    rw [rdU32Go] at h
    simp only [show ¬ i < k by omega, ↓reduceDIte] at h
    cases h
  | f + 1, acc, sh, i, n, p, hf, h, hp => by
    have hip := rdU32Go_lt ba k (f + 1) acc sh i n p hf h
    rw [rdU32Go] at h
    rw [rdU32Go]
    simp only [show i < k by omega, show i < j by omega, ↓reduceDIte] at h ⊢
    split at h
    · cases h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      split at h
      · rename_i hb
        simp only [hb, ↓reduceIte]
        exact h
      · rename_i hb
        simp only [hb, ↓reduceIte]
        exact rdU32Go_down ba j k f _ _ _ n p (by omega) h hp

end Silmaril.Proofs.Wasm.Tools.Meta

end
