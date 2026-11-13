module

public import Silmaril.Net.Ip.Checksum.Defs
public import Silmaril.Net.Wire.Thms

/-!
# The Internet checksum: theorems

PROVED (standard axioms):

* **`ocSum_eq`**: the incremental RFC 1071 algorithm over 16-bit words computes `fold` of their
  plain sum; with `words_sum` and `words_lt`, `ocSum (words l) = fold (wsum l)`
  (`ocSum_words`). So the checksum depends only on the plain sum of the words.
* `wsum_append`: the word sum of a concatenation whose first part has even length is the sum
  of the word sums; `wsum_be16`: a 16-bit field contributes its value.
* **`verify_fill`**: inserting `checksum (pre ++ [0, 0] ++ post)` at an even offset `pre`
  makes the receiver's check `verify` succeed. **`verify_fill_tx`**: the same for the UDP
  transmitted value `txUdp` (zero sent as all ones).
* `rfc1071_example`: the numerical example of RFC 1071 §3 (`#guard`-style, by `decide`).
-/

@[expose] public section

namespace Silmaril.Net.Ip.Checksum

open Silmaril.Net.Wire

theorem fold_le (s : Nat) : fold s ≤ 65535 := by
  unfold fold
  split <;> omega

/-- One step of the incremental algorithm on a folded sum. -/
theorem ocAdd_fold (s w : Nat) (hw : w < 65536) : ocAdd (fold s) w = fold (s + w) := by
  unfold ocAdd fold
  by_cases hs : s = 0
  · subst hs
    by_cases hw0 : w = 0
    · subst hw0; rfl
    · simp only [↓reduceIte, Nat.zero_add]
      split <;> omega
  · have h1 : s + w ≠ 0 := by omega
    simp only [hs, h1, ↓reduceIte]
    split <;> omega

theorem foldl_ocAdd (ws : List Nat) (hw : ∀ w ∈ ws, w < 65536) (s : Nat) :
    ws.foldl ocAdd (fold s) = fold (s + ws.sum) := by
  induction ws generalizing s with
  | nil => simp
  | cons w ws ih =>
    have hw0 : w < 65536 := hw w (by simp)
    have hws : ∀ v ∈ ws, v < 65536 := fun v hv => hw v (by simp [hv])
    have step : ocAdd (fold s) w = fold (s + w) := ocAdd_fold s w hw0
    rw [List.foldl_cons, step, ih hws (s + w), List.sum_cons, Nat.add_assoc]

/-- **The RFC 1071 algorithm computes the folded plain sum.** -/
theorem ocSum_eq (ws : List Nat) (hw : ∀ w ∈ ws, w < 65536) : ocSum ws = fold ws.sum := by
  have h := foldl_ocAdd ws hw 0
  simpa [ocSum, fold] using h

theorem words_sum (l : List UInt8) : (words l).sum = wsum l := by
  induction l using wsum.induct with
  | case1 => rfl
  | case2 a => simp [words, wsum]
  | case3 a b r ih => simp [words, wsum, ih]

theorem words_lt (l : List UInt8) : ∀ w ∈ words l, w < 65536 := by
  induction l using wsum.induct with
  | case1 => simp [words]
  | case2 a =>
    have ha : a.toNat < 256 := a.toNat_lt
    simp [words]; omega
  | case3 a b r ih =>
    have ha : a.toNat < 256 := a.toNat_lt
    have hb : b.toNat < 256 := b.toNat_lt
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · omega
    · exact ih w h

/-- The incremental algorithm over the words of `l` is `fold (wsum l)`. -/
theorem ocSum_words (l : List UInt8) : ocSum (words l) = fold (wsum l) := by
  rw [ocSum_eq _ (words_lt l), words_sum]

theorem wsum_append (l r : List UInt8) (h : l.length % 2 = 0) :
    wsum (l ++ r) = wsum l + wsum r := by
  induction l using wsum.induct with
  | case1 => simp [wsum]
  | case2 a => simp at h
  | case3 a b t ih =>
    have ht : t.length % 2 = 0 := by simp at h; omega
    simp only [List.cons_append, wsum, ih ht]
    omega

theorem wsum_be16 (c : UInt16) (r : List UInt8) : wsum (be16 c ++ r) = c.toNat + wsum r := by
  have h := be16_toNat c
  simp only [be16, List.cons_append, List.nil_append, wsum]
  rw [h]

@[simp] theorem wsum_zero2 (r : List UInt8) : wsum ([0, 0] ++ r) = wsum r := by
  simp [wsum]

theorem checksum_toNat (l : List UInt8) : (checksum l).toNat = 65535 - fold (wsum l) := by
  have h := fold_le (wsum l)
  rw [checksum, u16_toNat_ofNat]
  omega

/-- The folded sum is all ones once the complement of the fold is added. -/
theorem fold_add_compl (s : Nat) : fold (s + (65535 - fold s)) = 65535 := by
  unfold fold
  by_cases hs : s = 0
  · simp [hs]
  · have h1 : s + (65535 - ((s - 1) % 65535 + 1)) ≠ 0 := by omega
    simp only [hs, h1, ↓reduceIte]
    omega

/-- A nonzero sum whose fold is all ones stays all ones after adding `0xFFFF`. -/
theorem fold_add_ones (s : Nat) (h : fold s = 65535) : fold (s + 65535) = 65535 := by
  unfold fold at h ⊢
  by_cases hs : s = 0
  · simp [hs] at h
  · simp only [hs, ↓reduceIte] at h
    have h1 : s + 65535 ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
    omega

/-- **Filling in the checksum makes the receiver's check succeed.** The checksum is computed
over `pre ++ [0, 0] ++ post` (the field zeroed, RFC 9293 §3.1) and placed at an even offset. -/
theorem verify_fill (pre post : List UInt8) (h : pre.length % 2 = 0) :
    verify (pre ++ be16 (checksum (pre ++ [0, 0] ++ post)) ++ post) = true := by
  have hz : wsum (pre ++ [0, 0] ++ post) = wsum pre + wsum post := by
    rw [List.append_assoc, wsum_append _ _ h, wsum_zero2]
  have hf : wsum (pre ++ be16 (checksum (pre ++ [0, 0] ++ post)) ++ post) =
      (wsum pre + wsum post) + (65535 - fold (wsum pre + wsum post)) := by
    rw [List.append_assoc, wsum_append _ _ h, wsum_be16, checksum_toNat, hz]
    omega
  simp only [verify, hf, fold_add_compl, beq_self_eq_true]

/-- **The same with the UDP transmission rule** (zero sent as `0xFFFF`, RFC 768). -/
theorem verify_fill_tx (pre post : List UInt8) (h : pre.length % 2 = 0) :
    verify (pre ++ be16 (txUdp (checksum (pre ++ [0, 0] ++ post))) ++ post) = true := by
  by_cases hc : checksum (pre ++ [0, 0] ++ post) = 0
  · show verify (pre ++ be16 (txUdp (checksum (pre ++ [0, 0] ++ post))) ++ post) = true
    have hz : wsum (pre ++ [0, 0] ++ post) = wsum pre + wsum post := by
      rw [List.append_assoc, wsum_append _ _ h, wsum_zero2]
    have hn : (checksum (pre ++ [0, 0] ++ post)).toNat = 0 := by rw [hc]; rfl
    have hfold : fold (wsum pre + wsum post) = 65535 := by
      have := fold_le (wsum pre + wsum post)
      rw [checksum_toNat, hz] at hn
      omega
    have hf : wsum (pre ++ be16 (txUdp (checksum (pre ++ [0, 0] ++ post))) ++ post) =
        (wsum pre + wsum post) + 65535 := by
      have ht : txUdp (checksum (pre ++ [0, 0] ++ post)) = 0xFFFF := by
        rw [txUdp]; split
        · rfl
        · contradiction
      rw [ht, List.append_assoc, wsum_append _ _ h, wsum_be16]
      have : (0xFFFF : UInt16).toNat = 65535 := rfl
      omega
    simp only [verify, hf, fold_add_ones _ hfold, beq_self_eq_true]
  · show verify (pre ++ be16 (txUdp (checksum (pre ++ [0, 0] ++ post))) ++ post) = true
    have ht : txUdp (checksum (pre ++ [0, 0] ++ post)) = checksum (pre ++ [0, 0] ++ post) := by
      rw [txUdp]; split
      · contradiction
      · rfl
    rw [ht]
    exact verify_fill pre post h

/-- The numerical example of RFC 1071 §3: the octets `00 01 f2 03 f4 f5 f6 f7` have the ones'
complement sum `0xddf2`. -/
theorem rfc1071_example :
    fold (wsum [0x00, 0x01, 0xf2, 0x03, 0xf4, 0xf5, 0xf6, 0xf7]) = 0xddf2 := by decide

end Silmaril.Net.Ip.Checksum
