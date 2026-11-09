module

public import Silmaril.Formats.Compression.Deflate.LZ77
public import Silmaril.Formats.Compression.Deflate.Compress

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.LZ77`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

@[simp] theorem applyTokens_nil (out : List UInt8) : applyTokens out [] = out := rfl

@[simp] theorem applyTokens_cons (out : List UInt8) (t : Token) (ts : List Token) :
    applyTokens out (t :: ts) = applyTokens (applyToken out t) ts := rfl

theorem take_append_getD (data : List UInt8) (pos : Nat) (hpos : pos < data.length) :
    data.take pos ++ [data.getD pos 0] = data.take (pos + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hpos, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hpos]
  rfl

/-- Copying a run that repeats `d` bytes back extends a prefix of `data`. -/
theorem copyBack_take (data : List UInt8) (d : Nat) :
    ∀ (len pos : Nat), 1 ≤ d → d ≤ pos → pos + len ≤ data.length →
      (∀ k < len, data.getD (pos - d + k) 0 = data.getD (pos + k) 0) →
      copyBack d (data.take pos) len = data.take (pos + len) := by
  intro len
  induction len with
  | zero => intro pos _ _ _ _; simp [copyBack]
  | succ len ih =>
    intro pos h1 hd hlen hm
    rw [copyBack]
    have hpos : pos < data.length := by omega
    have hget : (data.take pos).getD ((data.take pos).length - d) 0 = data.getD pos 0 := by
      rw [List.length_take, Nat.min_eq_left (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_take, ite_eq_left (by omega), ← List.getD_eq_getElem?_getD]
      simpa using hm 0 (by omega)
    rw [hget, take_append_getD data pos hpos, ih (pos + 1) h1 (by omega) (by omega),
      show pos + 1 + len = pos + (len + 1) by omega]
    intro k hk
    rw [show pos + 1 - d + k = pos - d + (k + 1) by omega,
      show pos + 1 + k = pos + (k + 1) by omega]
    exact hm (k + 1) (by omega)

theorem matchLen_spec (data : Array UInt8) (src pos maxLen i : Nat) (hi : i ≤ maxLen) :
    i ≤ matchLen data src pos maxLen i ∧ matchLen data src pos maxLen i ≤ maxLen ∧
      ∀ k, i ≤ k → k < matchLen data src pos maxLen i →
        data.toList.getD (src + k) 0 = data.toList.getD (pos + k) 0 := by
  fun_induction matchLen data src pos maxLen i with
  | case1 i hlt heq ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    refine ⟨by omega, h2, fun k hk hk' => ?_⟩
    by_cases hki : k = i
    · subst hki; rw [← arr_getD, ← arr_getD]; exact heq
    · exact h3 k (by omega) hk'
  | case2 i hlt hne => exact ⟨Nat.le_refl _, hi, fun k hk hk' => by omega⟩
  | case3 i hge => exact ⟨hi, Nat.le_refl _, fun k hk hk' => by omega⟩

/-- Whatever the hash chains propose, a nonzero match really is a match: the
distance is a legal DEFLATE back-reference and the bytes agree.  Nothing here
depends on `head`, `prev` or `chainSearch` being well formed, because the length
is recomputed by `matchLen`. -/
theorem bestMatchAt_spec (data : Array UInt8) (head prev : Array Nat) (pos maxLen len d : Nat)
    (hm : bestMatchAt data head prev pos maxLen = (len, d)) (hlen : 0 < len) :
    1 ≤ d ∧ d ≤ min pos maxDistance ∧ len ≤ maxLen ∧
      ∀ k < len, data.toList.getD (pos - d + k) 0 = data.toList.getD (pos + k) 0 := by
  simp only [bestMatchAt] at hm
  split at hm
  · next hcond =>
    simp only [Prod.mk.injEq] at hm
    obtain ⟨hl, hd⟩ := hm
    obtain ⟨_, h2, h3⟩ := matchLen_spec data (pos - bestDistAt data head prev pos maxLen) pos
      maxLen 0 (Nat.zero_le _)
    rw [hl] at h2 h3
    rw [hd] at h3 hcond
    exact ⟨hcond.1, hcond.2, h2, fun k hk => by simpa using h3 k (Nat.zero_le _) hk⟩
  · simp only [Prod.mk.injEq] at hm
    omega

theorem lz77Go_spec (data : Array UInt8) (head prev : Array Nat) (pos : Nat)
    (hpos : pos ≤ data.size) :
    TokensValid (data.toList.take pos) (lz77Go data head prev pos) ∧
      applyTokens (data.toList.take pos) (lz77Go data head prev pos) = data.toList := by
  fun_induction lz77Go data head prev pos with
  | case1 head prev pos hlt len d hm h3 hp2 ih =>
    obtain ⟨hd1, hd2, hlen, hmatch⟩ :=
      bestMatchAt_spec data head prev pos (min (data.size - pos) 258) len d hm (by omega)
    have hdp : d ≤ pos := Nat.le_trans hd2 (Nat.min_le_left _ _)
    have hdmax : d ≤ maxDistance := Nat.le_trans hd2 (Nat.min_le_right _ _)
    have hsz : data.toList.length = data.size := by simp
    have hlen258 : len ≤ 258 := Nat.le_trans hlen (Nat.min_le_right _ _)
    have hple : pos + len ≤ data.toList.length := by
      have := Nat.le_trans hlen (Nat.min_le_left (data.size - pos) 258); omega
    have hcopy := copyBack_take data.toList d len pos (by omega) hdp hple hmatch
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    refine ⟨⟨⟨h3, hlen258, hd1, hdmax, by simp; omega⟩, ?_⟩, ?_⟩
    · simpa [applyToken, hcopy] using ih1
    · simpa [applyToken, hcopy] using ih2
  | case2 head prev pos hlt len d hm h3 hp2 ih =>
    have hsz : data.toList.length = data.size := by simp
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    refine ⟨⟨trivial, ?_⟩, ?_⟩
    · simp only [applyToken]
      rw [arr_getD, take_append_getD data.toList pos (by omega)]
      exact ih1
    · simp only [applyTokens_cons, applyToken]
      rw [arr_getD, take_append_getD data.toList pos (by omega)]
      exact ih2
  | case3 head prev pos hge =>
    have hsz : data.toList.length = data.size := by simp
    refine ⟨trivial, ?_⟩
    simp only [applyTokens_nil]
    exact List.take_of_length_le (by omega)

theorem lz77Greedy_spec (data : Array UInt8) :
    lz77Greedy data =
        lz77Go data (Array.replicate hashSize 0) (Array.replicate data.size 0) 0 ++ [.eob] ∧
      TokensValid [] (lz77Go data (Array.replicate hashSize 0) (Array.replicate data.size 0) 0) ∧
      applyTokens [] (lz77Go data (Array.replicate hashSize 0) (Array.replicate data.size 0) 0)
        = data.toList := by
  have h := lz77Go_spec data (Array.replicate hashSize 0) (Array.replicate data.size 0) 0
    (Nat.zero_le _)
  simp only [List.take_zero] at h
  exact ⟨rfl, h⟩

end Silmaril.Formats.Compression.Deflate
