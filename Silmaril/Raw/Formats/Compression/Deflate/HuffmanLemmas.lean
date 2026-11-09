module

public import Silmaril.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.HuffmanLemmas`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

/-! ### Decoding -/

theorem decodeSymbolLSBAux_of_codeOK {t : HuffmanTable} {s c l : Nat} (h : t.CodeOK s c l) :
    ∀ (j : Nat) (r : LSBReader) (rest : List Bool) (fuel : Nat), j ≤ l → j + 1 ≤ fuel →
      r.Rep (msbBits c j ++ rest) →
      ∃ r', decodeSymbolLSBAux t.entries r (c >>> j) (l - j) fuel = some (s, r') ∧
        r'.Rep rest := by
  intro j
  induction j with
  | zero =>
    intro r rest fuel _ hf hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨r, ?_, by simpa [msbBits] using hr⟩
    simp [decodeSymbolLSBAux, h.found]
  | succ j ih =>
    intro r rest fuel hj hf hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hpf := h.prefixFree (l - (j + 1)) (by omega)
    rw [show l - (l - (j + 1)) = j + 1 by omega] at hpf
    rw [msbBits, List.cons_append] at hr
    obtain ⟨r1, h1, hr1⟩ := hr.readBit
    obtain ⟨r', h', hr'⟩ := ih r1 rest f (by omega) (by omega) hr1
    refine ⟨r', ?_, hr'⟩
    have hcode : (c >>> (j + 1)) * 2 + (if c.testBit j then 1 else 0) = c >>> j := by
      rw [Nat.shiftRight_succ, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
      by_cases hc : (c >>> j) % 2 = 1 <;> simp [hc] <;> omega
    have hlen : l - (j + 1) + 1 = l - j := by omega
    simp only [decodeSymbolLSBAux, hpf, h1, hcode, hlen]
    exact h'

theorem HuffmanTable.readSymbolLSB_of_codeOK {t : HuffmanTable} {s c l : Nat}
    (h : t.CodeOK s c l) {r : LSBReader} {rest : List Bool}
    (hr : r.Rep (msbBits c l ++ rest)) :
    ∃ r', t.readSymbolLSB r = some (s, r') ∧ r'.Rep rest := by
  obtain ⟨r', h', hr'⟩ :=
    decodeSymbolLSBAux_of_codeOK h l r rest (t.maxBits + 1) (Nat.le_refl _)
      (by have := h.le; omega) hr
  have h0 : c >>> l = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt h.lt
  rw [h0, Nat.sub_self] at h'
  exact ⟨r', h', hr'⟩

theorem HuffmanTable.SymOK.writeSymbolLSB {t : HuffmanTable} {s : Nat} (h : t.SymOK s)
    {w : LSBWriter} {bs : List Bool} (hw : w.Rep bs) :
    ∃ w' bits, t.writeSymbolLSB w s = some w' ∧ w'.Rep (bs ++ bits) ∧ 0 < bits.length ∧
      ∀ (r : LSBReader) rest, r.Rep (bits ++ rest) →
        ∃ r', t.readSymbolLSB r = some (s, r') ∧ r'.Rep rest := by
  obtain ⟨c, l, he, hok⟩ := h
  refine ⟨w.writeCodeMSB c l, msbBits c l, ?_, hw.writeCodeMSB c l, by simpa using hok.pos,
    fun r rest hr => HuffmanTable.readSymbolLSB_of_codeOK hok hr⟩
  simp [HuffmanTable.writeSymbolLSB, he]

/-! ### List helpers -/

theorem modifyListAtIdx_eq {α : Type} (l : List α) (idx : Nat) (f : α → α) :
    modifyListAtIdx l idx f = l.modify idx f := by
  induction l generalizing idx with
  | nil => cases idx <;> rfl
  | cons x xs ih => cases idx <;> simp [modifyListAtIdx, ih]

theorem listGet_eq {α : Type} (l : List α) (i : Nat) : listGet l i = l[i]? := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [listGet, ih]

theorem lookupEntry_go_eq_none (code len : Nat) (es : List CodeEntry)
    (h : ∀ e ∈ es, ¬(0 < e.length ∧ e.length = len ∧ e.code = code)) :
    lookupEntry.go code len es = none := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [lookupEntry.go, ih h.2]
    intro h1 h2; have := h.1; omega

theorem lookupEntry_go_eq_some (code len : Nat) :
    ∀ (es : List CodeEntry) (s : Nat) (e : CodeEntry), es[s]? = some e →
      (0 < e.length ∧ e.length = len ∧ e.code = code) →
      (∀ j < s, ∀ e', es[j]? = some e' → ¬(0 < e'.length ∧ e'.length = len ∧ e'.code = code)) →
      lookupEntry.go code len es = some e.symbol := by
  intro es
  induction es with
  | nil => intro s e h; simp at h
  | cons x xs ih =>
    intro s e hs hm hbefore
    cases s with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      rw [lookupEntry.go, ite_eq_left_of_eq_true _ _ (eq_true hm)]
    | succ s =>
      have hx := hbefore 0 (by omega) x rfl
      simp only [lookupEntry.go]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
      exact ih s e (by simpa using hs) hm
        (fun j hj e' he' => hbefore (j + 1) (by omega) e' (by simpa using he'))

/-! ### Canonical codes -/

section Canonical

variable (L : CodeLengths) (M : Nat)

theorem countByLength_go_length (ls : CodeLengths) (counts : List Nat) :
    (countByLength.go M ls counts).length = counts.length := by
  induction ls generalizing counts with
  | nil => rfl
  | cons x xs ih =>
    simp only [countByLength.go]
    split <;> simp [ih, modifyListAtIdx_eq]

theorem countByLength_go_getD (ls : CodeLengths) (counts : List Nat) (i : Nat)
    (hi : i < counts.length) (hM : counts.length = M) :
    (countByLength.go M ls counts).getD i 0 = counts.getD i 0 + ls.count (i + 1) := by
  induction ls generalizing counts with
  | nil => simp [countByLength.go]
  | cons x xs ih =>
    simp only [countByLength.go]
    split
    · next hx =>
      rw [ih _ (by simpa [modifyListAtIdx_eq] using hi) (by simpa [modifyListAtIdx_eq] using hM)]
      simp only [modifyListAtIdx_eq, List.getD_eq_getElem?_getD, List.getElem?_modify,
        List.count_cons, beq_iff_eq]
      rw [List.getElem?_eq_getElem hi]
      by_cases hxi : x = i + 1
      · simp [hxi] <;> omega
      · have : x - 1 ≠ i := by omega
        simp [this, hxi]
    · next hx =>
      rw [ih _ hi hM]
      have : x ≠ i + 1 := by omega
      simp [this]

theorem countByLength_length : (countByLength L M).length = M := by
  simp [countByLength, countByLength_go_length]

theorem countByLength_getD (i : Nat) (hi : i < M) :
    (countByLength L M).getD i 0 = L.count (i + 1) := by
  rw [countByLength, countByLength_go_getD M L _ i (by simpa using hi) (by simp)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem nextCode_go_length (cs : List Nat) (code : Nat) :
    (nextCode.go cs code).length = cs.length := by
  induction cs generalizing code with
  | nil => rfl
  | cons c cs ih => simp [nextCode.go, ih]

theorem nextCode_go_getD_zero (cs : List Nat) (code : Nat) (h : 0 < cs.length) :
    (nextCode.go cs code).getD 0 0 = code := by
  cases cs with
  | nil => simp at h
  | cons c cs => rfl

theorem nextCode_go_getD_succ (cs : List Nat) (code i : Nat) (h : i + 1 < cs.length) :
    (nextCode.go cs code).getD (i + 1) 0 =
      ((nextCode.go cs code).getD i 0 + cs.getD i 0) * 2 := by
  induction cs generalizing code i with
  | nil => simp at h
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [nextCode.go, List.getD_cons_succ, List.getD_cons_zero]
      rw [nextCode_go_getD_zero _ _ (by simp at h; omega), Nat.shiftLeft_eq]
    | succ i =>
      simp only [nextCode.go, List.getD_cons_succ]
      exact ih _ i (by simp at h; omega)

theorem assignCodes_loop_length (i : Nat) (ncR : List Nat) (ls : CodeLengths) :
    (assignCodes.loop M i ncR ls).length = ls.length := by
  induction ls generalizing i ncR with
  | nil => rfl
  | cons x xs ih => simp [assignCodes.loop, ih]

theorem assignCodes_loop_getElem? (ls : CodeLengths) :
    ∀ (i : Nat) (ncR : List Nat) (j : Nat), ncR.length = M →
      (assignCodes.loop M i ncR ls)[j]? =
        ls[j]?.map (fun len => canonEntry M ncR (i + j) len ((ls.take j).count len)) := by
  induction ls with
  | nil => intros; rfl
  | cons x xs ih =>
    intro i ncR j hM
    cases j with
    | zero =>
      simp only [assignCodes.loop, List.getElem?_cons_zero, Option.map_some, Nat.add_zero,
        List.take_zero, List.count_nil, Option.some.injEq, canonEntry]
      split
      · rfl
      · next hx =>
        rw [listGet_eq, List.getElem?_eq_getElem (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x - 1 < ncR.length by omega)]
    | succ j =>
      simp only [assignCodes.loop, List.getElem?_cons_succ, List.take_succ_cons]
      rw [ih (i + 1) _ j (by split <;> simp [modifyListAtIdx_eq, hM])]
      cases hj : xs[j]? with
      | none => rfl
      | some len =>
        simp only [Option.map_some, Option.some.injEq, canonEntry, List.count_cons, beq_iff_eq,
          show i + 1 + j = i + (j + 1) by omega]
        split
        · rfl
        · next hlen =>
          simp only [CodeEntry.mk.injEq, true_and, and_true]
          split
          · next hx =>
            by_cases hxl : x = len <;> simp [hxl] <;> omega
          · next hx =>
            simp only [modifyListAtIdx_eq, List.getD_eq_getElem?_getD, List.getElem?_modify]
            by_cases hxl : x = len
            · subst hxl
              rw [List.getElem?_eq_getElem (show x - 1 < ncR.length by omega)]
              simp <;> omega
            · have : x - 1 ≠ len - 1 := by omega
              simp [this, hxl]

theorem assignCodes_getElem? (j : Nat) :
    (assignCodes L M)[j]? =
      L[j]?.map (fun len =>
        canonEntry M (nextCode (countByLength L M)) j len ((L.take j).count len)) := by
  simp only [assignCodes]
  rw [assignCodes_loop_getElem? M L 0 _ j
    (by simp [nextCode, nextCode_go_length, countByLength_length])]
  simp

/-! #### Kraft inequality -/

theorem kraftUpTo_zero : kraftUpTo L M 0 = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [kraftUpTo, List.map_cons, List.sum_cons] at *
    rw [ih]; simp <;> omega

theorem kraftUpTo_succ (k : Nat) :
    kraftUpTo L M (k + 1) = kraftUpTo L M k + L.count (k + 1) * 2 ^ (M - (k + 1)) := by
  induction L with
  | nil => simp [kraftUpTo]
  | cons x xs ih =>
    simp only [kraftUpTo, List.map_cons, List.sum_cons, List.count_cons, beq_iff_eq] at *
    rw [ih, Nat.add_mul]
    by_cases hx : x = k + 1
    · subst hx
      have h1 : ¬(1 ≤ k + 1 ∧ k + 1 ≤ k) := by omega
      have h2 : 1 ≤ k + 1 ∧ k + 1 ≤ k + 1 := by omega
      rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left rfl]
      omega
    · have : (1 ≤ x ∧ x ≤ k + 1) ↔ (1 ≤ x ∧ x ≤ k) := by omega
      simp only [this, hx, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
      omega

theorem kraftUpTo_le (k : Nat) : kraftUpTo L M k ≤ kraftTotal L M := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [kraftUpTo, kraftTotal, List.map_cons, List.sum_cons] at *
    have : (if 1 ≤ x ∧ x ≤ k then 2 ^ (M - x) else 0) ≤ (if x = 0 then 0 else 2 ^ (M - x)) := by
      split <;> split <;> first | exact Nat.le_refl _ | exact Nat.zero_le _ | omega
    omega

theorem kraft_foldl (acc : Nat) :
    L.foldl (fun (acc : Nat) (len : Nat) => if len = 0 then acc else acc + (1 <<< (M - len))) acc =
      acc + kraftTotal L M := by
  induction L generalizing acc with
  | nil => simp [kraftTotal]
  | cons x xs ih =>
    simp only [List.foldl_cons, kraftTotal, List.map_cons, List.sum_cons] at *
    rw [ih]
    split <;> simp [Nat.shiftLeft_eq] <;> omega

theorem kraftTotal_le (h : isValidLengths L M = true) : kraftTotal L M ≤ 2 ^ M := by
  simp only [isValidLengths, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 := h.2
  rw [kraftSum, kraft_foldl, Nat.shiftLeft_eq] at h2
  simpa using h2

/-- `isValidLengths` enforces RFC 1951's cap on individual code lengths. -/
theorem isValidLengths_le (h : isValidLengths L M = true) : ∀ x ∈ L, x ≤ M := by
  simp only [isValidLengths, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1

/-! #### Next-code table -/

theorem firstCode_zero (hM : 0 < M) : firstCode L M 0 = 0 := by
  simp only [firstCode, nextCode]
  exact nextCode_go_getD_zero _ _ (by simpa [countByLength_length] using hM)

theorem firstCode_succ (m : Nat) (hm : m + 1 < M) :
    firstCode L M (m + 1) = (firstCode L M m + L.count (m + 1)) * 2 := by
  simp only [firstCode, nextCode]
  rw [nextCode_go_getD_succ _ _ _ (by simpa [countByLength_length] using hm),
    countByLength_getD L M m (by omega)]

theorem firstCode_kraft (m : Nat) (hm : m < M) :
    (firstCode L M m + L.count (m + 1)) * 2 ^ (M - (m + 1)) = kraftUpTo L M (m + 1) := by
  induction m with
  | zero => rw [firstCode_zero L M hm, kraftUpTo_succ, kraftUpTo_zero]; simp
  | succ m ih =>
    rw [firstCode_succ L M m hm, kraftUpTo_succ, ← ih (by omega),
      show M - (m + 1) = M - (m + 1 + 1) + 1 by omega, Nat.pow_succ]
    generalize 2 ^ (M - (m + 1 + 1)) = P
    generalize firstCode L M m + L.count (m + 1) = A
    rw [Nat.add_mul, Nat.mul_comm A 2, Nat.mul_comm P 2, Nat.mul_assoc, Nat.mul_left_comm]

/-- Codes of length `m + 1` fit in `m + 1` bits. -/
theorem firstCode_add_count_le (hv : isValidLengths L M = true) (m : Nat) (hm : m < M) :
    firstCode L M m + L.count (m + 1) ≤ 2 ^ (m + 1) := by
  have h1 := firstCode_kraft L M m hm
  have h2 := kraftUpTo_le L M (m + 1)
  have h3 := kraftTotal_le L M hv
  have h4 : 2 ^ M = 2 ^ (m + 1) * 2 ^ (M - (m + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h5 : (firstCode L M m + L.count (m + 1)) * 2 ^ (M - (m + 1)) ≤
      2 ^ (m + 1) * 2 ^ (M - (m + 1)) := by omega
  exact Nat.le_of_mul_le_mul_right h5 (Nat.two_pow_pos _)

/-- Codes of a greater length start above every shorter code, shifted up. -/
theorem firstCode_growth (m' : Nat) :
    ∀ m, m' < m → m < M →
      (firstCode L M m' + L.count (m' + 1)) * 2 ^ (m - m') ≤ firstCode L M m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro h hk
    rw [firstCode_succ L M k hk]
    by_cases hk' : m' = k
    · subst hk'; simp
    · have := ih (by omega) (by omega)
      rw [show k + 1 - m' = (k - m') + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_trans this (Nat.le_add_right _ _))

end Canonical

theorem count_take_lt (L : List Nat) (s : Nat) (hs : s < L.length) :
    (L.take s).count L[s] < L.count L[s] := by
  have h1 : L.count L[s] = (L.take s).count L[s] + (L.drop s).count L[s] := by
    rw [← List.count_append, List.take_append_drop]
  rw [List.drop_eq_getElem_cons hs, List.count_cons_self] at h1
  omega

theorem count_take_lt_of_lt (L : List Nat) (j s : Nat) (hj : j < s) (hs : s < L.length) :
    (L.take j).count L[j] < (L.take s).count L[j] := by
  have h1 : L.take (j + 1) = L.take j ++ [L[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
  have h2 : L.take s = L.take (j + 1) ++ (L.take s).drop (j + 1) := by
    conv => lhs; rw [← List.take_append_drop (j + 1) (L.take s)]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [h2, h1, List.count_append, List.count_append, List.count_singleton_self]
  omega

theorem HuffmanTable.ofLengths_symOK {L : CodeLengths} {M : Nat} {t : HuffmanTable}
    (h : HuffmanTable.ofLengths L M = some t) {s : Nat} (hs : s < L.length)
    (hpos : 0 < L[s]) : t.SymOK s := by
  unfold HuffmanTable.ofLengths at h
  split at h
  · simp at h
  next hv =>
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hv
  simp only [Option.some.injEq] at h
  subst h
  have hle : L[s] ≤ M := isValidLengths_le L M hv _ (List.getElem_mem hs)
  -- Every entry, described.
  have hent : ∀ j, (assignCodes L M)[j]? =
      L[j]?.map (fun len => canonEntry M (nextCode (countByLength L M)) j len
        ((L.take j).count len)) :=
    assignCodes_getElem? L M
  -- Facts about a used entry.
  have hused : ∀ e ∈ assignCodes L M, 0 < e.length →
      ∃ j, ∃ hj : j < L.length, e.length = L[j] ∧ L[j] ≤ M ∧
        e.code = firstCode L M (L[j] - 1) + (L.take j).count L[j] ∧ e.symbol = j := by
    intro e he hpos'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    rw [hent j] at hj
    cases hLj : L[j]? with
    | none => simp [hLj] at hj
    | some len =>
      have hjl : j < L.length := by
        rcases List.getElem?_eq_some_iff.mp hLj with ⟨h, _⟩; exact h
      have hLj' : L[j] = len := by
        rcases List.getElem?_eq_some_iff.mp hLj with ⟨_, h⟩; exact h
      simp only [hLj, Option.map_some, Option.some.injEq] at hj
      subst hj
      refine ⟨j, hjl, ?_⟩
      unfold canonEntry at hpos' ⊢
      split at hpos'
      · simp at hpos'
      · next hlen =>
        rw [ite_eq_right hlen]
        simp only [hLj']
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega
  have hcodeLt : ∀ e ∈ assignCodes L M, 0 < e.length →
      e.code < firstCode L M (e.length - 1) + L.count e.length := by
    intro e he hp
    obtain ⟨j, hj, hl, _, hc, _⟩ := hused e he hp
    rw [hc, hl]
    have := count_take_lt L j hj
    omega
  -- The symbol's own entry.
  have hrank := count_take_lt L s hs
  obtain ⟨l, hl⟩ : ∃ l, L[s] = l := ⟨_, rfl⟩
  rw [hl] at hpos hle hrank
  obtain ⟨c, hc⟩ : ∃ c, c = firstCode L M (l - 1) + (L.take s).count l := ⟨_, rfl⟩
  have hes : (assignCodes L M)[s]? = some { symbol := s, code := c, length := l } := by
    rw [hent s, List.getElem?_eq_getElem hs, hl]
    simp only [Option.map_some, Option.some.injEq, canonEntry]
    rw [ite_eq_right (by omega), hc]
  have hcl : c < 2 ^ l := by
    have h1 := firstCode_add_count_le L M hv (l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at h1
    omega
  refine ⟨c, l, ?_, ?_⟩
  · simp only [HuffmanTable.encodeSymbol, listGet_eq, List.getElem?_map, hes, Option.map_some]
    rw [ite_eq_left hpos]
  refine ⟨hpos, hle, hcl, ?_, ?_⟩
  · -- `(c, l)` decodes to `s`: earlier symbols of length `l` have smaller codes.
    have := lookupEntry_go_eq_some c l (assignCodes L M) s _ hes ⟨hpos, rfl, rfl⟩
    refine this ?_
    intro j hj e' he' hm
    obtain ⟨j', hj', hl', _, hc', hsym'⟩ := hused e' (List.mem_of_getElem? he') hm.1
    have hjj : j' = j := by
      rw [hent j] at he'
      cases hLj : L[j]? with
      | none => simp [hLj] at he'
      | some len =>
        simp only [hLj, Option.map_some, Option.some.injEq] at he'
        rw [← hsym', ← he']; unfold canonEntry; split <;> rfl
    subst hjj
    have hlj : L[j'] = l := by rw [← hl']; exact hm.2.1
    have hlt := count_take_lt_of_lt L j' s hj hs
    rw [hlj] at hlt
    have : e'.code = c := hm.2.2
    rw [hc', hlj] at this
    omega
  · -- No proper prefix of `c` is a code.
    intro k hk
    apply lookupEntry_go_eq_none
    intro e he hm
    obtain ⟨hp, hkl, hkc⟩ := hm
    have h1 := hcodeLt e he hp
    rw [hkl] at h1
    have hg := firstCode_growth L M (k - 1) (l - 1) (by omega) (by omega)
    rw [show l - 1 - (k - 1) = l - k by omega, show k - 1 + 1 = k by omega] at hg
    have h2 : firstCode L M (k - 1) + L.count k ≤ c >>> (l - k) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      omega
    omega

end Silmaril.Formats.Compression
