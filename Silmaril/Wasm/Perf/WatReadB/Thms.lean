module

public import Silmaril.Wasm.Perf.WatReadB.Defs
public import Silmaril.Wasm.Perf.WatRead.Thms

/-!
# The byte lexer is the lexer

On the characters `cs b i` of the bytes from `i`: `skipLineB_eq`, `skipBlockB_eq`,
`lexStrB_eq`, `takeWhile_cs`, `dropWhile_cs` and `lexB_eq : lexB b i acc = lexT (cs b i) acc`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.WatReadB

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (hexVal? charBytes isSpace isIdChar parseTop skipLine
  skipBlock)
open Silmaril.Wasm.Perf.WatRead (lexStrT lexT)

/-- The characters of the bytes of `b` from `i`. -/
def cs (b : ByteArray) (i : Nat) : List Char := (b.data.toList.drop i).map chr

theorem cs_cons {b : ByteArray} {i : Nat} (h : i < b.size) :
    cs b i = chr b[i] :: cs b (i + 1) := by
  have h' : i < b.data.toList.length := by rw [Array.length_toList]; exact h
  simp only [cs, List.drop_eq_getElem_cons h', List.map_cons, Array.getElem_toList]
  rfl

theorem cs_nil {b : ByteArray} {i : Nat} (h : ¬ i < b.size) : cs b i = [] := by
  have h' : b.data.toList.length ≤ i := by simp only [Array.length_toList]; exact Nat.le_of_not_lt h
  simp only [cs, List.drop_eq_nil_of_le h', List.map_nil]

theorem skipLineB_eq (b : ByteArray) (i : Nat) :
    skipLine (cs b i) = cs b (skipLineB b i) ∧ i ≤ skipLineB b i := by
  fun_induction skipLineB b i with
  | case1 i h hc => simp [cs_cons h, hc, skipLine]
  | case2 i h hc ih =>
    refine ⟨?_, by omega⟩
    rw [cs_cons h, ← ih.1]
    simp [skipLine]
  | case3 i h => simp [cs_nil h, skipLine]

theorem skipBlock_step (d : Nat) (c c' : Char) (r : List Char) (h₁ : ¬(c = ';' ∧ c' = ')'))
    (h₂ : ¬(c = '(' ∧ c' = ';')) : skipBlock d (c :: c' :: r) = skipBlock d (c' :: r) := by
  rw [skipBlock.eq_def]
  split <;> simp_all

theorem skipBlock_one (d : Nat) (c : Char) : skipBlock d [c] = none := by
  rw [skipBlock.eq_def]
  split <;> simp_all [skipBlock]

theorem skipBlockB_eq (b : ByteArray) (d i : Nat) :
    skipBlock d (cs b i) = (skipBlockB b d i).map (cs b) ∧
      ∀ j, skipBlockB b d i = some j → i < j := by
  fun_induction skipBlockB b d i with
  | case1 i h h' hc => simp [cs_cons h, cs_cons h', hc.1, hc.2, skipBlock]
  | case2 i h h' hc d ih =>
    refine ⟨?_, fun j hj => by have := ih.2 j hj; omega⟩
    rw [cs_cons h, cs_cons h', hc.1, hc.2, ← ih.1]
    simp [skipBlock]
  | case3 d i h h' hc hc' ih =>
    refine ⟨?_, fun j hj => by have := ih.2 j hj; omega⟩
    rw [cs_cons h, cs_cons h', hc'.1, hc'.2, ← ih.1]
    simp [skipBlock]
  | case4 d i h h' hc hc' ih =>
    refine ⟨?_, fun j hj => by have := ih.2 j hj; omega⟩
    rw [cs_cons h, cs_cons h', skipBlock_step d _ _ _ hc hc', ← cs_cons h', ih.1]
  | case5 d i h h' ih =>
    refine ⟨?_, fun j hj => by have := ih.2 j hj; omega⟩
    rw [cs_cons h, cs_nil h', skipBlock_one, ← ih.1, cs_nil h']
    rfl
  | case6 d i h => simp [cs_nil h, skipBlock]

theorem lexStrB_eq (b : ByteArray) (i : Nat) (acc : List UInt8) :
    lexStrT (cs b i) acc = (lexStrB b i acc).map (fun p => (p.1, cs b p.2)) ∧
      ∀ p, lexStrB b i acc = some p → i < p.2 := by
  fun_induction lexStrB b i acc <;> simp_all [cs_cons, cs_nil, lexStrT]
  all_goals
    rename_i ih
    intro a c hac
    have := ih.2 a c hac
    omega

theorem scanId_eq (b : ByteArray) (i : Nat) :
    (cs b i).dropWhile isIdChar = cs b (scanId b i) ∧
      (cs b i).takeWhile isIdChar = idChars b i (scanId b i) ∧ i ≤ scanId b i := by
  fun_induction scanId b i with
  | case1 i h hc ih =>
    have hj : i < scanId b (i + 1) := by omega
    refine ⟨?_, ?_, by omega⟩
    · rw [cs_cons h, List.dropWhile_cons_of_pos hc, ih.1]
    · rw [cs_cons h, List.takeWhile_cons_of_pos hc, ih.2.1]
      conv_rhs => rw [idChars]
      simp only [hj, h, and_self, ↓reduceDIte]
  | case2 i h hc =>
    refine ⟨?_, ?_, Nat.le_refl i⟩
    · rw [cs_cons h, List.dropWhile_cons_of_neg hc]
    · rw [cs_cons h, List.takeWhile_cons_of_neg hc, idChars]
      simp
  | case3 i h =>
    refine ⟨by rw [cs_nil h]; rfl, ?_, Nat.le_refl i⟩
    rw [cs_nil h, idChars]
    simp

theorem head_cs (b : ByteArray) (i : Nat) : (cs b i).head? = nx b i := by
  by_cases h : i < b.size
  · simp [cs_cons h, nx, h]
  · simp [cs_nil h, nx, h]

/-! ### `lexT` one step at a time -/

theorem lexT_semi (r : List Char) (acc : List Tok) :
    lexT (';' :: ';' :: r) acc = lexT (skipLine r) acc := by
  rw [lexT]

theorem lexT_block (r : List Char) (acc : List Tok) :
    lexT ('(' :: ';' :: r) acc =
      match skipBlock 0 r with
      | none => none
      | some r' => lexT r' acc := by
  rw [lexT]
  split <;> simp_all

theorem lexT_lp (r : List Char) (acc : List Tok) (h : r.head? ≠ some ';') :
    lexT ('(' :: r) acc = lexT r (Tok.lp :: acc) := by
  rw [lexT]
  intro r₁ hr
  exact h (by rw [hr]; rfl)

theorem lexT_rp (r : List Char) (acc : List Tok) : lexT (')' :: r) acc = lexT r (Tok.rp :: acc) := by
  rw [lexT]

theorem lexT_str (r : List Char) (acc : List Tok) :
    lexT ('"' :: r) acc =
      match Silmaril.Wasm.Component.Wat.Sexp.lexStr r with
      | none => none
      | some (bs, r') => lexT r' (Tok.str bs :: acc) := by
  rw [lexT]
  split <;> simp_all

theorem lexT_other (c : Char) (r : List Char) (acc : List Tok) (h₁ : c ≠ '(') (h₂ : c ≠ ')')
    (h₃ : c ≠ '"') (h₄ : ¬(c = ';' ∧ r.head? = some ';')) :
    lexT (c :: r) acc =
      if isSpace c then lexT r acc
      else if isIdChar c then
        lexT (r.dropWhile isIdChar) (Tok.atom (String.ofList (c :: r.takeWhile isIdChar)) :: acc)
      else none := by
  rw [lexT]
  all_goals first
    | (intro r₁ hc hr; exact h₄ ⟨hc, by rw [hr]; rfl⟩)
    | simp_all
theorem cs_two {b : ByteArray} {i : Nat} {d : Char} (h : i < b.size) (hn : nx b (i + 1) = some d) :
    cs b i = chr b[i] :: d :: cs b (i + 2) := by
  have h₁ : i + 1 < b.size := by
    unfold nx at hn
    split at hn
    · assumption
    · cases hn
  have hd : chr b[i + 1] = d := by
    unfold nx at hn
    simp only [h₁, ↓reduceDIte] at hn
    exact Option.some.inj hn
  rw [cs_cons h, cs_cons h₁, hd]

theorem not_semi {b : ByteArray} {i : Nat} (h : i < b.size)
    (hn : ¬(chr b[i] = ';' ∧ nx b (i + 1) = some ';')) :
    ¬(chr b[i] = ';' ∧ (cs b (i + 1)).head? = some ';') := by
  rw [head_cs]
  exact hn

/-- **The byte lexer is `lexT` on the bytes read as characters.** -/
theorem lexB_eq (b : ByteArray) (i : Nat) (acc : List Tok) : lexB b i acc = lexT (cs b i) acc := by
  fun_induction lexB b i acc with
  | case1 i acc h hc j hj ih =>
    rw [ih, cs_two h hc.2, hc.1, lexT_semi, (skipLineB_eq b (i + 2)).1]
  | case2 i acc h hc j hj =>
    have hle : i + 2 ≤ skipLineB b (i + 2) := (skipLineB_eq b (i + 2)).2
    exact absurd (by omega) hj
  | case3 i acc h hn hc hsb =>
    rw [cs_two h hc.2, hc.1, lexT_block, (skipBlockB_eq b 0 (i + 2)).1, hsb]
    rfl
  | case4 i acc h hn hc j hsb hj ih =>
    rw [ih, cs_two h hc.2, hc.1, lexT_block, (skipBlockB_eq b 0 (i + 2)).1, hsb]
    rfl
  | case5 i acc h hn hc j hsb hj =>
    have hlt : i + 2 < j := (skipBlockB_eq b 0 (i + 2)).2 j hsb
    exact absurd (by omega) hj
  | case6 i acc h hn1 hn2 hc ih =>
    rw [ih, cs_cons h, hc, lexT_lp _ _ (by rw [head_cs]; exact fun e => hn2 ⟨hc, e⟩)]
  | case7 i acc h hn1 hn2 hn3 hc ih => rw [ih, cs_cons h, hc, lexT_rp]
  | case8 i acc h hn1 hn2 hn3 hn4 hc hls =>
    rw [cs_cons h, hc, lexT_str, ← WatRead.lexStrF_eq, WatRead.lexStrF,
      (lexStrB_eq b (i + 1) []).1, hls]
    rfl
  | case9 i acc h hn1 hn2 hn3 hn4 hc bs j hls hj ih =>
    rw [ih, cs_cons h, hc, lexT_str, ← WatRead.lexStrF_eq, WatRead.lexStrF,
      (lexStrB_eq b (i + 1) []).1, hls]
    rfl
  | case10 i acc h hn1 hn2 hn3 hn4 hc bs j hls hj =>
    have hlt : i + 1 < j := (lexStrB_eq b (i + 1) []).2 (bs, j) hls
    exact absurd (by omega) hj
  | case11 i acc h hn1 hn2 hn3 hn4 hn5 hsp ih =>
    rw [ih, cs_cons h, lexT_other _ _ _ hn3 hn4 hn5 (not_semi h hn1), ite_eq_left hsp]
  | case12 i acc h hn1 hn2 hn3 hn4 hn5 hsp hid j hj ih =>
    rw [ih, cs_cons h, lexT_other _ _ _ hn3 hn4 hn5 (not_semi h hn1), ite_eq_right hsp, ite_eq_left hid,
      (scanId_eq b (i + 1)).1, (scanId_eq b (i + 1)).2.1]
  | case13 i acc h hn1 hn2 hn3 hn4 hn5 hsp hid j hj =>
    have hle : i + 1 ≤ scanId b (i + 1) := (scanId_eq b (i + 1)).2.2
    exact absurd (by omega) hj
  | case14 i acc h hn1 hn2 hn3 hn4 hn5 hsp hid =>
    rw [cs_cons h, lexT_other _ _ _ hn3 hn4 hn5 (not_semi h hn1), ite_eq_right hsp, ite_eq_right hid]
  | case15 i acc h => rw [cs_nil h, lexT]

/-! ## ASCII texts -/

theorem utf8EncodeChar_ascii (c : Char) (h : ∀ x ∈ String.utf8EncodeChar c, x < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] ∧ c.toNat < 128 := by
  by_cases hv : c.val.toNat ≤ 127
  · have he : String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
      simp only [String.utf8EncodeChar, hv, ↓reduceIte]
      rfl
    exact ⟨he, by simp only [Char.toNat]; omega⟩
  · have hmem : ∃ x ∈ String.utf8EncodeChar c, 128 ≤ x.toNat := by
      simp only [String.utf8EncodeChar, hv, ↓reduceIte]
      split_ifs <;> exact ⟨_, List.mem_cons_self, by simp only [UInt8.toNat_ofNat']; omega⟩
    obtain ⟨x, hx, hle⟩ := hmem
    have hlt : x.toNat < 128 := UInt8.lt_iff_toNat_lt.mp (h x hx)
    omega

theorem map_chr_flatMap : ∀ l : List Char,
    (∀ x ∈ l.flatMap String.utf8EncodeChar, x < 128) → (l.flatMap String.utf8EncodeChar).map chr = l
  | [], _ => rfl
  | c :: l, h => by
    have hc : ∀ x ∈ String.utf8EncodeChar c, x < 128 := fun x hx =>
      h x (by rw [List.flatMap_cons]; exact List.mem_append_left _ hx)
    have hl : ∀ x ∈ l.flatMap String.utf8EncodeChar, x < 128 := fun x hx =>
      h x (by rw [List.flatMap_cons]; exact List.mem_append_right _ hx)
    obtain ⟨he, hlt⟩ := utf8EncodeChar_ascii c hc
    have hch : chr (UInt8.ofNat c.toNat) = c := by
      have hn : (UInt8.ofNat c.toNat).toNat = c.toNat := by simp only [UInt8.toNat_ofNat']; omega
      show Char.ofNat (UInt8.ofNat c.toNat).toNat = c
      rw [hn, Char.ofNat_toNat]
    rw [List.flatMap_cons, he, List.singleton_append, List.map_cons, hch, map_chr_flatMap l hl]

/-- **On an ASCII text, the bytes read as characters are the text's characters.** -/
theorem cs_ascii (s : String) (h : ∀ x ∈ s.toByteArray.data.toList, x < 128) :
    cs s.toByteArray 0 = s.toList := by
  have hb : s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
    rw [← String.utf8Encode_toList, List.utf8Encode]
  rw [hb] at h
  simp only [cs, List.drop_zero, hb]
  exact map_chr_flatMap _ h

/-- **The reader over the bytes is `Sexp.read`.** -/
theorem readB_eq : readB = Sexp.read := by
  funext s
  unfold readB
  split
  · rename_i h
    have ha : ∀ x ∈ s.toByteArray.data.toList, x < 128 := by
      intro x hx
      have hall : s.toByteArray.data.all (· < 128) = true := h
      rw [Array.all_eq_true_iff_forall_mem] at hall
      exact of_decide_eq_true (hall x (Array.mem_toList_iff.mp hx))
    rw [lexB_eq, cs_ascii s ha, WatRead.lexT_eq]
    simp only [Sexp.read, List.reverse_nil, List.nil_append]
    cases Silmaril.Wasm.Component.Wat.Sexp.lex s.toList <;> rfl
  · exact congrFun WatRead.readF_eq s

theorem readWatB_eq : readWatB = Silmaril.Wasm.Component.Wat.read := by
  funext s
  simp only [readWatB, Silmaril.Wasm.Component.Wat.read, readB_eq]
  rfl

/-- **`parseWatB` is `wasm-wit parse`'s specification.** -/
theorem parseWatB_eq : parseWatB = Silmaril.Wasm.Wit.Tool.parseWat := by
  funext t
  simp only [parseWatB, Silmaril.Wasm.Wit.Tool.parseWat, readWatB_eq,
    ← Silmaril.Wasm.Perf.EncodeB.encode_eq_encodeF]
  rfl

end Silmaril.Wasm.Perf.WatReadB
