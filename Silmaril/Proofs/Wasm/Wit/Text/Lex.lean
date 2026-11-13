module

public import Silmaril.Wasm.Wit.Text.Lex.Defs

/-!
# WIT text: every layout lexes back

`lex (render d ps) = some (toks ps)` when every token is printable (`Tok.ok`): the
lexer reads a printed token back whenever what follows it stops it (`lex_str`), the
separators `gap` are whitespace, and `render` only omits a separator when the next
characters stop the token (`stopB`). Comments and whitespace are dropped
(`lex_ws`, `lex_lineComment`, `lex_blockComment`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

/-! ## Unfolding the lexer -/

theorem lex_other {c : Char} {r : List Char} (h1 : c ≠ '/') (h2 : c ≠ '-') (h3 : c ≠ '%') :
    lex (c :: r) =
      if isWs c then lex r
      else if isDigitC c then
        (Tok.num (String.ofList (c :: (takeNum r).1)) :: ·) <$> lex (takeNum r).2
      else if wordStart c then
        (wordTok (String.ofList (c :: r.takeWhile wordCont)) :: ·) <$> lex (r.dropWhile wordCont)
      else if symChars.contains c then (Tok.sym c :: ·) <$> lex r
      else none := by
  rw [lex.eq_def]
  split <;> simp_all

theorem ws_cases {c : Char} (h : isWs c = true) : c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' := by
  simp only [isWs, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> simp [h]

theorem lex_ws {c : Char} (r : List Char) (h : isWs c = true) : lex (c :: r) = lex r := by
  rcases ws_cases h with rfl | rfl | rfl | rfl <;> rw [lex_other] <;> simp [isWs]

theorem lex_ws_append (w r : List Char) (h : ∀ c ∈ w, isWs c = true) :
    lex (w ++ r) = lex r := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [List.cons_append, lex_ws _ (h c (by simp))]
    exact ih (fun x hx => h x (by simp [hx]))

theorem takeLine_append {s : List Char} (h : '\n' ∉ s) (r : List Char) :
    takeLine (s ++ '\n' :: r) = (s, r) := by
  induction s with
  | nil => simp [takeLine]
  | cons c s ih =>
    have hc : c ≠ '\n' := fun e => h (by simp [e])
    have ih := ih (fun e => h (by simp [e]))
    rw [List.cons_append, takeLine.eq_def]
    split <;> simp_all

/-- Comments are skipped: a line comment that is not a doc line. -/
theorem lex_lineComment {s : List Char} (h : '\n' ∉ s) (r : List Char) :
    lex ('/' :: '/' :: '/' :: '/' :: s ++ '\n' :: r) = lex r := by
  rw [lex.eq_def]; simp only [List.cons_append, List.head?_cons, ite_true]
  rw [← List.cons_append, takeLine_append (by simp [h])]

/-- A line comment `//` followed by a character other than `/`. -/
theorem lex_lineComment' {c : Char} (hc : c ≠ '/') {s : List Char} (h : '\n' ∉ c :: s)
    (r : List Char) : lex ('/' :: '/' :: c :: s ++ '\n' :: r) = lex r := by
  rw [lex.eq_def]
  simp only [List.cons_append]
  split <;> simp_all
  all_goals first
    | (rename_i heq; obtain ⟨rfl, rfl⟩ := heq; simp_all; done)
    | (rename_i heq; subst heq; rw [← List.cons_append, takeLine_append (by simp_all)])

/-- A block comment without nested comment markers. -/
theorem lex_blockComment {s : List Char} (h : ∀ c ∈ s, c ≠ '*' ∧ c ≠ '/') (r : List Char) :
    lex ('/' :: '*' :: s ++ '*' :: '/' :: r) = lex r := by
  have hs : ∀ d, skipBlock d (s ++ '*' :: '/' :: r) = skipBlock d ('*' :: '/' :: r) := by
    induction s with
    | nil => simp
    | cons c s ih =>
      intro d
      have hc := h c (by simp)
      rw [List.cons_append, skipBlock.eq_def]
      split <;> simp_all
  rw [lex.eq_def]
  simp only [List.cons_append]
  split <;> simp_all [skipBlock]

/-! ## Tokens read back -/

theorem wordCont_of_ws {c : Char} (h : isWs c = true) : wordCont c = false := by
  rcases ws_cases h with rfl | rfl | rfl | rfl <;> rfl

theorem takeWhile_dropWhile_of_stop {cs s : List Char} (hc : ∀ x ∈ cs, wordCont x = true)
    (hs : ∀ c t, s = c :: t → wordCont c = false) :
    (cs ++ s).takeWhile wordCont = cs ∧ (cs ++ s).dropWhile wordCont = s := by
  refine ⟨?_, ?_⟩
  · rw [List.takeWhile_append_of_pos hc]
    cases s with
    | nil => simp
    | cons d t => simp [hs d t rfl]
  · rw [List.dropWhile_append_of_pos hc]
    cases s with
    | nil => simp
    | cons d t => simp [hs d t rfl]

theorem takeNum_fst_snd (cs : List Char) : (takeNum cs).1 ++ (takeNum cs).2 = cs := by
  fun_induction takeNum cs <;> simp_all

theorem takeNum_append {cs s : List Char} (hc : (takeNum cs).2 = [])
    (hs : (takeNum s).1 = []) : takeNum (cs ++ s) = (cs, s) := by
  have hs' : takeNum s = ([], s) := by
    have := takeNum_fst_snd s; rw [hs] at this; simp_all [Prod.ext_iff]
  induction cs with
  | nil => simpa using hs'
  | cons c cs ih =>
    rw [takeNum] at hc
    split at hc
    · rename_i hcond
      have ih := ih hc
      rw [List.cons_append, takeNum, ih]
      cases cs with
      | nil =>
        have hw : wordCont c = true := by
          simp at hcond; exact hcond
        simp [hw]
      | cons d t => simp_all
    · simp at hc

/-- The keywords are words. -/
theorem keywords_words : Kw.all.all (fun k => match k.name.toList with
    | [] => false
    | c :: cs => wordStart c && cs.all wordCont && !isDigitC c && c != '/' && c != '-' &&
        c != '%' && !isWs c) = true := by decide

theorem Kw.mem_all (k : Kw) : k ∈ Kw.all := by cases k <;> decide

theorem kwOf_name (k : Kw) : kwOf? k.name = some k := by cases k <;> rfl

theorem letter_facts {c : Char} (h : isLetter c = true) :
    c ≠ '/' ∧ c ≠ '-' ∧ c ≠ '%' ∧ isWs c = false ∧ isDigitC c = false ∧ wordStart c = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by simp [wordStart, h]⟩
  · rintro rfl; revert h; decide
  · rintro rfl; revert h; decide
  · rintro rfl; revert h; decide
  · cases hw : isWs c
    · rfl
    · rcases ws_cases hw with rfl | rfl | rfl | rfl <;> revert h <;> decide
  · simp only [isLetter, isDigitC, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Char.le_def, UInt32.le_iff_toNat_le] at h ⊢
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    simp at h ⊢
    omega

theorem lex_id {s : String} (h : idOk s = true) {r : List Char}
    (hs : stopB (.id s) r = true) :
    lex ((Tok.id s).str ++ r) = (Tok.id s :: ·) <$> lex r := by
  unfold idOk at h
  split at h
  · simp at h
  · rename_i c cs hl
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hc, hcs⟩ := h
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := letter_facts hc
    obtain ⟨ht, hd⟩ := takeWhile_dropWhile_of_stop (s := r) hcs
      (by intro c t e; subst e; simpa [stopB] using hs)
    simp only [Tok.str]
    split
    · rw [hl]; simp only [List.cons_append]
      rw [lex.eq_def]; simp only [hc, ite_true, ht, hd, ← hl, String.ofList_toList]
    · rw [hl, List.cons_append, lex_other t1 t2 t3]
      rename_i hk
      have hk' : kwOf? s = none := by simpa using hk
      simp only [t4, t5, t6, ite_false, ite_true, Bool.false_eq_true, ht, hd, wordTok, ← hl,
        String.ofList_toList, hk']

theorem lex_kw (s : Kw) {r : List Char}
    (hs : stopB (.kw s) r = true) :
    lex ((Tok.kw s).str ++ r) = (Tok.kw s :: ·) <$> lex r := by
  have hw := List.all_eq_true.mp keywords_words s (Kw.mem_all s)
  simp only [Tok.str]
  split at hw
  · simp at hw
  · rename_i c cs hl
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hw
    obtain ⟨⟨⟨⟨⟨⟨hc, hcs⟩, hd⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hw
    obtain ⟨ht, hd'⟩ := takeWhile_dropWhile_of_stop (s := r) hcs
      (by intro c t e; subst e; simpa [stopB] using hs)
    rw [hl, List.cons_append, lex_other h1 h2 h3]
    simp only [h4, hd, hc, ite_false, ite_true, Bool.false_eq_true, ht, hd', wordTok, ← hl,
      String.ofList_toList, kwOf_name]

theorem lex_num {s : String} (h : numOk s = true) {r : List Char}
    (hs : stopB (.num s) r = true) :
    lex ((Tok.num s).str ++ r) = (Tok.num s :: ·) <$> lex r := by
  unfold numOk at h
  split at h
  · simp at h
  · rename_i c cs hl
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨hc, hcs⟩ := h
    have hr : (takeNum r).1 = [] := by simpa [stopB] using hs
    have ht := takeNum_append hcs hr
    have h1 : c ≠ '/' := by rintro rfl; revert hc; decide
    have h2 : c ≠ '-' := by rintro rfl; revert hc; decide
    have h3 : c ≠ '%' := by rintro rfl; revert hc; decide
    have h4 : isWs c = false := by
      cases hw : isWs c
      · rfl
      · rcases ws_cases hw with rfl | rfl | rfl | rfl <;> revert hc <;> decide
    simp only [Tok.str]
    rw [hl, List.cons_append, lex_other h1 h2 h3]
    simp only [h4, hc, ite_false, ite_true, Bool.false_eq_true, ht, ← hl, String.ofList_toList]

theorem lex_slash {r : List Char} (h1 : r.head? ≠ some '/') (h2 : r.head? ≠ some '*') :
    lex ('/' :: r) = (Tok.sym '/' :: ·) <$> lex r := by
  rw [lex.eq_def]
  split <;> simp_all
  rename_i heq
  obtain ⟨rfl, rfl⟩ := heq
  simp [isWs, isDigitC, wordStart, isLetter, symChars]

theorem symChars_facts : ∀ c ∈ symChars, isWs c = false ∧ isDigitC c = false ∧
    wordStart c = false ∧ c ≠ '-' ∧ c ≠ '%' := by decide

theorem lex_sym {c : Char} (h : symChars.contains c = true) {r : List Char}
    (hs : stopB (.sym c) r = true) :
    lex ((Tok.sym c).str ++ r) = (Tok.sym c :: ·) <$> lex r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := symChars_facts c (List.contains_iff_mem.mp h)
  simp only [Tok.str, List.cons_append, List.nil_append]
  by_cases hc : c = '/'
  · subst hc
    have hs' : r.head? ≠ some '/' ∧ r.head? ≠ some '*' := by
      rcases r with _ | ⟨x, t⟩
      · simp
      · by_cases e1 : x = '/'
        · subst e1; simp [stopB] at hs
        by_cases e2 : x = '*'
        · subst e2; simp [stopB] at hs
        simp [e1, e2]
    rw [lex_slash hs'.1 hs'.2]
  · rw [lex_other hc h4 h5]
    simp [h1, h2, h3, List.contains_iff_mem.mp h]

theorem lex_arrow (r : List Char) : lex (Tok.arrow.str ++ r) = (Tok.arrow :: ·) <$> lex r := by
  rw [lex.eq_def]; rfl

theorem lex_doc {s : String} (h : (Tok.doc s).ok = true) (r : List Char) :
    lex ((Tok.doc s).str ++ r) = (Tok.doc s :: ·) <$> lex r := by
  simp only [Tok.ok, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨hn, hh⟩ := h
  have hn' : '\n' ∉ s.toList := by
    intro hm; have := List.elem_eq_true_of_mem hm; simp_all
  have hhead : (s.toList ++ '\n' :: r).head? ≠ some '/' := by
    cases hs : s.toList with
    | nil => simp
    | cons x t => rw [hs] at hh; simpa using hh
  simp only [Tok.str, List.cons_append, List.append_assoc]
  rw [lex.eq_def]
  simp only [List.nil_append, takeLine_append hn', String.ofList_toList] at *
  simp only [hhead, ite_false]

theorem lex_str {a : Tok} (h : a.ok = true) {r : List Char} (hs : stopB a r = true) :
    lex (a.str ++ r) = (a :: ·) <$> lex r := by
  cases a with
  | id s => exact lex_id h hs
  | kw s => exact lex_kw s hs
  | sym c => exact lex_sym h hs
  | arrow => exact lex_arrow r
  | num s => exact lex_num h hs
  | doc s => exact lex_doc h r

/-! ## Layouts read back -/

theorem stopB_ws (a : Tok) {c : Char} (h : isWs c = true) (r : List Char) :
    stopB a (c :: r) = true := by
  have hw := wordCont_of_ws h
  have h1 : c ≠ '/' ∧ c ≠ '*' ∧ c ≠ '.' ∧ c ≠ '+' := by
    rcases ws_cases h with rfl | rfl | rfl | rfl <;> decide
  cases a with
  | id _ => simp [stopB, hw]
  | kw _ => simp [stopB, hw]
  | num _ => simp [stopB, takeNum, hw, h1]
  | sym d => unfold stopB; split <;> simp_all
  | arrow => simp [stopB]
  | doc _ => simp [stopB]

theorem indent_ws (d : Nat) (n : Option PTok) : ∀ c ∈ indent d n, isWs c = true := by
  intro c hc; simp only [indent, List.mem_replicate] at hc; rw [hc.2]; rfl

theorem gap_ws (d : Nat) (a : Tok) (b : Brk) (n : Option PTok) (r : List Char) :
    ∀ c ∈ gap d a b n r, isWs c = true := by
  intro c hc
  unfold gap at hc
  split at hc
  · exact indent_ws d n c hc
  · split at hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · rfl
      · exact indent_ws d n c hc
    · simp at hc; rw [hc]; rfl
    · split at hc
      · simp at hc; rw [hc]; rfl
      · split at hc
        · simp at hc
        · simp at hc; rw [hc]; rfl

theorem stopB_gap (d : Nat) (a : Tok) (b : Brk) (n : Option PTok) (r : List Char) :
    stopB a (gap d a b n r ++ r) = true := by
  cases hg : gap d a b n r with
  | cons c t => exact stopB_ws a (gap_ws d a b n r c (by simp [hg])) _
  | nil =>
    simp only [List.nil_append]
    unfold gap at hg
    split at hg
    · simp [stopB]
    · split at hg
      · simp at hg
      · simp at hg
      · split at hg
        · simp at hg
        · split at hg
          · assumption
          · simp at hg

@[simp] theorem toks_nil : toks [] = [] := rfl

@[simp] theorem toks_cons (p : PTok) (ps : List PTok) : toks (p :: ps) = p.1 :: toks ps := rfl

@[simp] theorem toks_append (ps qs : List PTok) : toks (ps ++ qs) = toks ps ++ toks qs := by
  simp [toks]

@[simp] theorem length_toks (ps : List PTok) : (toks ps).length = ps.length := by simp [toks]

/-- Every layout of printable tokens lexes back to its tokens. -/
theorem lex_render : ∀ (d : Nat) (ps : List PTok), (∀ p ∈ ps, p.1.ok = true) →
    lex (render d ps) = some (toks ps)
  | _, [], _ => by simp [render, lex]
  | d, (a, b) :: rest, h => by
    have ha : a.ok = true := h (a, b) (by simp)
    have ih := lex_render (depthAfter d a) rest (fun p hp => h p (by simp [hp]))
    simp only [render, List.append_assoc]
    rw [lex_str ha (stopB_gap _ _ _ _ _), lex_ws_append _ _ (gap_ws _ _ _ _ _), ih]
    rfl

end Silmaril.Wasm.Wit.Text
