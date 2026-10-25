module

public import Silmaril.Logic.Metamath.Text.Printer

@[expose] public section

/-!
# Round trip of the Metamath text format

The formal meaning of "exact text format": printing a well-formed source and
parsing it back gives the same source.

* `parseTokens_tokens`: the parser inverts `Source.tokens` on valid sources.
* `lexChars_pieces`: the lexer inverts printing tokens with arbitrary nonempty
  white space after each one; `lexChars_printTokens` is the case of single
  spaces.
* `parse_print`: `parse src.print = .ok src` for every valid source.
-/

namespace Silmaril.Logic.Metamath.Text

/-! ### Character classes -/

theorem isWs_eq_false_of_isPrintable {c : Char} (h : isPrintable c) : isWs c = false := by
  simp only [isPrintable, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> simp at h

theorem isAllowed_of_isPrintable {c : Char} (h : isPrintable c) : isAllowed c := by
  simp [isAllowed, h]

theorem isAllowed_of_isWs {c : Char} (h : isWs c) : isAllowed c := by
  simp [isAllowed, h]

theorem ne_dollar_of_isWs {c : Char} (h : isWs c) : c ≠ '$' := by
  rintro rfl; simp [isWs] at h

theorem isLabelChar_printable {c : Char} (h : isLabelChar c) : isPrintable c ∧ c ≠ '$' := by
  simp only [isLabelChar, Bool.or_eq_true, beq_iff_eq, Char.isAlphanum, Char.isAlpha,
    Char.isUpper, Char.isLower, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isPrintable, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | rfl) | rfl) | rfl
  all_goals first
    | decide
    | (simp only [GE.ge, UInt32.le_iff_toNat_le] at h1 h2
       refine ⟨⟨?_, ?_⟩, ?_⟩
       · change _ ≤ c.val.toNat; simp at h1 h2 ⊢; omega
       · change c.val.toNat ≤ _; simp at h1 h2 ⊢; omega
       · rintro rfl; simp at h1 h2)

theorem isProofLetter_printable {c : Char} (h : isProofLetter c) :
    isPrintable c ∧ c ≠ '$' := by
  simp only [isProofLetter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  simp only [isPrintable, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with ⟨h1, h2⟩ | rfl
  · simp only [Char.le_def, UInt32.le_iff_toNat_le] at h1 h2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change _ ≤ c.val.toNat; simp at h1 h2 ⊢; omega
    · change c.val.toNat ≤ _; simp at h1 h2 ⊢; omega
    · rintro rfl; simp at h1 h2
  · decide

theorem isMathSymbol_iff {s : String} :
    isMathSymbol s ↔ s.toList ≠ [] ∧ ∀ c ∈ s.toList, isPrintable c ∧ c ≠ '$' := by
  simp [isMathSymbol]

theorem isLabel_iff {s : String} : isLabel s ↔ s.toList ≠ [] ∧ ∀ c ∈ s.toList, isLabelChar c := by
  simp [isLabel]

theorem isMathSymbol_of_isLabel {s : String} (h : isLabel s) : isMathSymbol s := by
  rw [isLabel_iff] at h
  exact isMathSymbol_iff.2 ⟨h.1, fun c hc => isLabelChar_printable (h.2 c hc)⟩

theorem isMathSymbol_of_isProofStep {s : String} (h : isProofStep s) : isMathSymbol s := by
  simp only [isProofStep, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · decide
  · exact isMathSymbol_of_isLabel h

theorem isMathSymbol_of_isLetterToken {s : String} (h : isLetterToken s) (hs : s ≠ "") :
    isMathSymbol s := by
  simp only [isLetterToken, List.all_eq_true] at h
  refine isMathSymbol_iff.2 ⟨fun h' => hs (String.toList_inj.1 (by simpa using h')), ?_⟩
  exact fun c hc => isProofLetter_printable (h c hc)

theorem ne_open_of_isProofStep {s : String} (h : isProofStep s) : s ≠ "(" := by
  rintro rfl; revert h; decide

theorem ne_close_of_isLabel {s : String} (h : isLabel s) : s ≠ ")" := by
  rintro rfl; revert h; decide

/-! ### The parser inverts `Source.tokens` -/

namespace ParseState

theorem foldl_error (l : List Token) (e : ParseError) :
    l.foldl parseStep (.error e) = .error e := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem parseStep_ok (st : ParseState) (t : Token) :
    parseStep (.ok st) t = st.step t := rfl

@[simp] theorem step_kw (st : ParseState) (k : Keyword) : st.step (.kw k) = st.stepKw k := rfl

@[simp] theorem step_sym (st : ParseState) (s : String) : st.step (.sym s) = st.stepSym s := rfl

theorem foldl_decl (stmts pending : List _) (k : DeclKind) (acc ss : List String) :
    (ss.map Token.sym).foldl parseStep (.ok ⟨stmts, .decl k acc, pending⟩) =
      .ok ⟨stmts, .decl k (ss.reverse ++ acc), pending⟩ := by
  induction ss generalizing acc with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.foldl_cons, parseStep_ok, step, stepSym, goto]
    simp [ih]

theorem foldl_expr (stmts pending : List _) (k : ExprKind) (l : String) (acc ss : List String) :
    (ss.map Token.sym).foldl parseStep (.ok ⟨stmts, .expr k l acc, pending⟩) =
      .ok ⟨stmts, .expr k l (ss.reverse ++ acc), pending⟩ := by
  induction ss generalizing acc with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.foldl_cons, parseStep_ok, step, stepSym, goto]
    simp [ih]

theorem foldl_normal (stmts pending : List _) (l tc : String) (body acc ss : List String)
    (h : ∀ s ∈ ss, isProofStep s) :
    (ss.map Token.sym).foldl parseStep (.ok ⟨stmts, .normal l tc body acc, pending⟩) =
      .ok ⟨stmts, .normal l tc body (ss.reverse ++ acc), pending⟩ := by
  induction ss generalizing acc with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, List.foldl_cons, parseStep_ok, step, stepSym, goto, h.1,
      ]
    simp [ih (s :: acc) h.2]

theorem foldl_cLabels (stmts pending : List _) (l tc : String) (body acc ss : List String)
    (h : ∀ s ∈ ss, isLabel s) :
    (ss.map Token.sym).foldl parseStep (.ok ⟨stmts, .cLabels l tc body acc, pending⟩) =
      .ok ⟨stmts, .cLabels l tc body (ss.reverse ++ acc), pending⟩ := by
  induction ss generalizing acc with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, List.foldl_cons, parseStep_ok, step, stepSym, goto,
      ne_close_of_isLabel h.1, h.1]
    simp [ih (s :: acc) h.2]

theorem emit_nil (stmts : List Stmt) (m : ParseMode) (s : Stmt) :
    (⟨stmts, m, []⟩ : ParseState).emit s = ⟨s :: stmts, .top, []⟩ := rfl

/-- Reading the tokens of a valid statement records it. -/
theorem foldl_stmt (stmts : List Stmt) (s : Stmt) (h : s.valid) :
    s.tokens.foldl parseStep (.ok ⟨stmts, .top, []⟩) = .ok ⟨s :: stmts, .top, []⟩ := by
  cases s with
  | comment t => rfl
  | constants ss =>
    simp only [Stmt.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    simp [Stmt.tokens, stepKw, goto, foldl_decl, h.1, emit]
  | «variables» ss =>
    simp only [Stmt.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    simp [Stmt.tokens, stepKw, goto, foldl_decl, h.1, emit]
  | disjoint ss =>
    simp only [Stmt.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Stmt.tokens, stepKw, goto, foldl_decl, show ¬ ss.length < 2 by omega, emit]
  | floating l tc v =>
    simp only [Stmt.valid, Bool.and_eq_true] at h
    simp [Stmt.tokens, stepKw, stepSym, goto, h.1.1, emit]
  | essential l tc body =>
    simp only [Stmt.valid, Bool.and_eq_true] at h
    simp [Stmt.tokens, stepKw, stepSym, goto, h.1.1, foldl_expr, emit]
  | «axiom» l tc body =>
    simp only [Stmt.valid, Bool.and_eq_true] at h
    simp [Stmt.tokens, stepKw, stepSym, goto, h.1.1, foldl_expr, emit]
  | provable l tc body pf =>
    simp only [Stmt.valid, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hl, -⟩, -⟩, hpf⟩ := h
    simp only [Stmt.tokens, List.foldl_cons, List.foldl_append, parseStep_ok, step_sym,
      step_kw, stepSym, stepKw, goto, hl, ↓reduceIte, foldl_expr]
    cases pf with
    | normal steps =>
      simp only [ProofText.valid, List.all_eq_true] at hpf
      cases steps with
      | nil => simp [ProofText.tokens, stepKw, emit]
      | cons s steps =>
        simp only [List.mem_cons, forall_eq_or_imp] at hpf
        simp [ProofText.tokens, stepSym, goto, ne_open_of_isProofStep hpf.1, hpf.1,
          foldl_normal _ _ _ _ _ _ _ hpf.2, stepKw, emit]
    | compressed labels letters =>
      simp only [ProofText.valid, Bool.and_eq_true, List.all_eq_true] at hpf
      by_cases hs : letters = ""
      · subst hs
        simp [ProofText.tokens, stepSym, goto, foldl_cLabels _ _ _ _ _ _ _ hpf.1, stepKw, emit]
      · simp [ProofText.tokens, stepSym, goto, foldl_cLabels _ _ _ _ _ _ _ hpf.1, stepKw, emit,
          hs, hpf.2]
  | openScope => rfl
  | closeScope => rfl
  | «include» f => rfl

end ParseState

/-- The parser inverts `Source.tokens` on valid sources. -/
theorem parseTokens_tokens (src : Source) (h : src.Valid) : parseTokens src.tokens = .ok src := by
  have key : ∀ (stmts : List Stmt) (src : Source), src.Valid →
      src.tokens.foldl parseStep (.ok ⟨stmts, .top, []⟩) =
        .ok ⟨src.reverse ++ stmts, .top, []⟩ := by
    intro stmts src h
    induction src generalizing stmts with
    | nil => rfl
    | cons s src ih =>
      have hs : s.valid := h s (by simp)
      have hsrc : Source.Valid src := fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
      simp only [Source.tokens, List.flatMap_cons, List.foldl_append] at ih ⊢
      rw [ParseState.foldl_stmt _ _ hs, ih _ hsrc]
      simp
  simp [parseTokens, ParseState.init, key [] src h, Except.bind, ParseState.finish]

/-! ### The lexer inverts printing -/

theorem ne_newline_of_isPrintable {c : Char} (h : isPrintable c) : c ≠ '\n' := by
  rintro rfl; simp [isPrintable] at h

theorem isAllowed_dollar : isAllowed '$' := by decide
theorem isAllowed_open : isAllowed '(' := by decide
theorem isAllowed_close : isAllowed ')' := by decide
theorem isWs_dollar : isWs '$' = false := by decide
theorem isWs_open : isWs '(' = false := by decide

theorem wordToken_sym (line : Nat) (w : List Char) (h : '$' ∉ w) :
    wordToken line w = .ok (.sym (String.ofList w)) := by
  unfold wordToken
  split
  · simp at h
  · simp [h]

theorem wordToken_kw (line : Nat) (k : Keyword) : wordToken line ['$', k.char] = .ok (.kw k) := by
  simp [wordToken]

namespace LexState

theorem foldl_error (l : List Char) (e : LexError) : l.foldl lexStep (.error e) = .error e := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem lexStep_ok (st : LexState) (c : Char) : lexStep (.ok st) c = stepChar st c := rfl

/-- The mode of the lexer inside a comment, given the reversed text read so far. -/
def cmtMode : List Char → LexMode
  | [] => .cmt [] true
  | c :: acc =>
    if c = '$' then .cmtDollar (c :: acc) (acc.head?.any isWs) else .cmt (c :: acc) (isWs c)

/-- After the last character of a token, in mode `m`, white space or the end
of the input emits the token `t`. -/
def Pending (t : Token) (m : LexMode) : Prop :=
  (∀ toks line c, isWs c →
    ∃ line', stepChar ⟨toks, m, line⟩ c = .ok ⟨t :: toks, .ws, line'⟩) ∧
  ∀ toks line, finish ⟨toks, m, line⟩ = .ok (t :: toks).reverse

theorem foldl_ws (toks : List Token) (w : List Char) (hw : ∀ c ∈ w, isWs c) (line : Nat) :
    ∃ line', w.foldl lexStep (.ok ⟨toks, .ws, line⟩) = .ok ⟨toks, .ws, line'⟩ := by
  induction w generalizing line with
  | nil => exact ⟨line, rfl⟩
  | cons c w ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hw
    simp only [List.foldl_cons, lexStep_ok, stepChar, isAllowed_of_isWs hw.1, hw.1,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ih hw.2 _

theorem foldl_word (toks : List Token) (w acc : List Char) (hw : ∀ c ∈ w, isPrintable c)
    (line : Nat) : ∃ line', w.foldl lexStep (.ok ⟨toks, .word acc, line⟩) =
      .ok ⟨toks, .word (w.reverse ++ acc), line'⟩ := by
  induction w generalizing acc line with
  | nil => exact ⟨line, rfl⟩
  | cons c w ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hw
    simp only [List.foldl_cons, lexStep_ok, stepChar, isAllowed_of_isPrintable hw.1,
      isWs_eq_false_of_isPrintable hw.1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨line', h⟩ := ih (c :: acc) hw.2 _
    exact ⟨line', by simpa using h⟩

theorem foldl_cmt (toks : List Token) (c : Char) (acc rest : List Char)
    (hall : ∀ d ∈ rest, isAllowed d) (hnd : noCommentDelim (c :: rest)) (line : Nat) :
    ∃ line', rest.foldl lexStep (.ok ⟨toks, cmtMode (c :: acc), line⟩) =
      .ok ⟨toks, cmtMode (rest.reverse ++ c :: acc), line'⟩ := by
  induction rest generalizing c acc line with
  | nil => exact ⟨line, rfl⟩
  | cons d rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hall
    rw [noCommentDelim, Bool.and_eq_true] at hnd
    have hstep : stepChar ⟨toks, cmtMode (c :: acc), line⟩ d =
        .ok ⟨toks, cmtMode (d :: c :: acc), if d = '\n' then line + 1 else line⟩ := by
      by_cases hc : c = '$'
      · subst hc
        have hd : d ≠ '(' ∧ d ≠ ')' := by simpa using hnd.1
        by_cases hd' : d = '$'
        · subst hd'; simp [stepChar, cmtMode, isWs_dollar, isAllowed_dollar]
        · simp [stepChar, cmtMode, hall.1, hd.1, hd.2, hd']
      · by_cases hd' : d = '$'
        · subst hd'; simp [stepChar, cmtMode, hc, isAllowed_dollar]
        · simp [stepChar, cmtMode, hall.1, hc, hd']
    simp only [List.foldl_cons, lexStep_ok, hstep]
    obtain ⟨line'', h'⟩ := ih d (c :: acc) hall.2 hnd.2 _
    exact ⟨line'', by simpa using h'⟩

theorem pending_word (w : List Char) (h : w.reverse ≠ ['(', '$'])
    (t : Token) (ht : ∀ line, wordToken line w = .ok t) : Pending t (.word w.reverse) := by
  refine ⟨fun toks line c hc => ?_, fun toks line => ?_⟩
  · simp [stepChar, isAllowed_of_isWs hc, hc, h, ht, Except.map]
  · simp [finish, h, ht, Except.map]

theorem foldl_token (toks : List Token) (t : Token) (ht : t.valid) (line : Nat) :
    ∃ m line', t.chars.foldl lexStep (.ok ⟨toks, .ws, line⟩) = .ok ⟨toks, m, line'⟩ ∧
      Pending t m := by
  cases t with
  | kw k =>
    have hk : isPrintable k.char := k.isPrintable_char
    refine ⟨.word [k.char, '$'], line, ?_, ?_⟩
    · simp [Token.chars, stepChar, isAllowed_of_isPrintable hk, isWs_eq_false_of_isPrintable hk,
        isAllowed_dollar, isWs_dollar, ne_newline_of_isPrintable hk]
    · exact pending_word ['$', k.char] (by simp) _ (fun line => wordToken_kw line k)
  | sym s =>
    obtain ⟨hne, hs⟩ := isMathSymbol_iff.1 ht
    have hd : '$' ∉ s.toList := fun h => (hs _ h).2 rfl
    obtain ⟨c, w, hcw⟩ := List.exists_cons_of_ne_nil hne
    have hc := hs c (by simp [hcw])
    obtain ⟨line', hw⟩ := foldl_word toks w [c] (fun d hd => (hs d (by simp [hcw, hd])).1)
      (if c = '\n' then line + 1 else line)
    refine ⟨.word s.toList.reverse, line', ?_, ?_⟩
    · simp only [Token.chars, hcw, List.foldl_cons, lexStep_ok, stepChar,
        isAllowed_of_isPrintable hc.1, isWs_eq_false_of_isPrintable hc.1, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, hw]
      simp
    · refine pending_word s.toList ?_ _
        (fun line => by rw [wordToken_sym line _ hd, String.ofList_toList])
      intro h
      apply hd
      have : s.toList = ['$', '('] := by simpa using congrArg List.reverse h
      simp [this]
  | comment txt =>
    simp only [Token.valid, isCommentText, Bool.and_eq_true, List.all_eq_true] at ht
    obtain ⟨⟨⟨hfirst, hlast⟩, hall⟩, hnd⟩ := ht
    obtain ⟨c, rest, hcr⟩ := List.exists_cons_of_ne_nil
      (fun h => by simp [h] at hfirst : txt.toList ≠ [])
    have hc : isWs c := by simpa [hcr] using hfirst
    rw [hcr] at hall hnd
    simp only [List.mem_cons, forall_eq_or_imp] at hall
    obtain ⟨line', hcmt⟩ := foldl_cmt toks c [] rest hall.2 hnd
      (if c = '\n' then line + 1 else line)
    have hstart : List.foldl lexStep (.ok ⟨toks, .ws, line⟩) ['$', '(', c] =
        .ok ⟨toks, cmtMode [c], if c = '\n' then line + 1 else line⟩ := by
      simp [stepChar, hc, cmtMode, ne_dollar_of_isWs hc, isAllowed_of_isWs hc, isAllowed_dollar,
        isWs_dollar, isAllowed_open, isWs_open]
    obtain ⟨e, r, her⟩ : ∃ e r, rest.reverse ++ [c] = e :: r := by
      cases h : rest.reverse ++ [c] with
      | nil => simp at h
      | cons e r => exact ⟨e, r, rfl⟩
    have htxt : txt.toList.reverse = e :: r := by simpa [hcr] using her
    have he : isWs e := by simpa [htxt] using hlast
    have hmode : cmtMode (rest.reverse ++ [c]) = .cmt (e :: r) true := by
      simp [her, cmtMode, ne_dollar_of_isWs he, he]
    refine ⟨.cmtEnd (e :: r), line', ?_, ?_, ?_⟩
    · have hsplit : (Token.comment txt).chars = ['$', '(', c] ++ rest ++ ['$', ')'] := by
        simp [Token.chars, hcr]
      rw [hsplit, List.foldl_append, List.foldl_append, hstart, hcmt]
      simp [hmode, stepChar, isAllowed_dollar, isAllowed_close]
    · intro toks line d hd
      refine ⟨if d = '\n' then line + 1 else line, ?_⟩
      simp [stepChar, isAllowed_of_isWs hd, hd, ← htxt]
    · intro toks line
      simp [finish, ← htxt]

/-- Lexing tokens each followed by nonempty white space. -/
theorem foldl_pieces (ps : List (Token × List Char))
    (h : ∀ p ∈ ps, p.1.valid ∧ p.2 ≠ [] ∧ ∀ c ∈ p.2, isWs c) (toks : List Token) (line : Nat) :
    ∃ line', (ps.flatMap fun p => p.1.chars ++ p.2).foldl lexStep (.ok ⟨toks, .ws, line⟩) =
      .ok ⟨(ps.map Prod.fst).reverse ++ toks, .ws, line'⟩ := by
  induction ps generalizing toks line with
  | nil => exact ⟨line, rfl⟩
  | cons p ps ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨⟨hv, hne, hws⟩, hps⟩ := h
    obtain ⟨m, line₁, htok, hpend⟩ := foldl_token toks p.1 hv line
    obtain ⟨c, w, hcw⟩ := List.exists_cons_of_ne_nil hne
    rw [hcw] at hws
    simp only [List.mem_cons, forall_eq_or_imp] at hws
    obtain ⟨line₂, hc⟩ := hpend.1 toks line₁ c hws.1
    obtain ⟨line₃, hw⟩ := foldl_ws (p.1 :: toks) w hws.2 line₂
    obtain ⟨line₄, hrest⟩ := ih hps (p.1 :: toks) line₃
    refine ⟨line₄, ?_⟩
    simp only [List.flatMap_cons, List.foldl_append, htok, hcw, List.foldl_cons, lexStep_ok, hc,
      hw, hrest, List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append]

end LexState

/-- The lexer inverts printing valid tokens, each followed by nonempty white
space, after leading white space. -/
theorem lexChars_pieces (lead : List Char) (hlead : ∀ c ∈ lead, isWs c)
    (ps : List (Token × List Char)) (h : ∀ p ∈ ps, p.1.valid ∧ p.2 ≠ [] ∧ ∀ c ∈ p.2, isWs c) :
    lexChars (lead ++ ps.flatMap fun p => p.1.chars ++ p.2) = .ok (ps.map Prod.fst) := by
  obtain ⟨line₁, h₁⟩ := LexState.foldl_ws [] lead hlead 1
  obtain ⟨line₂, h₂⟩ := LexState.foldl_pieces ps h [] line₁
  simp [lexChars, LexState.init, List.foldl_append, h₁, h₂, LexState.finish, Except.bind]

/-- The lexer inverts `printTokens` on valid tokens. -/
theorem lexChars_printTokens (ts : List Token) (h : ∀ t ∈ ts, t.valid) :
    lexChars (printTokens ts).toList = .ok ts := by
  have key : ∀ (ts : List Token), (∀ t ∈ ts, t.valid) → ∀ toks line,
      ((printTokens ts).toList.foldl lexStep (.ok ⟨toks, .ws, line⟩)).bind LexState.finish =
        .ok (ts.reverse ++ toks).reverse := by
    intro ts h
    induction ts with
    | nil => intro toks line; simp [printTokens, LexState.finish, Except.bind]
    | cons t ts ih =>
      intro toks line
      simp only [List.mem_cons, forall_eq_or_imp] at h
      obtain ⟨m, line₁, htok, hpend⟩ := LexState.foldl_token toks t h.1 line
      cases ts with
      | nil => simp [printTokens, htok, Except.bind, hpend.2]
      | cons t' ts =>
        obtain ⟨line₂, hsp⟩ := hpend.1 toks line₁ ' ' (by decide)
        have := ih h.2 (t :: toks) line₂
        simp only [printTokens, String.toList_append, Token.toList_print, List.foldl_append,
          htok] at this ⊢
        simp [hsp, this]
  simpa [lexChars, LexState.init] using key ts h [] 1

/-! ### Printing then parsing a source -/

/-- The pieces of `printLine`: each token is followed by a space, the last by a line feed. -/
def linePieces : List Token → List (Token × List Char)
  | [] => []
  | [t] => [(t, ['\n'])]
  | t :: ts => (t, [' ']) :: linePieces ts

theorem linePieces_cons_cons (t t' : Token) (ts : List Token) :
    linePieces (t :: t' :: ts) = (t, [' ']) :: linePieces (t' :: ts) := rfl

theorem map_fst_linePieces (ts : List Token) : (linePieces ts).map Prod.fst = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases ts with
    | nil => rfl
    | cons t' ts => rw [linePieces_cons_cons, List.map_cons, ih]

theorem toList_printLine (ts : List Token) :
    (printLine ts).toList = (linePieces ts).flatMap fun p => p.1.chars ++ p.2 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases ts with
    | nil => simp [printLine, linePieces]
    | cons t' ts => simp [printLine, linePieces_cons_cons, ih]

theorem mem_linePieces {ts : List Token} {p : Token × List Char} (h : p ∈ linePieces ts) :
    p.1 ∈ ts ∧ p.2 ≠ [] ∧ ∀ c ∈ p.2, isWs c := by
  induction ts with
  | nil => simp [linePieces] at h
  | cons t ts ih =>
    cases ts with
    | nil =>
      simp only [linePieces, List.mem_singleton] at h
      subst h
      simp [isWs]
    | cons t' ts =>
      rw [linePieces_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp [isWs]
      · obtain ⟨h1, h2⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- The tokens of a valid statement are valid. -/
theorem Stmt.valid_tokens {s : Stmt} (h : s.valid) : ∀ t ∈ s.tokens, t.valid := by
  have syms : ∀ ss : List String, (∀ s ∈ ss, isMathSymbol s) →
      ∀ t ∈ ss.map Token.sym, t.valid := by
    intro ss h t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    exact h s hs
  cases s with
  | comment t => simpa [Stmt.tokens, Token.valid, Stmt.valid] using h
  | constants ss | «variables» ss | disjoint ss =>
    simp only [Stmt.valid, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Stmt.tokens, List.mem_cons, List.mem_append, or_assoc,
      List.not_mem_nil, or_false]
    rintro t (rfl | ht | rfl)
    · rfl
    · exact syms ss h.2 t ht
    · rfl
  | floating l tc v =>
    simp only [Stmt.valid, Bool.and_eq_true] at h
    simp only [Stmt.tokens, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl | rfl | rfl)
    · exact isMathSymbol_of_isLabel h.1.1
    · rfl
    · exact h.1.2
    · exact h.2
    · rfl
  | essential l tc body | «axiom» l tc body =>
    simp only [Stmt.valid, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Stmt.tokens, List.mem_cons, List.mem_append, or_assoc,
      List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl | ht | rfl)
    · exact isMathSymbol_of_isLabel h.1.1
    · rfl
    · exact h.1.2
    · exact syms body h.2 t ht
    · rfl
  | provable l tc body pf =>
    simp only [Stmt.valid, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨hl, htc⟩, hbody⟩, hpf⟩ := h
    simp only [Stmt.tokens, List.mem_cons, List.mem_append, or_assoc,
      List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl | ht | rfl | ht | rfl)
    · exact isMathSymbol_of_isLabel hl
    · rfl
    · exact htc
    · exact syms body hbody t ht
    · rfl
    · cases pf with
      | normal steps =>
        simp only [ProofText.valid, List.all_eq_true] at hpf
        exact syms steps (fun s hs => isMathSymbol_of_isProofStep (hpf s hs)) t ht
      | compressed labels letters =>
        simp only [ProofText.valid, Bool.and_eq_true, List.all_eq_true] at hpf
        simp only [ProofText.tokens, List.mem_cons, List.mem_append, or_assoc] at ht
        rcases ht with rfl | ht | rfl | ht
        · decide
        · exact syms labels (fun s hs => isMathSymbol_of_isLabel (hpf.1 s hs)) t ht
        · decide
        · split at ht
          · simp at ht
          · rename_i hne
            simp only [List.mem_singleton] at ht
            subst ht
            exact isMathSymbol_of_isLetterToken hpf.2 hne
    · rfl
  | openScope | closeScope => simp [Stmt.tokens, Token.valid]
  | «include» f =>
    simp only [Stmt.tokens, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl)
    · rfl
    · exact h
    · rfl

theorem toList_print (src : Source) :
    src.print.toList =
      (src.flatMap fun s => linePieces s.tokens).flatMap fun p => p.1.chars ++ p.2 := by
  induction src with
  | nil => simp [Source.print]
  | cons s src ih =>
    simp only [Source.print, List.map_cons, String.join_cons, String.toList_append] at ih ⊢
    rw [ih, Stmt.print, toList_printLine]
    simp

/-- The lexer inverts printing on valid sources. -/
theorem lexChars_print (src : Source) (h : src.Valid) :
    lexChars src.print.toList = .ok src.tokens := by
  have := lexChars_pieces [] (by simp) (src.flatMap fun s => linePieces s.tokens) (by
    intro p hp
    obtain ⟨s, hs, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨h1, h2⟩ := mem_linePieces hp
    exact ⟨Stmt.valid_tokens (h s hs) _ h1, h2⟩)
  simpa [toList_print, List.map_flatMap, map_fst_linePieces, Source.tokens] using this

/-- **Round trip.** Printing a valid source and parsing the text gives it back. -/
theorem parse_print (src : Source) (h : src.Valid) : parse src.print = .ok src := by
  rw [parse_eq_parseChars, parseChars, lexChars_print src h]
  simp [parseTokens_tokens src h, Except.mapError]

/-- Printing is injective on valid sources. -/
theorem print_injective {src src' : Source} (h : src.Valid) (h' : src'.Valid)
    (e : src.print = src'.print) : src = src' := by
  have := parse_print src h
  rw [e, parse_print src' h'] at this
  exact (Except.ok.inj this).symm

end Silmaril.Logic.Metamath.Text
