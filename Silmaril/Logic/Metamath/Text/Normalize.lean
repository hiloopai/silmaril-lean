module

public import Silmaril.Logic.Metamath.Text.RoundTrip

@[expose] public section

/-!
# Parsing produces valid sources

The converse direction of the round trip. The lexer only produces valid
tokens (`lexChars_valid`) and the parser only produces valid statements from
valid tokens (`parseTokens_valid`), so every parsed source is valid
(`parse_valid`). Together with `parse_print`:

* `parse_print_eq_ok_iff`: `parse src.print = .ok src` exactly when `src` is
  valid, so `Source.Valid` is precisely the set of printable sources;
* `parse_print_of_parse`: printing a parsed source and parsing it again gives
  the same source. The printer is a normal form of the text format: it changes
  white space and moves comments found inside a statement after it.
-/

namespace Silmaril.Logic.Metamath.Text

/-! ### Comment text -/

theorem noCommentDelim_append_singleton (l : List Char) (c : Char) :
    noCommentDelim (l ++ [c]) =
      (noCommentDelim l && (l.getLast? != some '$' || (c != '(' && c != ')'))) := by
  induction l with
  | nil => simp [noCommentDelim]
  | cons a l ih =>
    cases l with
    | nil =>
      have : (some a != some '$') = (a != '$') := by
        by_cases ha : a = '$'
        · subst ha; rfl
        · simp [bne]
      simp [noCommentDelim, this]
    | cons b l =>
      simp only [List.cons_append, noCommentDelim] at ih ⊢
      rw [ih]
      simp only [List.getLast?_cons_cons]
      cases noCommentDelim (b :: l) <;> simp [Bool.and_comm, Bool.and_left_comm]

theorem isPrintable_of_isAllowed {c : Char} (h : isAllowed c) (hw : isWs c = false) :
    isPrintable c := by
  simpa [isAllowed, hw] using h

namespace LexState

/-- The reversed text `acc` of an open comment is well formed so far. -/
def GoodCmt (acc : List Char) : Prop :=
  acc ≠ [] ∧ acc.reverse.head?.any isWs ∧ (∀ c ∈ acc, isAllowed c) ∧
    noCommentDelim acc.reverse

/-- The invariant of the lexer modes. -/
def ModeInv : LexMode → Prop
  | .ws => True
  | .word acc => acc ≠ [] ∧ ∀ c ∈ acc, isPrintable c
  | .cmt acc b => GoodCmt acc ∧ cmtMode acc = .cmt acc b
  | .cmtDollar acc b => GoodCmt acc ∧ cmtMode acc = .cmtDollar acc b
  | .cmtEnd acc => isCommentText (String.ofList acc.reverse)

/-- The invariant of the lexer states: the tokens so far are valid. -/
def Inv (st : LexState) : Prop := (∀ t ∈ st.toks, t.valid) ∧ ModeInv st.mode

theorem wordToken_valid {line : Nat} {w : List Char} {t : Token} (hne : w ≠ [])
    (hw : ∀ c ∈ w, isPrintable c) (h : wordToken line w = .ok t) : t.valid := by
  unfold wordToken at h
  split at h
  · split at h
    · cases h; rfl
    · split at h <;> cases h
  · split at h
    · cases h
    · cases h
      rename_i hd
      refine isMathSymbol_iff.2 ⟨by simpa using hne, fun c hc => ⟨hw c (by simpa using hc), ?_⟩⟩
      rintro rfl
      exact hd (by simpa using hc)

theorem goodCmt_cons {acc : List Char} {c : Char} (hg : GoodCmt acc) (hc : isAllowed c)
    (hd : acc.head? = some '$' → c ≠ '(' ∧ c ≠ ')') : GoodCmt (c :: acc) := by
  obtain ⟨hne, hfirst, hall, hnd⟩ := hg
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simpa [List.head?_append] using hfirst
  · simp only [List.mem_cons, forall_eq_or_imp] at hall ⊢
    exact ⟨hc, hall⟩
  · rw [List.reverse_cons, noCommentDelim_append_singleton]
    simp only [hnd, Bool.true_and, List.getLast?_reverse, List.head?_cons]
    by_cases ha : a = '$'
    · subst ha
      have := hd rfl
      simp [this.1, this.2]
    · simp [bne, ha]

theorem modeInv_cmtMode {c : Char} {acc : List Char} (hg : GoodCmt (c :: acc)) :
    ModeInv (cmtMode (c :: acc)) := by
  by_cases hc : c = '$'
  · simp only [cmtMode, hc, ↓reduceIte, ModeInv]
    exact ⟨hc ▸ hg, by simp⟩
  · simp only [cmtMode, hc, ↓reduceIte, ModeInv]
    exact ⟨hg, by simp⟩

theorem stepChar_inv {st st' : LexState} {c : Char} (h : Inv st) (hs : stepChar st c = .ok st') :
    Inv st' := by
  obtain ⟨toks, mode, line⟩ := st
  obtain ⟨htoks, hmode⟩ := h
  unfold stepChar at hs
  by_cases hal : isAllowed c
  swap
  · simp [hal] at hs
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
  cases mode with
  | ws =>
    cases hs
    refine ⟨htoks, ?_⟩
    by_cases hw : isWs c
    · simp [hw, ModeInv]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, ModeInv]
      exact ⟨by simp, by simpa using isPrintable_of_isAllowed hal (by simpa using hw)⟩
  | word acc =>
    obtain ⟨hne, hpr⟩ := hmode
    by_cases hw : isWs c
    · simp only [hw, ↓reduceIte] at hs
      by_cases hc : acc = ['(', '$']
      · simp only [hc, ↓reduceIte, Except.ok.injEq] at hs
        subst hs
        refine ⟨htoks, ?_, ?_⟩
        · exact ⟨by simp, by simp [hw], by simp [hal], by simp [noCommentDelim]⟩
        · simp [cmtMode, ne_dollar_of_isWs hw, hw]
      · simp only [hc, ↓reduceIte] at hs
        cases ht : wordToken line acc.reverse with
        | error e => simp [ht, Except.map] at hs
        | ok t =>
          simp only [ht, Except.map, Except.ok.injEq] at hs
          subst hs
          refine ⟨?_, trivial⟩
          simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨wordToken_valid (by simpa using hne) (by simpa using hpr) ht, htoks⟩
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hs
      subst hs
      refine ⟨htoks, by simp, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨isPrintable_of_isAllowed hal (by simpa using hw), hpr⟩
  | cmt acc b =>
    obtain ⟨hg, hm⟩ := hmode
    obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hg.1
    have ha : a ≠ '$' := by
      intro ha
      simp [cmtMode, ha] at hm
    have hb : b = isWs a := by
      simp only [cmtMode, ha, ↓reduceIte, LexMode.cmt.injEq, true_and] at hm
      exact hm.symm
    have hg' : GoodCmt (c :: a :: r) := goodCmt_cons hg hal (by simp [ha])
    simp only [Except.ok.injEq] at hs
    subst hs
    refine ⟨htoks, ?_⟩
    have := modeInv_cmtMode hg'
    by_cases hc : c = '$'
    · simpa [cmtMode, hc, hb] using this
    · simpa [cmtMode, hc] using this
  | cmtDollar acc b =>
    obtain ⟨hg, hm⟩ := hmode
    obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hg.1
    have ha : a = '$' := by
      by_contra ha
      simp [cmtMode, ha] at hm
    subst ha
    have hb : b = r.head?.any isWs := by
      simp only [cmtMode, ↓reduceIte, LexMode.cmtDollar.injEq, true_and] at hm
      exact hm.symm
    by_cases ho : c = '('
    · simp [ho] at hs
    by_cases hcl : c = ')'
    · subst hcl
      by_cases hwb : b
      · simp only [hwb, ho, ↓reduceIte, Except.ok.injEq] at hs
        subst hs
        refine ⟨htoks, ?_⟩
        obtain ⟨-, hfirst, hall, hnd⟩ := hg
        subst hb
        obtain ⟨e, r', rfl⟩ : ∃ e r', r = e :: r' := by
          cases r with
          | nil => simp at hwb
          | cons e r' => exact ⟨e, r', rfl⟩
        simp only [List.head?_cons, Option.any_some] at hwb
        simp only [ModeInv, isCommentText, String.toList_ofList, List.tail_cons,
          List.reverse_reverse, List.head?_cons, Option.any_some, hwb, Bool.and_true,
          Bool.and_eq_true, List.all_eq_true]
        refine ⟨⟨?_, fun x hx => hall x (by simp at hx ⊢; tauto)⟩, ?_⟩
        · simpa [List.head?_append] using hfirst
        · rw [List.reverse_cons, noCommentDelim_append_singleton] at hnd
          simpa using hnd
      · simp [hwb] at hs
    · simp only [ho, hcl, ↓reduceIte, Except.ok.injEq] at hs
      subst hs
      refine ⟨htoks, ?_⟩
      have hg' : GoodCmt (c :: '$' :: r) := goodCmt_cons hg hal (by simp [ho, hcl])
      have := modeInv_cmtMode hg'
      by_cases hc : c = '$'
      · simpa [cmtMode, hc, isWs_dollar] using this
      · simpa [cmtMode, hc] using this
  | cmtEnd acc =>
    by_cases hw : isWs c
    · simp only [hw, ↓reduceIte, Except.ok.injEq] at hs
      subst hs
      refine ⟨?_, trivial⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hmode, htoks⟩
    · simp [hw] at hs

theorem finish_valid {st : LexState} {ts : List Token} (h : Inv st) (hf : st.finish = .ok ts) :
    ∀ t ∈ ts, t.valid := by
  obtain ⟨toks, mode, line⟩ := st
  obtain ⟨htoks, hmode⟩ := h
  cases mode with
  | ws =>
    simp only [finish, Except.ok.injEq] at hf
    subst hf
    simpa using htoks
  | word acc =>
    obtain ⟨hne, hpr⟩ := hmode
    simp only [finish] at hf
    split at hf
    · cases hf
    · cases ht : wordToken line acc.reverse with
      | error e => simp [ht, Except.map] at hf
      | ok t =>
        simp only [ht, Except.map, Except.ok.injEq] at hf
        subst hf
        simp only [List.mem_reverse, List.mem_cons, forall_eq_or_imp]
        exact ⟨wordToken_valid (by simpa using hne) (by simpa using hpr) ht, htoks⟩
  | cmt | cmtDollar => simp [finish] at hf
  | cmtEnd acc =>
    simp only [finish, Except.ok.injEq] at hf
    subst hf
    simp only [List.mem_reverse, List.mem_cons, forall_eq_or_imp]
    exact ⟨hmode, htoks⟩

end LexState

/-- The lexer only produces valid tokens. -/
theorem lexChars_valid {l : List Char} {ts : List Token} (h : lexChars l = .ok ts) :
    ∀ t ∈ ts, t.valid := by
  have key : ∀ (l : List Char) (st : LexState), LexState.Inv st →
      ∀ st', l.foldl lexStep (.ok st) = .ok st' → LexState.Inv st' := by
    intro l
    induction l with
    | nil => intro st h st' e; cases e; exact h
    | cons c l ih =>
      intro st h st' e
      simp only [List.foldl_cons, LexState.lexStep_ok] at e
      cases hs : stepChar st c with
      | error err => rw [hs, LexState.foldl_error] at e; cases e
      | ok st₁ => rw [hs] at e; exact ih st₁ (LexState.stepChar_inv h hs) st' e
  unfold lexChars at h
  cases hf : l.foldl lexStep (.ok .init) with
  | error e => simp [hf, Except.bind] at h
  | ok st =>
    simp only [hf, Except.bind] at h
    exact LexState.finish_valid (key l .init ⟨by simp [LexState.init], trivial⟩ st hf) h

/-! ### The parser -/

theorem isLetterToken_join {l : List String} (h : ∀ s ∈ l, isLetterToken s) :
    isLetterToken (String.join l) := by
  simp only [isLetterToken, List.all_eq_true, String.toList_join, List.mem_flatMap] at h ⊢
  rintro c ⟨s, hs, hc⟩
  exact h s hs c hc

namespace ParseState

/-- The header of a `$p` statement read so far is well formed. -/
def HeadInv (l tc : String) (body : List String) : Prop :=
  isLabel l ∧ isMathSymbol tc ∧ ∀ s ∈ body, isMathSymbol s

/-- The invariant of the parser modes. -/
def ModeInv : ParseMode → Prop
  | .top => True
  | .decl _ acc => ∀ s ∈ acc, isMathSymbol s
  | .label l => isLabel l
  | .float l acc => isLabel l ∧ ∀ s ∈ acc, isMathSymbol s
  | .expr _ l acc => isLabel l ∧ ∀ s ∈ acc, isMathSymbol s
  | .proofStart l tc body => HeadInv l tc body
  | .normal l tc body steps => HeadInv l tc body ∧ ∀ s ∈ steps, isProofStep s
  | .cLabels l tc body labels => HeadInv l tc body ∧ ∀ s ∈ labels, isLabel s
  | .cLetters l tc body labels letters =>
    HeadInv l tc body ∧ (∀ s ∈ labels, isLabel s) ∧ ∀ s ∈ letters, isLetterToken s
  | .incl => True
  | .inclFile f => isMathSymbol f

/-- The invariant of the parser states: the statements and pending comments so
far are valid. -/
def Inv (st : ParseState) : Prop :=
  (∀ s ∈ st.stmts, s.valid) ∧ (∀ t ∈ st.pending, isCommentText t) ∧ ModeInv st.mode

theorem emit_inv {st : ParseState} {s : Stmt} (h : Inv st) (hs : s.valid) : Inv (st.emit s) := by
  obtain ⟨hstmts, hpend, -⟩ := h
  refine ⟨?_, by simp [emit], trivial⟩
  simp only [emit, List.mem_append, List.mem_map, List.mem_cons]
  rintro s' (⟨t, ht, e⟩ | rfl | hs')
  · subst e; exact hpend t ht
  · exact hs
  · exact hstmts s' hs'

theorem goto_inv {st : ParseState} {m : ParseMode} (h : Inv st) (hm : ModeInv m) :
    Inv (st.goto m) := ⟨h.1, h.2.1, hm⟩

@[simp] theorem fail_ne_ok {α : Type} (st : ParseState) (msg : String) (a : α) :
    st.fail msg ≠ .ok a := by
  simp [fail]

theorem stepSym_inv {st st' : ParseState} {s : String} (h : Inv st) (hs : isMathSymbol s)
    (e : st.stepSym s = .ok st') : Inv st' := by
  obtain ⟨stmts, mode, pending⟩ := st
  have hm := h.2.2
  cases mode with
  | top =>
    by_cases hl : isLabel s
    · simp only [stepSym, hl, ↓reduceIte, Except.ok.injEq] at e
      subst e; exact goto_inv h hl
    · simp [stepSym, hl] at e
  | decl k acc =>
    simp only [stepSym, Except.ok.injEq] at e
    subst e; exact goto_inv h (List.forall_mem_cons.2 ⟨hs, hm⟩)
  | label l => simp [stepSym] at e
  | float l acc =>
    simp only [stepSym, Except.ok.injEq] at e
    subst e; exact goto_inv h ⟨hm.1, List.forall_mem_cons.2 ⟨hs, hm.2⟩⟩
  | expr k l acc =>
    simp only [stepSym, Except.ok.injEq] at e
    subst e; exact goto_inv h ⟨hm.1, List.forall_mem_cons.2 ⟨hs, hm.2⟩⟩
  | proofStart l tc body =>
    by_cases ho : s = "("
    · simp only [stepSym, ho, ↓reduceIte, Except.ok.injEq] at e
      subst e; exact goto_inv h ⟨hm, by simp⟩
    · by_cases hp : isProofStep s
      · simp only [stepSym, ho, hp, ↓reduceIte, Except.ok.injEq] at e
        subst e; exact goto_inv h ⟨hm, by simpa using hp⟩
      · simp [stepSym, ho, hp] at e
  | normal l tc body steps =>
    by_cases hp : isProofStep s
    · simp only [stepSym, hp, ↓reduceIte, Except.ok.injEq] at e
      subst e; exact goto_inv h ⟨hm.1, List.forall_mem_cons.2 ⟨hp, hm.2⟩⟩
    · simp [stepSym, hp] at e
  | cLabels l tc body labels =>
    by_cases hc : s = ")"
    · simp only [stepSym, hc, ↓reduceIte, Except.ok.injEq] at e
      subst e; exact goto_inv h ⟨hm.1, hm.2, by simp⟩
    · by_cases hl : isLabel s
      · simp only [stepSym, hc, hl, ↓reduceIte, Except.ok.injEq] at e
        subst e; exact goto_inv h ⟨hm.1, List.forall_mem_cons.2 ⟨hl, hm.2⟩⟩
      · simp [stepSym, hc, hl] at e
  | cLetters l tc body labels letters =>
    by_cases hl : isLetterToken s
    · simp only [stepSym, hl, ↓reduceIte, Except.ok.injEq] at e
      subst e; exact goto_inv h ⟨hm.1, hm.2.1, List.forall_mem_cons.2 ⟨hl, hm.2.2⟩⟩
    · simp [stepSym, hl] at e
  | incl =>
    simp only [stepSym, Except.ok.injEq] at e
    subst e; exact goto_inv h hs
  | inclFile f => simp [stepSym] at e

theorem stepKw_inv {st st' : ParseState} {k : Keyword} (h : Inv st)
    (e : st.stepKw k = .ok st') : Inv st' := by
  have hm := h.2.2
  unfold stepKw at e
  split at e <;> (try split at e) <;> (try exact absurd e (fail_ne_ok _ _ _)) <;> cases e
  all_goals first
    | exact goto_inv h (by simp_all [ModeInv, HeadInv])
    | exact emit_inv h
        (by simp_all [Stmt.valid, ModeInv, HeadInv, ProofText.valid, isLetterToken_join])

theorem step_inv {st st' : ParseState} {t : Token} (h : Inv st) (ht : t.valid)
    (e : st.step t = .ok st') : Inv st' := by
  cases t with
  | kw k => exact stepKw_inv h e
  | sym s => exact stepSym_inv h ht e
  | comment text =>
    obtain ⟨hstmts, hpend, hm⟩ := h
    simp only [step] at e
    split at e <;> cases e
    · refine ⟨?_, by simp, trivial⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨ht, hstmts⟩
    · refine ⟨hstmts, ?_, hm⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨ht, hpend⟩

end ParseState

/-- The parser produces valid sources from valid tokens. -/
theorem parseTokens_valid {ts : List Token} {src : Source} (hts : ∀ t ∈ ts, t.valid)
    (h : parseTokens ts = .ok src) : src.Valid := by
  have key : ∀ (ts : List Token), (∀ t ∈ ts, t.valid) → ∀ st, ParseState.Inv st →
      ∀ st', ts.foldl parseStep (.ok st) = .ok st' → ParseState.Inv st' := by
    intro ts hts
    induction ts with
    | nil => intro st h st' e; cases e; exact h
    | cons t ts ih =>
      intro st h st' e
      simp only [List.mem_cons, forall_eq_or_imp] at hts
      simp only [List.foldl_cons, ParseState.parseStep_ok] at e
      cases hs : st.step t with
      | error err => rw [hs, ParseState.foldl_error] at e; cases e
      | ok st₁ => rw [hs] at e; exact ih hts.2 st₁ (ParseState.step_inv h hts.1 hs) st' e
  unfold parseTokens at h
  cases hf : ts.foldl parseStep (.ok .init) with
  | error e => simp [hf, Except.bind] at h
  | ok st =>
    simp only [hf, Except.bind] at h
    have hinv := key ts hts .init ⟨by simp [ParseState.init], by simp [ParseState.init], trivial⟩
      st hf
    unfold ParseState.finish at h
    split at h
    · cases h
      intro s hs
      exact hinv.1 s (by simpa using hs)
    · exact absurd h (ParseState.fail_ne_ok _ _ _)

/-- Every parsed source is valid. -/
theorem parseChars_valid {l : List Char} {src : Source} (h : parseChars l = .ok src) :
    src.Valid := by
  unfold parseChars at h
  split at h
  · cases h
  · rename_i ts hts
    cases hp : parseTokens ts with
    | error e => simp [hp, Except.mapError] at h
    | ok src' =>
      simp only [hp, Except.mapError, Except.ok.injEq] at h
      subst h
      exact parseTokens_valid (lexChars_valid hts) hp

/-- Every parsed source is valid. -/
theorem parse_valid {s : String} {src : Source} (h : parse s = .ok src) : src.Valid :=
  parseChars_valid (by rwa [← parse_eq_parseChars])

/-- **Normal form.** Printing a parsed source and parsing it again gives the
same source. -/
theorem parse_print_of_parse {s : String} {src : Source} (h : parse s = .ok src) :
    parse src.print = .ok src :=
  parse_print src (parse_valid h)

/-- A source round-trips through the printer exactly when it is valid. -/
theorem parse_print_eq_ok_iff {src : Source} : parse src.print = .ok src ↔ src.Valid :=
  ⟨parse_valid, parse_print src⟩

end Silmaril.Logic.Metamath.Text
