module

public import Silmaril.Wasm.Component.Wat.Sexp.Defs

/-!
# S-expressions of WAT: the printer's output reads back

`read (print s) = some [s]` and `read (printAll ss) = some ss` for well-formed
S-expressions: the lexer turns the printed characters into the tokens `toks s`
(`lex_pp`), and the tree parser rebuilds `s` from them (`parseSeq_toksL`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat.Sexp

/-! ## The lexer on printed pieces -/

/-- What may follow a printed expression: the end, a separator or `)`. -/
def Stop : List Char → Prop
  | [] => True
  | c :: _ => c = ' ' ∨ c = '\n' ∨ c = ')'

theorem lex_other {c : Char} {r : List Char} (h1 : c ≠ ';') (h2 : c ≠ '(') (h3 : c ≠ ')')
    (h4 : c ≠ '"') : lex (c :: r) =
      if isSpace c then lex r
      else if isIdChar c then
        (Tok.atom (String.ofList (c :: r.takeWhile isIdChar)) :: ·) <$> lex (r.dropWhile isIdChar)
      else none := by
  rw [lex.eq_def]
  split <;> simp_all

theorem lex_space_cons {c : Char} (r : List Char) (h : isSpace c = true) :
    lex (c :: r) = lex r := by
  have : c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' := by
    simp only [isSpace, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ((h | h) | h) | h <;> simp [h]
  rcases this with rfl | rfl | rfl | rfl <;> rw [lex_other] <;> simp [isSpace]

theorem lex_spaces (n : Nat) (r : List Char) : lex (spaces n ++ r) = lex r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [spaces, List.replicate_succ, List.cons_append]
    rw [lex_space_cons _ (by decide)]; exact ih

theorem lex_rp (r : List Char) : lex (')' :: r) = (Tok.rp :: ·) <$> lex r := by
  rw [lex.eq_def]; rfl

theorem lex_lp {r : List Char} (h : r.head? ≠ some ';') :
    lex ('(' :: r) = (Tok.lp :: ·) <$> lex r := by
  rw [lex.eq_def]
  split <;> simp_all <;> (obtain ⟨h1, h2⟩ := ‹_ ∧ _›; subst_vars; simp_all)

theorem idChar_ne {c : Char} (h : isIdChar c = true) :
    c ≠ ';' ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '"' ∧ isSpace c = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  any_goals (rintro rfl; revert h; decide)
  cases hs : isSpace c
  · rfl
  · simp only [isSpace, Bool.or_eq_true, decide_eq_true_eq] at hs
    rcases hs with ((rfl | rfl) | rfl) | rfl <;> revert h <;> decide

theorem stop_head {cs : List Char} (h : Stop cs) :
    ∀ c, cs.head? = some c → isIdChar c = false ∧ c ≠ ';' := by
  intro c hc
  cases cs with
  | nil => cases hc
  | cons d t =>
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst hc
    rcases h with rfl | rfl | rfl <;> decide

theorem lex_atom {a : String} {cs : List Char} (ha : AtomOk a) (hs : Stop cs) :
    lex (a.toList ++ cs) = (Tok.atom a :: ·) <$> lex cs := by
  obtain ⟨hne, hall⟩ := ha
  cases hl : a.toList with
  | nil => exact absurd hl hne
  | cons c r =>
    show lex (c :: r ++ cs) = (Tok.atom a :: ·) <$> lex cs
    have hc : isIdChar c = true := hall c (by simp [hl])
    have hr : ∀ x ∈ r, isIdChar x = true := fun x hx => hall x (by simp [hl, hx])
    obtain ⟨h1, h2, h3, h4, h5⟩ := idChar_ne hc
    have ht : (r ++ cs).takeWhile isIdChar = r := by
      rw [List.takeWhile_append_of_pos hr]
      cases cs with
      | nil => simp
      | cons d t => simp [(stop_head hs d rfl).1]
    have hd : (r ++ cs).dropWhile isIdChar = cs := by
      rw [List.dropWhile_append_of_pos hr]
      cases cs with
      | nil => simp
      | cons d t => simp [(stop_head hs d rfl).1]
    rw [List.cons_append, lex_other h1 h2 h3 h4]
    simp only [h5, hc, Bool.false_eq_true, ite_false, ite_true, ht, hd]
    rw [← hl, String.ofList_toList]

/-! ## String literals -/

theorem hexVal_hexDigit : ∀ n : Fin 16, hexVal? (hexDigit n) = some n := by decide

theorem hexDigit_ne : ∀ n : Fin 16,
    hexDigit n ≠ 't' ∧ hexDigit n ≠ 'n' ∧ hexDigit n ≠ 'r' ∧ hexDigit n ≠ '"' ∧
      hexDigit n ≠ '\'' ∧ hexDigit n ≠ '\\' := by decide

/-- The condition under which `escByte` prints a byte verbatim. -/
abbrev Plain (b : UInt8) : Prop := 0x20 ≤ b.toNat ∧ b.toNat < 0x7f ∧ b.toNat ≠ 0x22 ∧ b.toNat ≠ 0x5c

theorem lexStr_plain {b : UInt8} (h : Plain b) {bs : List UInt8} {x r : List Char}
    (ih : lexStr x = some (bs, r)) : lexStr (Char.ofNat b.toNat :: x) = some (b :: bs, r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : (Char.ofNat b.toNat).toNat = b.toNat := by
    simp [Char.ofNat, Char.ofNatAux, Char.toNat, show b.toNat.isValidChar from
      Or.inl (by omega)]
  have q : Char.ofNat b.toNat ≠ '"' := fun he => h3 (by rw [← hc, he]; rfl)
  have bs' : Char.ofNat b.toNat ≠ '\\' := fun he => h4 (by rw [← hc, he]; rfl)
  rw [lexStr.eq_def]
  split <;> simp_all [charBytes]
  all_goals first
    | omega
    | (rename_i heq; obtain ⟨h5, rfl⟩ := heq; simp_all)
    | (rename_i heq; obtain ⟨-, rfl⟩ := heq
       simp_all [show b.toNat < 128 by omega]; omega)

theorem lexStr_hex {b : UInt8} {bs : List UInt8} {x r : List Char}
    (ih : lexStr x = some (bs, r)) :
    lexStr ('\\' :: hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: x) =
      some (b :: bs, r) := by
  have hlt : b.toNat < 256 := b.toNat_lt
  have hlo := hexDigit_ne ⟨b.toNat / 16, by omega⟩
  have hv1 : hexVal? (hexDigit (b.toNat / 16)) = some (b.toNat / 16) :=
    hexVal_hexDigit ⟨b.toNat / 16, by omega⟩
  have hv2 : hexVal? (hexDigit (b.toNat % 16)) = some (b.toNat % 16) :=
    hexVal_hexDigit ⟨b.toNat % 16, by omega⟩
  have hb : (16 * (b.toNat / 16) + b.toNat % 16).toUInt8 = b := by
    rw [Nat.div_add_mod]; simp
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hlo
  rw [lexStr.eq_def]
  split <;> simp_all
  all_goals first
    | (rename_i heq; obtain ⟨rfl, rfl, rfl⟩ := heq; simp_all)

theorem lexStr_escByte (b : UInt8) (bs : List UInt8) (r : List Char)
    (ih : lexStr (bs.flatMap escByte ++ '"' :: r) = some (bs, r)) :
    lexStr (escByte b ++ (bs.flatMap escByte ++ '"' :: r)) = some (b :: bs, r) := by
  by_cases h : Plain b
  · have he : escByte b = [Char.ofNat b.toNat] := by simp [escByte, h]
    rw [he, List.singleton_append]
    exact lexStr_plain h ih
  · have he : escByte b = ['\\', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)] := by
      simp only [escByte]; split <;> first | exact absurd ‹_› h | rfl
    rw [he]
    exact lexStr_hex ih

theorem lexStr_quote (r : List Char) :
    ∀ bs : List UInt8, lexStr (bs.flatMap escByte ++ '"' :: r) = some (bs, r)
  | [] => by simp [lexStr]
  | b :: bs => by
    rw [List.flatMap_cons, List.append_assoc]
    exact lexStr_escByte b bs r (lexStr_quote r bs)

theorem lex_str (bs : List UInt8) (cs : List Char) :
    lex (quote bs ++ cs) = (lex cs).map (Tok.str bs :: ·) := by
  simp only [quote, List.cons_append, List.append_assoc]
  rw [lex.eq_def]
  simp only
  split
  · rename_i h; rw [lexStr_quote] at h; cases h
  · rename_i h; rw [lexStr_quote] at h; cases h; rfl

/-! ## Printed expressions -/

theorem stop_sep {sep r : List Char} (hsep : sep = [' '] ∨ ∃ k, sep = '\n' :: spaces k) :
    Stop (sep ++ r) := by
  rcases hsep with rfl | ⟨k, rfl⟩ <;> simp [Stop]

theorem lex_sep {sep r : List Char} (hsep : sep = [' '] ∨ ∃ k, sep = '\n' :: spaces k) :
    lex (sep ++ r) = lex r := by
  rcases hsep with rfl | ⟨k, rfl⟩
  · exact lex_space_cons r (by decide)
  · rw [List.cons_append, lex_space_cons _ (by decide), lex_spaces]

theorem pp_head (f : Bool) (i : Nat) (x : Sexp) (h : WF x) (r : List Char) :
    (pp f i x ++ r).head? ≠ some ';' := by
  cases x with
  | atom a =>
    obtain ⟨hne, hall⟩ := h
    simp only [pp]
    cases hl : a.toList with
    | nil => exact absurd hl hne
    | cons c t =>
      have := (idChar_ne (hall c (by simp [hl]))).1
      simpa using this
  | str b => simp [pp, quote]
  | list xs => simp only [pp]; split <;> simp

/-- Separators: a space, or a new line and indentation. -/
def SepOk (sep : Sexp → Sexp → List Char) : Prop :=
  ∀ x y, sep x y = [' '] ∨ ∃ k, sep x y = '\n' :: spaces k

theorem sepOk_space : SepOk fun _ _ => [' '] := fun _ _ => .inl rfl

theorem sepOk_break (ind : Nat) : SepOk (breakSep ind) := by
  intro x y
  unfold breakSep
  split
  · exact .inl rfl
  · exact .inr ⟨ind, rfl⟩

theorem ppL_head (f : Bool) (sep : Sexp → Sexp → List Char) (i : Nat) (xs : List Sexp) (h : WFL xs)
    (r : List Char) (hr : r.head? ≠ some ';') : (ppL f sep i xs ++ r).head? ≠ some ';' := by
  match xs, h with
  | [], _ => simpa [ppL] using hr
  | [x], h => simpa [ppL] using pp_head f i x h.1 r
  | x :: y :: xs, h =>
    simp only [ppL, List.append_assoc]
    exact pp_head f i x h.1 _

mutual
theorem lex_pp (f : Bool) (i : Nat) : ∀ (s : Sexp) (cs : List Char), WF s → Stop cs →
    lex (pp f i s ++ cs) = (lex cs).map (toks s ++ ·)
  | .atom a, cs, h, hs => by
    simp only [pp, toks]
    rw [lex_atom h hs]; rfl
  | .str b, cs, _, _ => by
    simp only [pp, toks]
    rw [lex_str]; rfl
  | .list xs, cs, h, _ => by
    have key : ∀ f' sep i', SepOk sep →
        lex ('(' :: (ppL f' sep i' xs ++ [')']) ++ cs) = (lex cs).map (toks (.list xs) ++ ·) := by
      intro f' sep i' hsep
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [lex_lp (ppL_head f' sep i' xs h _ (by simp)),
        lex_ppL f' sep i' hsep xs (')' :: cs) h (by simp [Stop]), lex_rp]
      cases lex cs <;> simp [toks]
    simp only [pp]
    split
    · exact key _ _ _ sepOk_space
    · exact key _ _ _ (sepOk_break _)

theorem lex_ppL (f : Bool) (sep : Sexp → Sexp → List Char) (i : Nat) (hsep : SepOk sep) :
    ∀ (xs : List Sexp) (cs : List Char), WFL xs → Stop cs →
      lex (ppL f sep i xs ++ cs) = (lex cs).map (toks.toksL xs ++ ·)
  | [], cs, _, _ => by simp [ppL, toks.toksL]
  | [x], cs, h, hs => by
    simp only [ppL, toks.toksL]
    rw [lex_pp f i x cs h.1 hs]
    cases lex cs <;> simp
  | x :: y :: xs, cs, h, hs => by
    simp only [ppL, List.append_assoc]
    rw [lex_pp f i x _ h.1 (stop_sep (hsep x y)), lex_sep (hsep x y),
      lex_ppL f sep i hsep (y :: xs) cs h.2 hs]
    cases lex cs <;> simp [toks.toksL]
end

/-! ## Trees -/

theorem parseSeq_toksL : ∀ (n : Nat) (xs : List Sexp) (rest : List Tok),
    (toks.toksL xs).length < n → (rest = [] ∨ rest.head? = some .rp) →
    parseSeq n (toks.toksL xs ++ rest) = some (xs, rest)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, [], rest, _, hr => by
    rcases hr with rfl | hr
    · rfl
    · cases rest with
      | nil => rfl
      | cons t r => simp at hr; subst hr; rfl
  | n + 1, .atom a :: xs, rest, h, hr => by
    simp only [toks.toksL, toks, List.cons_append, List.nil_append, List.length_cons] at h ⊢
    rw [parseSeq, parseSeq_toksL n xs rest (by simp at h; omega) hr]; rfl
  | n + 1, .str b :: xs, rest, h, hr => by
    simp only [toks.toksL, toks, List.cons_append, List.nil_append, List.length_cons] at h ⊢
    rw [parseSeq, parseSeq_toksL n xs rest (by simp at h; omega) hr]; rfl
  | n + 1, .list ys :: xs, rest, h, hr => by
    simp only [toks.toksL, toks, List.cons_append, List.length_cons, List.length_append,
      List.append_assoc, List.nil_append] at h ⊢
    rw [parseSeq, parseSeq_toksL n ys _ (by simp at h; omega) (.inr rfl)]
    simp only
    rw [parseSeq_toksL n xs rest (by simp at h; omega) hr]; rfl

theorem toksL_singleton (s : Sexp) : toks.toksL [s] = toks s := by simp [toks.toksL]

theorem parseTop_toksL (xs : List Sexp) : parseTop (toks.toksL xs) = some xs := by
  unfold parseTop
  have := parseSeq_toksL ((toks.toksL xs).length + 1) xs [] (by omega) (.inl rfl)
  rw [List.append_nil] at this
  rw [this]

/-! ## The round trips -/

/-- **Round trip.** A well-formed S-expression reads back from its printing. -/
theorem read_print (s : Sexp) (h : WF s) : read (print s) = some [s] := by
  unfold read print
  rw [String.toList_ofList, ← List.append_nil (pp false 0 s), lex_pp false 0 s [] h trivial]
  have : lex [] = some [] := by rw [lex.eq_def]
  rw [this]
  simp only [Option.map_some, List.append_nil, Option.bind_eq_bind, Option.bind_some]
  rw [← toksL_singleton, parseTop_toksL]

theorem lex_printAll : ∀ (ss : List Sexp), WFL ss →
    lex (ss.flatMap fun s => pp false 0 s ++ ['\n']) = some (toks.toksL ss)
  | [], _ => by rw [lex.eq_def]; rfl
  | s :: ss, h => by
    rw [List.flatMap_cons, List.append_assoc, lex_pp false 0 s _ h.1 (by simp [Stop]),
      List.singleton_append, lex_space_cons _ (by decide), lex_printAll ss h.2]
    rfl

/-- **Round trip** for documents of several S-expressions. -/
theorem read_printAll (ss : List Sexp) (h : WFL ss) : read (printAll ss) = some ss := by
  unfold read printAll
  rw [String.toList_ofList, lex_printAll ss h]
  exact parseTop_toksL ss

end Silmaril.Wasm.Component.Wat.Sexp
