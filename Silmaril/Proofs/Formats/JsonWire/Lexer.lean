module

public import Silmaril.Formats.JsonWire.Grammar.Defs

/-! # Proofs: the RFC 8259 lexer, one step at a time (`Silmaril.Formats.JsonWire.Grammar.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Lexer

open Silmaril.Formats.JsonWire Silmaril.Formats.JsonWire.Internal

@[simp] theorem rfc_bne_rfc : (Dialect.rfc8259 != Dialect.rfc8259) = false := rfl
@[simp] theorem rfc_beq_json5 : (Dialect.rfc8259 == Dialect.json5) = false := rfl

theorem bind_tokens (o : Option Lexed) (pre : List Token) (k : Lexed → List (Located TokenKind)) :
    (o.bind fun t => some (⟨pre ++ t.tokens, k t⟩ : Lexed)).map Lexed.tokens =
      o.map fun t => pre ++ t.tokens := by cases o <;> rfl

theorem bind_tokens' (o : Option Lexed) (k : Lexed → List (Located TokenKind)) :
    (o.bind fun t => some (⟨t.tokens, k t⟩ : Lexed)).map Lexed.tokens =
      o.map fun t => [] ++ t.tokens := by cases o <;> rfl

theorem lex_succ_cons (d : Dialect) (f off : Nat) (c : Char) (cs : List Char) :
    (lex d (f + 1) off (c :: cs)).map Lexed.tokens =
      match step d c cs with
      | none => none
      | some (t, _, rest) =>
        if (c :: cs).length - rest.length = 0 then none
        else (lex d f (off + width ((c :: cs).take ((c :: cs).length - rest.length))) rest).map
          fun l => t.toList ++ l.tokens := by
  rw [lex]
  rcases step d c cs with _ | ⟨t, k, rest⟩
  · rfl
  · simp only [Option.bind_eq_bind, Option.bind_some, beq_iff_eq, Option.pure_def]
    split_ifs
    · rfl
    · exact bind_tokens _ _ _

theorem map_pre (o : Option Lexed) (p : List Token) :
    o.map (fun l => p ++ l.tokens) = (o.map Lexed.tokens).map (p ++ ·) := by cases o <;> rfl

/-- Enough fuel is all the lexer needs: its tokens do not depend on the fuel or the offset. -/
theorem lex_tokens_eq : ∀ (n : Nat) (cs : List Char) (f off : Nat), cs.length ≤ n → cs.length < f →
    (lex .rfc8259 f off cs).map Lexed.tokens = tokensOf cs
  | n, [], f, off, _, _ => by
    cases f <;> simp [tokensOf, lex]
  | n, c :: cs, f + 1, off, hn, hf => by
    unfold tokensOf
    rw [List.length_cons, lex_succ_cons, lex_succ_cons]
    rcases step .rfc8259 c cs with _ | ⟨t, k, rest⟩
    · rfl
    simp only
    split_ifs with h
    · rfl
    · have hr : rest.length ≤ cs.length := by simp at h; omega
      cases n with
      | zero => simp at hn
      | succ n =>
        rw [map_pre, map_pre, lex_tokens_eq n rest f _ (by simp at hn; omega) (by simp at hf; omega),
          lex_tokens_eq n rest (cs.length + 1) _ (by simp at hn; omega) (by omega)]
  | n, c :: cs, 0, off, _, hf => by simp at hf

/-- **One lexer step** on `tokensOf`. -/
theorem tokensOf_cons (c : Char) (cs : List Char) :
    tokensOf (c :: cs) = match step .rfc8259 c cs with
      | none => none
      | some (t, _, rest) =>
        if rest.length < cs.length + 1 then (tokensOf rest).map (t.toList ++ ·) else none := by
  conv_lhs => unfold tokensOf
  rw [List.length_cons, lex_succ_cons]
  rcases step .rfc8259 c cs with _ | ⟨t, k, rest⟩
  · rfl
  simp only [List.length_cons]
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · rw [map_pre, lex_tokens_eq rest.length rest (cs.length + 1) _ le_rfl (by omega)]
  · omega

@[simp] theorem tokensOf_nil : tokensOf [] = some [] := rfl

theorem length_dropWhile_le (p : Char → Bool) : ∀ l : List Char, (l.dropWhile p).length ≤ l.length
  | [] => le_rfl
  | c :: l => by
    rw [List.dropWhile_cons]
    split
    · exact Nat.le_trans (length_dropWhile_le p l) (Nat.le_succ _)
    · exact le_rfl

theorem step_white {c : Char} (h : white .rfc8259 c = true) (cs : List Char) :
    step .rfc8259 c cs = some (none, .whitespace, (c :: cs).dropWhile (white .rfc8259)) := by
  simp [step, h]

theorem tokensOf_white_cons {c : Char} (h : white .rfc8259 c = true) (cs : List Char) :
    tokensOf (c :: cs) = tokensOf (cs.dropWhile (white .rfc8259)) := by
  rw [tokensOf_cons, step_white h]
  simp only [List.dropWhile_cons, h, ite_true, Option.toList_none, List.nil_append]
  have := length_dropWhile_le (white .rfc8259) cs
  split_ifs with h1
  · simp
  · omega

theorem tokensOf_dropWhite (cs : List Char) :
    tokensOf (cs.dropWhile (white .rfc8259)) = tokensOf cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    by_cases h : white .rfc8259 c = true
    · rw [tokensOf_white_cons h, List.dropWhile_cons]; simp [h]
    · rw [List.dropWhile_cons]; simp [h]

/-- Whitespace before the rest makes no tokens. -/
theorem tokensOf_white_append {ws : List Char} (hw : ∀ c ∈ ws, white .rfc8259 c = true)
    (r : List Char) : tokensOf (ws ++ r) = tokensOf r := by
  cases ws with
  | nil => rfl
  | cons c ws =>
    rw [List.cons_append, tokensOf_white_cons (hw c (by simp)),
      List.dropWhile_append_of_pos (fun x hx => hw x (by simp [hx])), tokensOf_dropWhite]

/-! ## Strings -/

theorem char_le_iff {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

theorem isDigit_iff {c : Char} : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  rw [Char.isDigit]
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le, ge_iff_le]; rfl

theorem hex?_isSome {c : Char} : (hex? c).isSome ↔ IsHexChar c := by
  unfold hex? IsHexChar
  have hd := @isDigit_iff c
  split_ifs with h1 h2 h3 <;> simp_all [char_le_iff]

theorem hexes?_four {cs rest : List Char} {n : Nat} (h : hexes? 4 cs = some (n, rest)) :
    ∃ a b c d, cs = a :: b :: c :: d :: rest ∧ IsHexChar a ∧ IsHexChar b ∧ IsHexChar c ∧
      IsHexChar d := by
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, cs⟩⟩⟩⟩ <;> simp only [hexes?, reduceCtorEq] at h
  · cases hx : hex? a <;> simp [hx] at h
  · cases hx : hex? a <;> cases hy : hex? b <;> simp [hx, hy] at h
  · cases hx : hex? a <;> cases hy : hex? b <;> cases hz : hex? c <;> simp [hx, hy, hz] at h
  cases hx : hex? a <;> cases hy : hex? b <;> cases hz : hex? c <;> cases hw : hex? d <;>
    simp [hx, hy, hz, hw] at h
  refine ⟨a, b, c, d, by rw [h.2], hex?_isSome.mp (by simp [hx]), hex?_isSome.mp (by simp [hy]),
    hex?_isSome.mp (by simp [hz]), hex?_isSome.mp (by simp [hw])⟩

theorem hexes?_four_of {a b c d : Char} (rest : List Char) (ha : IsHexChar a) (hb : IsHexChar b)
    (hc : IsHexChar c) (hd : IsHexChar d) : ∃ n, hexes? 4 (a :: b :: c :: d :: rest) = some (n, rest) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hex?_isSome.mpr ha)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hex?_isSome.mpr hb)
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hex?_isSome.mpr hc)
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hex?_isSome.mpr hd)
  exact ⟨x * 4096 + (y * 256 + (z * 16 + w)), by simp [hexes?, hx, hy, hz, hw]⟩

@[simp] theorem rfc_bne_json5 : (Dialect.rfc8259 != Dialect.json5) = true := rfl

def shortEscapes : List Char := ['"', '\\', '/', 'b', 'f', 'n', 'r', 't']

theorem escape?_inv {cs rest : List Char} {u : Units} (h : escape? .rfc8259 cs = some (u, rest)) :
    (∃ e, cs = e :: rest ∧ e ∈ shortEscapes) ∨
    (∃ a b c d, cs = 'u' :: a :: b :: c :: d :: rest ∧ IsHexChar a ∧ IsHexChar b ∧ IsHexChar c ∧
      IsHexChar d) := by
  unfold escape? at h
  split at h
  · right
    rename_i r
    cases hn : hexes? 4 r with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r'⟩ := p
      simp [hn] at h
      obtain ⟨a, b, c, d, rfl, ha, hb, hc, hd⟩ := hexes?_four hn
      exact ⟨a, b, c, d, by rw [← h.2], ha, hb, hc, hd⟩
  · simp at h
  · simp only [rfc_beq_json5, Bool.false_and, Bool.false_eq_true, ite_false] at h
    left
    split at h <;> simp at h <;> exact ⟨_, by rw [h.2], by simp [shortEscapes]⟩
  · simp at h

theorem escape?_short {e : Char} (he : e ∈ shortEscapes) (rest : List Char) :
    ∃ u, escape? .rfc8259 (e :: rest) = some (u, rest) := by
  simp only [shortEscapes, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem escape?_unit {a b c d : Char} (rest : List Char) (ha : IsHexChar a) (hb : IsHexChar b)
    (hc : IsHexChar c) (hd : IsHexChar d) :
    ∃ u, escape? .rfc8259 ('u' :: a :: b :: c :: d :: rest) = some (u, rest) := by
  obtain ⟨n, hn⟩ := hexes?_four_of rest ha hb hc hd
  exact ⟨[UInt16.ofNat n], by simp [escape?, hn]⟩

theorem quoted?_complete {b : List Char} (hb : StrBody b) :
    ∀ (fuel : Nat), b.length < fuel → ∀ rest : List Char,
      ∃ u, quoted? .rfc8259 '"' fuel (b ++ '"' :: rest) = some (u, rest) := by
  induction hb with
  | nil =>
    intro fuel hf rest
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    exact ⟨[], by simp [quoted?]⟩
  | @plain c _ hc hq hbs _ ih =>
    intro fuel hf rest
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨u, hu⟩ := ih f (by simp at hf; omega) rest
    refine ⟨charUnits c ++ u, ?_⟩
    simp only [List.cons_append, quoted?]
    simp [hq, hbs, hu, show ¬ (c.toNat < 32) by omega]
  | @escape e bb he _ ih =>
    intro fuel hf rest
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨u, hu⟩ := ih f (by simp at hf; omega) rest
    obtain ⟨h, hh⟩ := escape?_short (rest := bb ++ '"' :: rest) (by simpa [shortEscapes] using he)
    refine ⟨h ++ u, ?_⟩
    simp only [List.cons_append, quoted?]
    simp [hh, hu]
  | @unit a b' c d bb ha hb hc hd _ ih =>
    intro fuel hf rest
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨u, hu⟩ := ih f (by simp at hf; omega) rest
    obtain ⟨h, hh⟩ := escape?_unit (bb ++ '"' :: rest) ha hb hc hd
    refine ⟨h ++ u, ?_⟩
    simp only [List.cons_append, quoted?]
    simp [hh, hu]

theorem quoted?_sound : ∀ (fuel : Nat) (cs rest : List Char) (u : Units),
    quoted? .rfc8259 '"' fuel cs = some (u, rest) → ∃ b, cs = b ++ '"' :: rest ∧ StrBody b
  | 0, _, _, _, h => by simp [quoted?] at h
  | _ + 1, [], _, _, h => by simp [quoted?] at h
  | f + 1, c :: cs, rest, u, h => by
    simp only [quoted?] at h
    by_cases hq : c = '"'
    · subst hq; simp at h; exact ⟨[], by simp [h.2], .nil⟩
    simp only [hq, beq_iff_eq, ite_false] at h
    by_cases hb : c = '\\'
    · subst hb
      simp only [ite_true, Option.bind_eq_bind] at h
      cases he : escape? .rfc8259 cs with
      | none => simp [he] at h
      | some p =>
        obtain ⟨hu, r⟩ := p
        simp only [he, Option.bind_some] at h
        cases hr : quoted? .rfc8259 '"' f r with
        | none => simp [hr] at h
        | some p =>
          obtain ⟨tu, r'⟩ := p
          have hrest : r' = rest := by simp [hr] at h; exact h.2
          subst hrest
          obtain ⟨b, rfl, hbody⟩ := quoted?_sound f r r' tu hr
          rcases escape?_inv he with ⟨e, rfl, he'⟩ | ⟨a, b₁, c₁, d, rfl, ha, hb₁, hc, hd⟩
          · exact ⟨'\\' :: e :: b, by simp, .escape (by simpa [shortEscapes] using he') hbody⟩
          · exact ⟨'\\' :: 'u' :: a :: b₁ :: c₁ :: d :: b, by simp, .unit ha hb₁ hc hd hbody⟩
    · simp only [hb, ite_false, rfc_bne_json5, Bool.true_and] at h
      split_ifs at h with hlt
      cases hr : quoted? .rfc8259 '"' f cs with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨tu, r'⟩ := p
        have hrest : r' = rest := by simp [hr] at h; exact h.2
        subst hrest
        obtain ⟨b, rfl, hbody⟩ := quoted?_sound f cs r' tu hr
        exact ⟨c :: b, by simp, .plain (by simp at hlt; omega) hq hb hbody⟩

/-! ## Numbers -/

theorem isDigit_iff' {c : Char} : c.isDigit = true ↔ IsDigitChar c := isDigit_iff

/-- Taking while `p` from `a ++ b`, where all of `a` and not the head of `b` satisfy `p`. -/
theorem takeWhile_append_stop {p : Char → Bool} {a b : List Char} (ha : ∀ x ∈ a, p x = true)
    (hb : ∀ y ∈ b.head?, p y = false) : (a ++ b).takeWhile p = a ∧ (a ++ b).dropWhile p = b := by
  induction a with
  | nil =>
    cases b with
    | nil => simp
    | cons y b => simp [hb y rfl]
  | cons x a ih =>
    have := ih (fun z hz => ha z (by simp [hz]))
    simp [ha x (by simp), this]

theorem span_loop (p : Char → Bool) : ∀ (l acc : List Char),
    List.span.loop p l acc = (acc.reverse ++ l.takeWhile p, l.dropWhile p)
  | [], acc => by simp [List.span.loop]
  | x :: l, acc => by
    unfold List.span.loop
    cases h : p x <;> simp [h, span_loop p l]

theorem span_eq (p : Char → Bool) (l : List Char) :
    l.span p = (l.takeWhile p, l.dropWhile p) := by
  simp [List.span, span_loop]

theorem span_append_stop {p : Char → Bool} {a b : List Char} (ha : ∀ x ∈ a, p x = true)
    (hb : ∀ y ∈ b.head?, p y = false) : (a ++ b).span p = (a, b) := by
  rw [span_eq, (takeWhile_append_stop ha hb).1,
    (takeWhile_append_stop ha hb).2]

/-- The exponent part `exponent?` accepts: nothing, or `e`/`E`, an optional sign and digits. -/
def ExpChars (e : List Char) : Prop :=
  e = [] ∨ ∃ x sg ds, e = x :: (sg ++ ds) ∧ (x = 'e' ∨ x = 'E') ∧
    (sg = [] ∨ sg = ['-'] ∨ sg = ['+']) ∧ Digits ds

theorem all_isDigit_iff {ds : List Char} : ds.all Char.isDigit = true ↔ ∀ x ∈ ds, IsDigitChar x := by
  simp [List.all_eq_true, isDigit_iff']

theorem splitSign_of {cs : List Char} (h : ∀ y ∈ cs.head?, y ≠ '-' ∧ y ≠ '+') :
    splitSign cs = (false, cs) := by
  unfold splitSign; split <;> simp_all

theorem splitFraction_of {cs : List Char} (h : ∀ y ∈ cs.head?, y ≠ '.') :
    splitFraction cs = ([], cs, false) := by
  unfold splitFraction; split <;> simp_all

theorem digits_test_iff (ds : List Char) :
    (ds.isEmpty || !(ds.all Char.isDigit)) = false ↔ Digits ds := by
  simp [Digits, isDigit_iff']

theorem exponent?_isSome {r : List Char} : (exponent? r).isSome ↔ ExpChars r := by
  unfold ExpChars
  rcases r with _ | ⟨x, rest⟩
  · simp [exponent?]
  simp only [exponent?, reduceCtorEq, false_or]
  by_cases hx : (x == 'e' || x == 'E') = true
  · have hx' : x = 'e' ∨ x = 'E' := by simpa using hx
    have dig : ∀ (ds : List Char) (v : Int), (if (ds.isEmpty || !(ds.all Char.isDigit)) = true then none
        else some v).isSome = true ↔ Digits ds := by
      intro ds v
      rw [← digits_test_iff]
      cases (ds.isEmpty || !(ds.all Char.isDigit)) <;> simp
    have e : ∀ (sg ds : List Char), splitSign (sg ++ ds) = (decide (sg = ['-']), ds) →
        ((exponent? (x :: (sg ++ ds))).isSome ↔ Digits ds) := by
      intro sg ds h
      simp only [exponent?, hx, ite_true, h]
      exact dig _ _
    constructor
    · intro h
      refine ⟨x, ?_⟩
      rcases rest with _ | ⟨y, ds⟩
      · simp [hx, splitSign] at h
      by_cases hy : y = '-'
      · subst hy
        exact ⟨['-'], ds, rfl, hx', Or.inr (Or.inl rfl), (e ['-'] ds rfl).mp (by simpa [exponent?] using h)⟩
      by_cases hy' : y = '+'
      · subst hy'
        exact ⟨['+'], ds, rfl, hx', Or.inr (Or.inr rfl), (e ['+'] ds rfl).mp (by simpa [exponent?] using h)⟩
      · exact ⟨[], y :: ds, rfl, hx', Or.inl rfl,
          (e [] (y :: ds) (by rw [List.nil_append, splitSign_of (by simp [hy, hy'])]; simp)).mp
            (by simpa [exponent?] using h)⟩
    · rintro ⟨x', sg, ds, he, -, hsg, hd⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := e sg ds (by
        rcases hsg with rfl | rfl | rfl
        · obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := List.exists_cons_of_ne_nil hd.1
          have hdd := hd.2 d (by simp)
          rw [List.nil_append, splitSign_of]
          · simp
          · simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
            constructor <;> rintro rfl <;> simp [IsDigitChar] at hdd
        · rfl
        · rfl)
      simpa [exponent?] using this.mpr hd
  · simp only [Bool.not_eq_true] at hx
    simp only [hx, Bool.false_eq_true, ite_false, Option.isSome_none, false_iff, not_exists, not_and]
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
    intro _ _ _ _ h; rcases h with rfl | rfl <;> simp_all

theorem takeWhile_all (p : Char → Bool) : ∀ (l : List Char), ∀ x ∈ l.takeWhile p, p x = true
  | [] => by simp
  | y :: l => by
    intro x hx
    rw [List.takeWhile_cons] at hx
    split at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · assumption
      · exact takeWhile_all p l x hx
    · simp at hx

theorem dropWhile_head (p : Char → Bool) : ∀ (l : List Char), ∀ y ∈ (l.dropWhile p).head?, p y = false
  | [] => by simp
  | x :: l => by
    intro y hy
    rw [List.dropWhile_cons] at hy
    split at hy
    · exact dropWhile_head p l y hy
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy; simpa using ‹¬p x = true›

theorem splitSign_spec {text cs : List Char} {neg : Bool} (h : splitSign text = (neg, cs)) :
    (text = '-' :: cs ∧ neg = true) ∨ text = '+' :: cs ∨
    (text = cs ∧ neg = false ∧ ∀ y ∈ text.head?, y ≠ '-' ∧ y ≠ '+') := by
  rcases text with _ | ⟨y, ys⟩
  · simp only [splitSign, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  by_cases h1 : y = '-'
  · subst h1; simp only [splitSign, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  by_cases h2 : y = '+'
  · subst h2; simp only [splitSign, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  rw [splitSign_of (by simp [h1, h2])] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact Or.inr (Or.inr ⟨rfl, rfl, by simp [h1, h2]⟩)

theorem splitFraction_spec {r f r2 : List Char} {dot : Bool} (h : splitFraction r = (f, r2, dot)) :
    (dot = true ∧ r = '.' :: (f ++ r2) ∧ (∀ x ∈ f, IsDigitChar x) ∧ ∀ y ∈ r2.head?, ¬ IsDigitChar y) ∨
    (dot = false ∧ f = [] ∧ r2 = r ∧ ∀ y ∈ r.head?, y ≠ '.') := by
  rcases r with _ | ⟨y, ys⟩
  · simp only [splitFraction, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  by_cases h1 : y = '.'
  · subst h1
    simp only [splitFraction, span_eq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine Or.inl ⟨rfl, by rw [List.takeWhile_append_dropWhile], fun x hx => ?_, fun y hy => ?_⟩
    · exact isDigit_iff'.mp (takeWhile_all _ ys x hx)
    · rw [← isDigit_iff']; simpa using dropWhile_head _ ys y hy
  rw [splitFraction_of (by simp [h1])] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact Or.inr ⟨rfl, rfl, rfl, by simp [h1]⟩

theorem decimal?_sound {text : List Char} {n : Number} (h : decimal? .rfc8259 text = some n) :
    NumberChars text ∧ ∃ d, n = .finite d := by
  unfold decimal? at h
  generalize hs : splitSign text = sc at h
  obtain ⟨neg, cs⟩ := sc
  simp only [rfc_bne_json5, rfc_beq_json5, Bool.true_and, Bool.false_and, Bool.false_eq_true,
    ite_false, Option.bind_eq_bind] at h
  rw [span_eq] at h
  generalize hw : cs.takeWhile Char.isDigit = whole at h
  generalize hr : cs.dropWhile Char.isDigit = rest at h
  generalize hf : splitFraction rest = fr at h
  obtain ⟨fraction, rest2, dot⟩ := fr
  simp only at h
  split_ifs at h with hp h0 h1 h2
  cases he : exponent? rest2 with
  | none => simp [he] at h
  | some ex =>
    simp only [he, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨?_, _, rfl⟩
    have hcs : cs = whole ++ rest := by rw [← hw, ← hr, List.takeWhile_append_dropWhile]
    have hwd : ∀ x ∈ whole, IsDigitChar x := fun x hx => isDigit_iff'.mp (takeWhile_all _ cs x (hw ▸ hx))
    have hrd : ∀ y ∈ rest.head?, ¬ IsDigitChar y := fun y hy => by
      rw [← isDigit_iff']; simpa using dropWhile_head _ cs y (hr ▸ hy)
    have hwne : whole ≠ [] := by simp at h2; exact h2.1
    have hint : whole = ['0'] ∨ ∃ d ds, whole = d :: ds ∧ 49 ≤ d.toNat ∧ d.toNat ≤ 57 ∧
        ∀ x ∈ ds, IsDigitChar x := by
      obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hwne
      have hd := hwd d (by simp)
      by_cases hd0 : d = '0'
      · subst hd0
        left
        cases ds with
        | nil => rfl
        | cons _ _ => simp at h0
      · right
        refine ⟨d, ds, rfl, ?_, hd.2, fun x hx => hwd x (by simp [hx])⟩
        have : d.toNat ≠ 48 := fun h' => hd0 (Char.ext (by
          simp only [Char.toNat] at h'; exact UInt32.toNat_inj.mp (by simpa using h')))
        unfold IsDigitChar at hd; omega
    have hexp : ExpChars rest2 := exponent?_isSome.mp (by simp [he])
    obtain ⟨sgn, hsgn, hcs'⟩ : ∃ sgn, (sgn = [] ∨ sgn = ['-']) ∧ text = sgn ++ cs := by
      rcases splitSign_spec hs with ⟨rfl, -⟩ | rfl | ⟨rfl, -, -⟩
      · exact ⟨['-'], Or.inr rfl, rfl⟩
      · simp at hp
      · exact ⟨[], Or.inl rfl, rfl⟩
    rcases splitFraction_spec hf with ⟨rfl, rfl, hfd, hr2⟩ | ⟨rfl, rfl, rfl, -⟩
    · refine ⟨sgn, whole, '.' :: fraction, rest2, by simp [hcs', hcs], hsgn, hint,
        Or.inr ⟨fraction, rfl, ⟨by simp at h2; exact h2.2, hfd⟩⟩, hexp⟩
    · exact ⟨sgn, whole, [], rest2, by simp [hcs', hcs], hsgn, hint, Or.inl rfl, hexp⟩

theorem not_isDigit_of_eq {c : Char} (h : c = '.' ∨ c = 'e' ∨ c = 'E') : ¬ IsDigitChar c := by
  rcases h with rfl | rfl | rfl <;> simp [IsDigitChar]

theorem decimal?_complete {text : List Char} (h : NumberChars text) :
    ∃ d, decimal? .rfc8259 text = some (.finite d) := by
  obtain ⟨s, i, f, e, rfl, hs, hi, hf, he⟩ := h
  -- the integer part: digits, the first `1`-`9` unless it is a lone `0`
  obtain ⟨d, ds, rfl, hd, hds, hd0⟩ : ∃ d ds, i = d :: ds ∧ IsDigitChar d ∧ (∀ x ∈ ds, IsDigitChar x) ∧
      (ds ≠ [] → d ≠ '0') := by
    rcases hi with rfl | ⟨d, ds, rfl, h1, h2, h3⟩
    · exact ⟨'0', [], rfl, by simp [IsDigitChar], by simp, by simp⟩
    · refine ⟨d, ds, rfl, ⟨by omega, h2⟩, h3, fun _ hd => ?_⟩
      subst hd; simp at h1
  have he' : ExpChars e := he
  have ehead : ∀ y ∈ e.head?, ¬ IsDigitChar y ∧ y ≠ '.' := by
    rcases he with rfl | ⟨x, sg, ds', rfl, hx, -, -⟩
    · simp
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      exact ⟨not_isDigit_of_eq (Or.inr hx), by rcases hx with rfl | rfl <;> simp⟩
  have fehead : ∀ y ∈ (f ++ e).head?, ¬ IsDigitChar y := by
    rcases hf with rfl | ⟨ds', rfl, -⟩
    · simpa using fun y hy => (ehead y hy).1
    · simp [not_isDigit_of_eq]
  have hsign : splitSign (s ++ (d :: ds) ++ f ++ e) = (decide (s = ['-']), d :: (ds ++ f ++ e)) := by
    rcases hs with rfl | rfl
    · rw [splitSign_of]
      · simp
      · simp only [List.nil_append, List.cons_append, List.head?_cons, Option.mem_def,
          Option.some.injEq, forall_eq']
        constructor <;> rintro rfl <;> simp [IsDigitChar] at hd
    · rfl
  have hspan : (d :: (ds ++ f ++ e)).span Char.isDigit = (d :: ds, f ++ e) := by
    have := span_append_stop (p := Char.isDigit) (a := d :: ds) (b := f ++ e)
      (fun x hx => isDigit_iff'.mpr (by simp at hx; rcases hx with rfl | hx; exacts [hd, hds x hx]))
      (fun y hy => by rw [Bool.eq_false_iff, ne_eq, isDigit_iff']; exact fehead y hy)
    simpa using this
  have hfrac : ∃ fr, splitFraction (f ++ e) = (fr, e, decide (f ≠ [])) ∧ (f = [] → fr = []) ∧
      (f ≠ [] → f = '.' :: fr ∧ Digits fr) := by
    rcases hf with rfl | ⟨ds', rfl, hds'⟩
    · exact ⟨[], splitFraction_of (fun y hy => (ehead y (by simpa using hy)).2), fun _ => rfl,
        fun h => absurd rfl h⟩
    · refine ⟨ds', ?_, by simp, fun _ => ⟨rfl, hds'⟩⟩
      have := span_append_stop (p := Char.isDigit) (a := ds') (b := e)
        (fun x hx => isDigit_iff'.mpr (hds'.2 x hx))
        (fun y hy => by rw [Bool.eq_false_iff, ne_eq, isDigit_iff']; exact (ehead y hy).1)
      simp [splitFraction, this]
  obtain ⟨fr, hfr, hf0, hf1⟩ := hfrac
  obtain ⟨ex, hex⟩ := Option.isSome_iff_exists.mp (exponent?_isSome.mpr he')
  unfold decimal?
  rw [hsign]
  simp only [rfc_bne_json5, rfc_beq_json5, Bool.true_and, Bool.false_and, Bool.false_eq_true,
    ite_false, Option.bind_eq_bind, hspan, hfr, hex]
  have c1 : ((s ++ d :: ds ++ f ++ e).head? == some '+') = false := by
    rcases hs with rfl | rfl
    · simp only [List.nil_append, List.cons_append, List.head?_cons, beq_eq_false_iff_ne, ne_eq,
        Option.some.injEq]
      rintro rfl; simp [IsDigitChar] at hd
    · rfl
  have c2 : (decide ((d :: ds).length > 1) && (d :: ds).head? == some '0') = false := by
    cases ds with
    | nil => simp
    | cons x xs => simp [hd0 (by simp)]
  have c4 : (false || decide (f ≠ []) && fr.isEmpty) = false := by
    by_cases hf' : f = []
    · simp [hf']
    · simp [hf', (hf1 hf').2.1]
  simp only [c1, c2, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons, Bool.false_and,
    Option.bind_some, Option.pure_def]
  simp only [c4, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

/-! ## Tokens, one lexeme at a time -/

/-- The characters the RFC 8259 lexer ends a number or literal at. -/
theorem delimiter_rfc (c : Char) : delimiter .rfc8259 c = true ↔
    c = ' ' ∨ c = '\t' ∨ c = '\r' ∨ c = '\n' ∨ c = ',' ∨ c = ']' ∨ c = '}' ∨ c = ':' ∨ c = '[' ∨ c = '{' := by
  simp [delimiter, white]
  tauto

theorem white_rfc (c : Char) : white .rfc8259 c = true ↔ c = ' ' ∨ c = '\t' ∨ c = '\r' ∨ c = '\n' := by
  simp [white, or_assoc]

/-- Not one of the six punctuation characters. -/
def NotPunct (c : Char) : Prop := c ≠ '[' ∧ c ≠ ']' ∧ c ≠ '{' ∧ c ≠ '}' ∧ c ≠ ',' ∧ c ≠ ':'

theorem step_other {c : Char} (cs : List Char) (hw : white .rfc8259 c = false) (hq : c ≠ '"')
    (hp : NotPunct c) :
    step .rfc8259 c cs =
      if c.isDigit || c == '-' || c == '+' || c == '.' then
        (decimal? .rfc8259 ((c :: cs).span (fun c => !delimiter .rfc8259 c)).1).map
          fun n => (some (.number n), .number, ((c :: cs).span (fun c => !delimiter .rfc8259 c)).2)
      else
        let (word, rest) := (c :: cs).span (fun c => !delimiter .rfc8259 c)
        if word == "true".toList then some (some (.bool true), .literal, rest)
        else if word == "false".toList then some (some (.bool false), .literal, rest)
        else if word == "null".toList then some (some .null, .literal, rest)
        else none := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  unfold step
  simp only [hw, rfc_bne_rfc, rfc_beq_json5, Bool.false_and, Bool.false_eq_true, ite_false,
    Bool.or_false, beq_iff_eq, hq]
  split
  all_goals first | rfl | (cases decimal? .rfc8259 _ <;> rfl)

theorem quoted?_rest {fuel : Nat} {cs rest : List Char} {u : Units}
    (h : quoted? .rfc8259 '"' fuel cs = some (u, rest)) : rest.length < cs.length + 1 := by
  obtain ⟨b, rfl, -⟩ := quoted?_sound fuel cs rest u h
  simp; omega

/-- **One step, inverted**: a step reads whitespace or one lexeme. -/
theorem step_inv {c : Char} {cs rest : List Char} {t : Option Token} {k : TokenKind}
    (h : step .rfc8259 c cs = some (t, k, rest)) :
    (t = none ∧ white .rfc8259 c = true ∧ rest = cs.dropWhile (white .rfc8259)) ∨
    (∃ tok l, t = some tok ∧ c :: cs = l ++ rest ∧ Lexeme l tok) := by
  by_cases hw : white .rfc8259 c = true
  · rw [step_white hw] at h
    simp only [Option.some.injEq, Prod.mk.injEq, List.dropWhile_cons, hw, ite_true] at h
    exact Or.inl ⟨h.1.symm, hw, h.2.2.symm⟩
  have hw' : white .rfc8259 c = false := by simpa using hw
  by_cases hq : c = '"'
  · subst hq
    simp only [step, hw', rfc_bne_rfc, Bool.false_and, Bool.false_eq_true, ite_false, beq_self_eq_true,
      Bool.true_or, ite_true, Option.bind_eq_bind] at h
    obtain ⟨⟨u, r⟩, hqs, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    obtain ⟨b, rfl, hb⟩ := quoted?_sound _ _ _ _ hqs
    exact Or.inr ⟨_, _, rfl, by simp, .string hb⟩
  by_cases hp : NotPunct c
  · rw [step_other cs hw' hq hp] at h
    rw [span_eq] at h
    have hsplit : c :: cs = (c :: cs).takeWhile (fun c => !delimiter .rfc8259 c) ++
        (c :: cs).dropWhile (fun c => !delimiter .rfc8259 c) := (List.takeWhile_append_dropWhile).symm
    split_ifs at h with hn
    · cases hd : decimal? .rfc8259 ((c :: cs).takeWhile (fun c => !delimiter .rfc8259 c)) with
      | none => simp [hd] at h
      | some n =>
        simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        obtain ⟨hnum, d, rfl⟩ := decimal?_sound hd
        exact Or.inr ⟨_, _, rfl, hsplit, .number hnum⟩
    · simp only at h
      split_ifs at h with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
        obtain ⟨rfl, -, rfl⟩ := h
      · simp only [beq_iff_eq] at h1; rw [h1] at hsplit; exact Or.inr ⟨_, _, rfl, hsplit, .true_⟩
      · simp only [beq_iff_eq] at h2; rw [h2] at hsplit; exact Or.inr ⟨_, _, rfl, hsplit, .false_⟩
      · simp only [beq_iff_eq] at h3; rw [h3] at hsplit; exact Or.inr ⟨_, _, rfl, hsplit, .null⟩
  · simp only [NotPunct, not_and_or, not_not] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [step] at h <;> obtain ⟨rfl, -, rfl⟩ := h
    · exact Or.inr ⟨_, ['['], rfl, rfl, .arrayOpen⟩
    · exact Or.inr ⟨_, [']'], rfl, rfl, .arrayClose⟩
    · exact Or.inr ⟨_, ['{'], rfl, rfl, .objectOpen⟩
    · exact Or.inr ⟨_, ['}'], rfl, rfl, .objectClose⟩
    · exact Or.inr ⟨_, [','], rfl, rfl, .comma⟩
    · exact Or.inr ⟨_, [':'], rfl, rfl, .colon⟩

theorem lexes_white_append {ws cs : List Char} {ts : List Token}
    (hw : ∀ c ∈ ws, white .rfc8259 c = true) (h : Lexes cs ts) : Lexes (ws ++ cs) ts := by
  induction ws with
  | nil => exact h
  | cons c ws ih => exact .white (hw c (by simp)) (ih fun x hx => hw x (by simp [hx]))

theorem white_takeWhile (cs : List Char) : ∀ c ∈ cs.takeWhile (white .rfc8259), white .rfc8259 c = true :=
  takeWhile_all _ cs

/-- **The lexer is sound**: what it reads is whitespace and lexemes. -/
theorem lexes_of_tokensOf : ∀ (n : Nat) (cs : List Char) (ts : List Token), cs.length ≤ n →
    tokensOf cs = some ts → Lexes cs ts
  | _, [], ts, _, h => by simp at h; subst h; exact .nil
  | 0, _ :: _, _, hn, _ => by simp at hn
  | n + 1, c :: cs, ts, hn, h => by
    rw [tokensOf_cons] at h
    cases hs : step .rfc8259 c cs with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨t, k, rest⟩ := r
      simp only [hs] at h
      split_ifs at h with hl
      obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := lexes_of_tokensOf n rest ts' (by simp at hn; omega) hts'
      rcases step_inv hs with ⟨rfl, hw, rfl⟩ | ⟨tok, l, rfl, he, hl'⟩
      · simp only [Option.toList_none, List.nil_append]
        rw [show c :: cs = [c] ++ (cs.takeWhile (white .rfc8259) ++ cs.dropWhile (white .rfc8259)) by
          simp [List.takeWhile_append_dropWhile]]
        exact .white hw (lexes_white_append (ws := cs.takeWhile (white .rfc8259)) (white_takeWhile cs) ih)
      · rw [he]; exact .token hl' ih

/-- What may follow a number or a literal: nothing, or a delimiter. -/
def Follow (rest : List Char) : Prop := ∀ c ∈ rest.head?, delimiter .rfc8259 c = true

theorem tokensOf_step {c : Char} {cs rest : List Char} {t : Option Token} {k : TokenKind}
    (h : step .rfc8259 c cs = some (t, k, rest)) (hl : rest.length < cs.length + 1) :
    tokensOf (c :: cs) = (tokensOf rest).map (t.toList ++ ·) := by
  rw [tokensOf_cons, h]
  simp only [hl, ite_true]

theorem tokensOf_punct {c : Char} {tok : Token} (h : c = '[' ∧ tok = .arrayOpen ∨
    c = ']' ∧ tok = .arrayClose ∨ c = '{' ∧ tok = .objectOpen ∨ c = '}' ∧ tok = .objectClose ∨
    c = ',' ∧ tok = .comma ∨ c = ':' ∧ tok = .colon) (X : List Char) :
    tokensOf (c :: X) = (tokensOf X).map (tok :: ·) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact tokensOf_step (c := '[') (t := some .arrayOpen) (k := .arrayOpen) (rest := X) (by simp [step, white]) (by simp)
  · exact tokensOf_step (c := ']') (t := some .arrayClose) (k := .arrayClose) (rest := X) (by simp [step, white]) (by simp)
  · exact tokensOf_step (c := '{') (t := some .objectOpen) (k := .objectOpen) (rest := X) (by simp [step, white]) (by simp)
  · exact tokensOf_step (c := '}') (t := some .objectClose) (k := .objectClose) (rest := X) (by simp [step, white]) (by simp)
  · exact tokensOf_step (c := ',') (t := some .comma) (k := .comma) (rest := X) (by simp [step, white]) (by simp)
  · exact tokensOf_step (c := ':') (t := some .colon) (k := .colon) (rest := X) (by simp [step, white]) (by simp)

theorem tokensOf_string {b : List Char} (hb : StrBody b) (X : List Char) :
    ∃ u, tokensOf (('"' :: (b ++ ['"'])) ++ X) = (tokensOf X).map (.string u :: ·) := by
  obtain ⟨u, hu⟩ := quoted?_complete hb (b.length + (X.length + 1) + 1 + 1) (by omega) X
  refine ⟨u, ?_⟩
  have hs : step .rfc8259 '"' (b ++ '"' :: X) = some (some (.string u), .string, X) := by
    simp [step, white, hu]
  simpa using tokensOf_step hs (by simp; omega)

theorem toNat_ne {c : Char} {d : Char} (h : c.toNat ≠ d.toNat) : c ≠ d := fun e => h (e ▸ rfl)

theorem delimiter_toNat {c : Char} (h : delimiter .rfc8259 c = true) :
    c.toNat = 32 ∨ c.toNat = 9 ∨ c.toNat = 13 ∨ c.toNat = 10 ∨ c.toNat = 44 ∨ c.toNat = 93 ∨
      c.toNat = 125 ∨ c.toNat = 58 ∨ c.toNat = 91 ∨ c.toNat = 123 := by
  rw [delimiter_rfc] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The characters of a number: digits, signs, the decimal point and the exponent marks. -/
theorem numberChars_mem {w : List Char} (h : NumberChars w) :
    ∀ x ∈ w, IsDigitChar x ∨ x = '-' ∨ x = '+' ∨ x = '.' ∨ x = 'e' ∨ x = 'E' := by
  obtain ⟨s, i, f, e, rfl, hs, hi, hf, he⟩ := h
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · rcases hs with rfl | rfl <;> simp_all
  · rcases hi with rfl | ⟨d, ds, rfl, h1, h2, h3⟩
    · simp at hx; subst hx; left; simp [IsDigitChar]
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · left; exact ⟨by omega, h2⟩
      · exact Or.inl (h3 x hx)
  · rcases hf with rfl | ⟨ds, rfl, hds⟩
    · simp at hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · exact Or.inl (hds.2 x hx)
  · rcases he with rfl | ⟨y, sg, ds, rfl, hy, hsg, hds⟩
    · simp at hx
    · simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · rcases hy with rfl | rfl <;> simp
      · rcases hsg with rfl | rfl | rfl <;> simp_all
      · exact Or.inl (hds.2 x hx)

theorem not_delimiter_of_number {w : List Char} (h : NumberChars w) :
    ∀ x ∈ w, delimiter .rfc8259 x = false := by
  intro x hx
  rw [Bool.eq_false_iff]
  intro hd
  have hn := delimiter_toNat hd
  rcases numberChars_mem h x hx with hx | rfl | rfl | rfl | rfl | rfl
  · unfold IsDigitChar at hx; omega
  all_goals simp at hn

theorem numberChars_head {w : List Char} (h : NumberChars w) :
    ∃ c w', w = c :: w' ∧ (IsDigitChar c ∨ c = '-') := by
  obtain ⟨s, i, f, e, rfl, hs, hi, -, -⟩ := h
  rcases hs with rfl | rfl
  · rcases hi with rfl | ⟨d, ds, rfl, h1, h2, -⟩
    · exact ⟨'0', _, rfl, Or.inl (by simp [IsDigitChar])⟩
    · exact ⟨d, _, rfl, Or.inl ⟨by omega, h2⟩⟩
  · exact ⟨'-', _, rfl, Or.inr rfl⟩

theorem span_word {w X : List Char} (hw : ∀ x ∈ w, delimiter .rfc8259 x = false) (hX : Follow X) :
    (w ++ X).span (fun c => !delimiter .rfc8259 c) = (w, X) :=
  span_append_stop (fun x hx => by simp [hw x hx]) (fun y hy => by simp [hX y hy])

theorem tokensOf_number_exact {w X : List Char} {number : Number}
    (parsed : decimal? .rfc8259 w = some number) (hX : Follow X) :
    tokensOf (w ++ X) = (tokensOf X).map (.number number :: ·) := by
  have hw := (decimal?_sound parsed).1
  obtain ⟨c, w', rfl, hc⟩ := numberChars_head hw
  have hnd := not_delimiter_of_number hw
  have hcw : white .rfc8259 c = false := by
    have := hnd c (by simp); simp [delimiter] at this; simp [this]
  have hcq : c ≠ '"' := by
    rintro rfl
    rcases hc with hc | hc
    · simp [IsDigitChar] at hc
    · exact absurd hc (by decide)
  have hcp : NotPunct c := by
    have := hnd c (by simp)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp [delimiter, white] at this
  have hstart : (c.isDigit || c == '-' || c == '+' || c == '.') = true := by
    rcases hc with hc | rfl
    · simp [isDigit_iff'.mpr hc]
    · rfl
  have hs : step .rfc8259 c (w' ++ X) = some (some (.number number), .number, X) := by
    rw [step_other _ hcw hcq hcp]
    simp only [hstart, ite_true]
    have := span_word hnd hX
    simp only [List.cons_append] at this
    simp [this, parsed]
  simpa using tokensOf_step hs (by simp; omega)

theorem tokensOf_number {w : List Char} (hw : NumberChars w) {X : List Char} (hX : Follow X) :
    ∃ n, tokensOf (w ++ X) = (tokensOf X).map (.number n :: ·) :=
  let ⟨_, parsed⟩ := decimal?_complete hw
  ⟨_, tokensOf_number_exact parsed hX⟩

theorem tokensOf_literal {w : List Char} {tok : Token} (hw : w = "true".toList ∧ tok = .bool true ∨
    w = "false".toList ∧ tok = .bool false ∨ w = "null".toList ∧ tok = .null) {X : List Char}
    (hX : Follow X) : tokensOf (w ++ X) = (tokensOf X).map (tok :: ·) := by
  have key : ∀ (c : Char) (w' : List Char) (tok : Token),
      step .rfc8259 c (w' ++ X) = some (some tok, .literal, X) →
      tokensOf ((c :: w') ++ X) = (tokensOf X).map (tok :: ·) := fun c w' tok h => by
    simpa using tokensOf_step h (by simp; omega)
  have sp : ∀ (w : List Char), (∀ x ∈ w, delimiter .rfc8259 x = false) →
      (w ++ X).span (fun c => !delimiter .rfc8259 c) = (w, X) := fun w hw => span_word hw hX
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine key 't' ['r', 'u', 'e'] _ ?_
    rw [step_other _ (by decide) (by decide) (by simp [NotPunct])]
    have := sp ['t', 'r', 'u', 'e'] (by decide)
    simp only [List.cons_append, List.nil_append] at this
    simp [this]
  · refine key 'f' ['a', 'l', 's', 'e'] _ ?_
    rw [step_other _ (by decide) (by decide) (by simp [NotPunct])]
    have := sp ['f', 'a', 'l', 's', 'e'] (by decide)
    simp only [List.cons_append, List.nil_append] at this
    simp [this]
  · refine key 'n' ['u', 'l', 'l'] _ ?_
    rw [step_other _ (by decide) (by decide) (by simp [NotPunct])]
    have := sp ['n', 'u', 'l', 'l'] (by decide)
    simp only [List.cons_append, List.nil_append] at this
    simp [this]

end Silmaril.Proofs.Formats.JsonWire.Lexer

end
