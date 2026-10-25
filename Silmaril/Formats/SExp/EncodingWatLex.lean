module

public import Silmaril.Formats.SExp.EncodingWatDefs

/-!
# Uniqueness of WAT lexing

Longest-match uniqueness of `Lex p true` for both profiles (`lex_functional`).

The proof is a strong induction on the length of the input.  `IU N` states
that two whitespace items starting at the same position of an input shorter
than `N` coincide: whitespace items are self-delimiting (line comments end at
the first newline, block comments by `BlockTail` determinism, annotations at
the `)` closing their balanced token body, which needs `lex_ext` on the
shorter body).  Given `IU`, the whitespace before a token is determined
(`space_align`, using that no whitespace item can start where a token starts,
`noItemStart_tok`), the token is determined by longest match (`tok1_unique`),
and induction on the rest of the input determines the token list.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

/-! ## Character facts -/

theorem IsIdChar.isRunChar {c : Char} (h : IsIdChar c) : IsRunChar c := h

theorem IsPunct.not_isRunChar {c : Char} (h : IsPunct c) : ¬ IsRunChar c := by
  unfold IsPunct at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem IsPunct.ne_quote {c : Char} (h : IsPunct c) : c ≠ '"' := by
  unfold IsPunct at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem IsPunct.ne_lp {c : Char} (h : IsPunct c) : c ≠ '(' := by
  unfold IsPunct at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem IsPunct.ne_rp {c : Char} (h : IsPunct c) : c ≠ ')' := by
  unfold IsPunct at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem not_isRunChar_quote : ¬ IsRunChar '"' := by decide
theorem not_isRunChar_rp : ¬ IsRunChar ')' := by decide
theorem isIdChar_dollar : IsIdChar '$' := by decide
theorem not_space_semi : ¬ IsSpaceChar ';' := by unfold IsSpaceChar; decide
theorem not_space_lp : ¬ IsSpaceChar '(' := by unfold IsSpaceChar; decide

theorem not_tokHead_of_space {x : Char} (h : IsSpaceChar x) :
    ¬ (x = '(' ∨ x = ')' ∨ x = '"' ∨ IsRunChar x ∨ IsPunct x) := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem len_pos {l : Chars} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- Splitting at the first character of a class. -/
theorem split_first {P : Char → Prop} {a a' : Chars} {z z' : Char} {r r' : Chars}
    (ha : ∀ c ∈ a, ¬ P c) (ha' : ∀ c ∈ a', ¬ P c) (hz : P z) (hz' : P z')
    (h : a ++ z :: r = a' ++ z' :: r') : a = a' ∧ z = z' ∧ r = r' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa using h
    | cons c a' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hz) (ha' c (by simp))
  | cons c a ih =>
    cases a' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ hz') (ha c (by simp))
    | cons c' a' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih (fun x hx => ha x (by simp [hx]))
        (fun x hx => ha' x (by simp [hx])) h
      exact ⟨by rw [h1], h2, h3⟩

/-- Maximal runs of identifier characters. -/
theorem idRun_max {c₁ c₂ R₁ R₂ : Chars} (h₁ : ∀ c ∈ c₁, IsIdChar c) (h₂ : ∀ c ∈ c₂, IsIdChar c)
    (f₁ : ∀ c, R₁.head? = some c → ¬ IsIdChar c) (f₂ : ∀ c, R₂.head? = some c → ¬ IsIdChar c)
    (h : c₁ ++ R₁ = c₂ ++ R₂) : c₁ = c₂ := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => rfl
    | cons c c₂ =>
      simp only [List.nil_append, List.cons_append] at h
      exact absurd (h₂ c (by simp)) (f₁ c (by simp [h]))
  | cons c c₁ ih =>
    cases c₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      exact absurd (h₁ c (by simp)) (f₂ c (by simp [← h]))
    | cons c' c₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [ih (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h]

/-! ## Numerals -/

theorem HexNum.ne_nil {ds : Chars} {n : Nat} (h : HexNum ds n) : ds ≠ [] := by
  cases h <;> simp

theorem HexNum.mem {ds : Chars} {n : Nat} (h : HexNum ds n) :
    ∀ c ∈ ds, IsHexDigit c ∨ c = '_' := by
  induction h with
  | @one d hd => intro c hc; simp at hc; subst hc; exact Or.inl hd
  | @snoc ds n d _ hd ih =>
    intro c hc; simp at hc
    rcases hc with hc | rfl
    · exact ih c hc
    · exact Or.inl hd
  | @snocSep ds n d _ hd ih =>
    intro c hc; simp at hc
    rcases hc with hc | rfl | rfl
    · exact ih c hc
    · exact Or.inr rfl
    · exact Or.inl hd

theorem HexNum.last {ds : Chars} {n : Nat} (h : HexNum ds n) :
    ∃ ds' d, ds = ds' ++ [d] ∧ IsHexDigit d := by
  cases h with
  | @one d hd => exact ⟨[], d, rfl, hd⟩
  | @snoc ds n d _ hd => exact ⟨ds, d, rfl, hd⟩
  | @snocSep ds n d _ hd => exact ⟨ds ++ ['_'], d, by simp, hd⟩

theorem not_isHexDigit_underscore : ¬ IsHexDigit '_' := by decide

theorem HexNum.inv {x : Chars} {m : Nat} (h : HexNum x m) :
    (∃ d, x = [d] ∧ m = hexVal d) ∨
    (∃ ds n d, x = ds ++ [d] ∧ HexNum ds n ∧ m = 16 * n + hexVal d) ∨
    (∃ ds n d, x = ds ++ ['_', d] ∧ HexNum ds n ∧ m = 16 * n + hexVal d) := by
  cases h with
  | @one d _ => exact Or.inl ⟨d, rfl, rfl⟩
  | @snoc ds n d h _ => exact Or.inr (Or.inl ⟨ds, n, d, rfl, h, rfl⟩)
  | @snocSep ds n d h _ => exact Or.inr (Or.inr ⟨ds, n, d, rfl, h, rfl⟩)

theorem HexNum.not_underscore {ds : Chars} {n : Nat} (h : HexNum (ds ++ ['_']) n) : False := by
  obtain ⟨ds', d, he, hd⟩ := h.last
  have := List.append_inj' he rfl
  simp only [List.cons.injEq, and_true] at this
  rw [← this.2] at hd
  exact not_isHexDigit_underscore hd

theorem snoc_inj {a b : Chars} {x y : Char} (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
  exact ⟨h1, by simpa using h2⟩

theorem HexNum.func {ds : Chars} {n m : Nat} (h₁ : HexNum ds n) (h₂ : HexNum ds m) : n = m := by
  induction h₁ generalizing m with
  | @one d _ =>
    rcases h₂.inv with ⟨d', h, rfl⟩ | ⟨ds', n', d', h, h', rfl⟩ | ⟨ds', n', d', h, h', rfl⟩
    · simp only [List.cons.injEq, and_true] at h; rw [h]
    · rcases ds' with _ | ⟨y, ds'⟩
      · exact absurd rfl h'.ne_nil
      · simp at h
    · rcases ds' with _ | ⟨y, ds'⟩ <;> simp at h
  | @snoc ds n d h₀ _ ih =>
    rcases h₂.inv with ⟨d', h, rfl⟩ | ⟨ds', n', d', h, h', rfl⟩ | ⟨ds', n', d', h, h', rfl⟩
    · rcases ds with _ | ⟨y, ds⟩
      · exact absurd rfl h₀.ne_nil
      · simp at h
    · obtain ⟨rfl, rfl⟩ := snoc_inj h
      rw [ih h']
    · have h3 : ds ++ [d] = (ds' ++ ['_']) ++ [d'] := by simpa using h
      obtain ⟨rfl, -⟩ := List.append_inj' h3 rfl
      exact h₀.not_underscore.elim
  | @snocSep ds n d h₀ _ ih =>
    rcases h₂.inv with ⟨d', h, rfl⟩ | ⟨ds', n', d', h, h', rfl⟩ | ⟨ds', n', d', h, h', rfl⟩
    · rcases ds with _ | ⟨y, ds⟩ <;> simp at h
    · have h3 : (ds ++ ['_']) ++ [d] = ds' ++ [d'] := by simpa using h
      obtain ⟨rfl, -⟩ := List.append_inj' h3 rfl
      exact h'.not_underscore.elim
    · have h3 : (ds ++ ['_']) ++ [d] = (ds' ++ ['_']) ++ [d'] := by simpa using h
      obtain ⟨h4, rfl⟩ := snoc_inj h3
      obtain ⟨rfl, -⟩ := snoc_inj h4
      rw [ih h']

/-! ## Strings -/

theorem StringElem.head {e : Chars} {b : List UInt8} (h : StringElem e b) :
    ∃ c t, e = c :: t ∧ c ≠ '"' := by
  cases h
  case char hq _ => exact ⟨_, [], rfl, hq⟩
  all_goals exact ⟨'\\', _, rfl, by decide⟩

theorem StringElem.prefix {e₁ e₂ x₁ x₂ : Chars} {b₁ b₂ : List UInt8}
    (h₁ : StringElem e₁ b₁) (h₂ : StringElem e₂ b₂) (he : e₁ ++ x₁ = e₂ ++ x₂) :
    e₁ = e₂ ∧ b₁ = b₂ := by
  have n1 : ¬ IsHexDigit 't' := by decide
  have n2 : ¬ IsHexDigit 'n' := by decide
  have n3 : ¬ IsHexDigit 'r' := by decide
  have n4 : ¬ IsHexDigit '"' := by decide
  have n5 : ¬ IsHexDigit '\'' := by decide
  have n6 : ¬ IsHexDigit '\\' := by decide
  have n7 : ¬ IsHexDigit 'u' := by decide
  cases h₁ with
  | @unicode ds n hn _ =>
    cases h₂ with
    | @unicode ds' n' hn' _ =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq,
        true_and] at he
      have hd : ∀ c ∈ ds, ¬ c = '}' := fun c hc => by
        rcases hn.mem c hc with h | rfl
        · rintro rfl; exact absurd h (by decide)
        · decide
      have hd' : ∀ c ∈ ds', ¬ c = '}' := fun c hc => by
        rcases hn'.mem c hc with h | rfl
        · rintro rfl; exact absurd h (by decide)
        · decide
      obtain ⟨rfl, -, -⟩ := split_first (P := (· = '}')) hd hd' rfl rfl he
      rw [hn.func hn']
      exact ⟨rfl, rfl⟩
    | _ =>
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq] at he
      (try casesm* _ ∧ _); subst_vars; simp_all
  | _ =>
    cases h₂ <;>
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq] at he <;>
      (try casesm* _ ∧ _) <;> subst_vars <;> simp_all

theorem StringBody.prefix {b₁ b₂ r₁ r₂ : Chars} {bs₁ bs₂ : List UInt8}
    (h₁ : StringBody b₁ bs₁) (h₂ : StringBody b₂ bs₂) (h : b₁ ++ '"' :: r₁ = b₂ ++ '"' :: r₂) :
    b₁ = b₂ ∧ bs₁ = bs₂ := by
  induction h₁ generalizing b₂ bs₂ with
  | nil =>
    cases h₂ with
    | nil => exact ⟨rfl, rfl⟩
    | cons he _ =>
      obtain ⟨c, t, rfl, hc⟩ := he.head
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm hc
  | @cons e rest b bs he₁ _ ih =>
    cases h₂ with
    | nil =>
      obtain ⟨c, t, rfl, hc⟩ := he₁.head
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 hc
    | cons he₂ hr₂ =>
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, rfl⟩ := StringElem.prefix he₁ he₂ h
      obtain ⟨rfl, rfl⟩ := ih hr₂ (List.append_cancel_left h)
      exact ⟨rfl, rfl⟩

theorem StringLit.head {s : Chars} {bs : List UInt8} (h : StringLit s bs) : ∃ t, s = '"' :: t := by
  obtain ⟨b, rfl, -⟩ := h
  exact ⟨_, rfl⟩

theorem StringLit.prefix {s₁ s₂ r₁ r₂ : Chars} {bs₁ bs₂ : List UInt8}
    (h₁ : StringLit s₁ bs₁) (h₂ : StringLit s₂ bs₂) (h : s₁ ++ r₁ = s₂ ++ r₂) :
    s₁ = s₂ ∧ bs₁ = bs₂ := by
  obtain ⟨b₁, rfl, hb₁, -⟩ := h₁
  obtain ⟨b₂, rfl, hb₂, -⟩ := h₂
  simp only [List.cons_append, List.append_assoc, List.cons.injEq,
    true_and] at h
  obtain ⟨rfl, rfl⟩ := hb₁.prefix hb₂ h
  exact ⟨rfl, rfl⟩

/-! ## Token runs -/

theorem RunPieces.head {cs : Chars} (h : RunPieces cs) (hne : cs ≠ []) :
    ∃ x c', cs = x :: c' ∧ (IsRunChar x ∨ x = '"') := by
  cases h with
  | nil => exact absurd rfl hne
  | char hc _ => exact ⟨_, _, rfl, Or.inl hc⟩
  | @str s rest bs hs _ =>
    obtain ⟨t, rfl⟩ := hs.head
    exact ⟨'"', t ++ rest, rfl, Or.inr rfl⟩

theorem RunPieces.of_chars {cs : Chars} (h : ∀ c ∈ cs, IsRunChar c) : RunPieces cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact .char (h c (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem RunPieces.max {c₁ c₂ R₁ R₂ : Chars} (h₁ : RunPieces c₁) (h₂ : RunPieces c₂)
    (f₁ : ∀ c, R₁.head? = some c → ¬ IsRunChar c ∧ c ≠ '"')
    (f₂ : ∀ c, R₂.head? = some c → ¬ IsRunChar c ∧ c ≠ '"')
    (h : c₁ ++ R₁ = c₂ ++ R₂) : c₁ = c₂ := by
  induction h₁ generalizing c₂ with
  | nil =>
    cases h₂ with
    | nil => rfl
    | @char c rest hc _ =>
      simp only [List.nil_append, List.cons_append] at h
      exact absurd hc (f₁ c (by simp [h])).1
    | @str s rest bs hs _ =>
      obtain ⟨t, rfl⟩ := hs.head
      simp only [List.nil_append, List.cons_append, List.append_assoc] at h
      exact absurd rfl (f₁ '"' (by simp [h])).2
  | @char c rest hc _ ih =>
    cases h₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      exact absurd hc (f₂ c (by simp [← h])).1
    | @char c' rest' _ hr' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [ih hr' h]
    | @str s rest' bs hs _ =>
      obtain ⟨t, rfl⟩ := hs.head
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
      rw [h.1] at hc
      exact absurd hc not_isRunChar_quote
  | @str s rest bs hs _ ih =>
    cases h₂ with
    | nil =>
      obtain ⟨t, rfl⟩ := hs.head
      simp only [List.nil_append, List.cons_append, List.append_assoc] at h
      exact absurd rfl (f₂ '"' (by simp [← h])).2
    | @char c' rest' hc' _ =>
      obtain ⟨t, rfl⟩ := hs.head
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
      rw [← h.1] at hc'
      exact absurd hc' not_isRunChar_quote
    | @str s' rest' bs' hs' hr' =>
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, -⟩ := StringLit.prefix hs hs' h
      rw [ih hr' (List.append_cancel_left h)]

theorem IdRun.chars {cs : Chars} {a : Atom} (h : IdRun cs a) :
    cs ≠ [] ∧ ∀ c ∈ cs, IsIdChar c := by
  cases h with
  | @sym cs hne hc _ => exact ⟨hne, hc⟩
  | @id rest _ hc =>
    refine ⟨by simp, ?_⟩
    intro c hc'
    simp only [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact isIdChar_dollar
    · exact hc c hc'

theorem IdRun.func {cs : Chars} {a₁ a₂ : Atom} (h₁ : IdRun cs a₁) (h₂ : IdRun cs a₂) : a₁ = a₂ := by
  cases h₁ with
  | @sym cs _ _ hd =>
    cases h₂ with
    | sym => rfl
    | @id rest hne _ =>
      have := len_pos hne
      exact absurd ⟨rfl, by simp only [List.length_cons]; omega⟩ hd
  | @id rest hne _ =>
    cases h₂ with
    | @sym _ _ _ hd =>
      have := len_pos hne
      exact absurd ⟨rfl, by simp only [List.length_cons]; omega⟩ hd
    | id => rfl

theorem RunAtom3.pieces {cs : Chars} {a : Atom} (h : RunAtom3 cs a) : RunPieces cs := by
  cases h with
  | str hs => simpa using RunPieces.str hs RunPieces.nil
  | idRun hi => exact RunPieces.of_chars fun c hc => (hi.chars.2 c hc).isRunChar
  | quotedId hq _ =>
    obtain ⟨bs, hs, -⟩ := hq
    exact .char isIdChar_dollar.isRunChar (by simpa using RunPieces.str hs RunPieces.nil)

theorem RunAtom3.ne_nil {cs : Chars} {a : Atom} (h : RunAtom3 cs a) : cs ≠ [] := by
  cases h with
  | str hs => obtain ⟨t, rfl⟩ := hs.head; simp
  | idRun hi => exact hi.chars.1
  | quotedId => simp

theorem RunAtom3.func {cs : Chars} {a₁ a₂ : Atom} (h₁ : RunAtom3 cs a₁) (h₂ : RunAtom3 cs a₂) :
    a₁ = a₂ := by
  cases h₁ with
  | str hs =>
    cases h₂ with
    | str hs' => rw [(StringLit.prefix (r₁ := []) (r₂ := []) hs hs' rfl).2]
    | idRun hi =>
      obtain ⟨t, rfl⟩ := hs.head
      exact absurd (hi.chars.2 '"' (by simp)) (by decide)
    | quotedId => obtain ⟨t, ht⟩ := hs.head; simp at ht
  | idRun hi =>
    cases h₂ with
    | str hs' =>
      obtain ⟨t, rfl⟩ := hs'.head
      exact absurd (hi.chars.2 '"' (by simp)) (by decide)
    | idRun hi' => exact hi.func hi'
    | quotedId hq _ =>
      obtain ⟨bs, hs, -⟩ := hq
      obtain ⟨t, rfl⟩ := hs.head
      exact absurd (hi.chars.2 '"' (by simp)) (by decide)
  | quotedId hq _ =>
    cases h₂ with
    | str hs' => obtain ⟨t, ht⟩ := hs'.head; simp at ht
    | idRun hi =>
      obtain ⟨bs, hs, -⟩ := hq
      obtain ⟨t, rfl⟩ := hs.head
      exact absurd (hi.chars.2 '"' (by simp)) (by decide)
    | quotedId hq' _ =>
      obtain ⟨bs, hs, hu⟩ := hq
      obtain ⟨bs', hs', hu'⟩ := hq'
      obtain ⟨-, rfl⟩ := StringLit.prefix (r₁ := []) (r₂ := []) hs hs' rfl
      rw [hu] at hu'
      cases hu'
      rfl

/-! ## Tokens -/

/-- The shape of a Wasm 1.0 token. -/
theorem tok_view1 {top : Bool} {c R : Chars} {t : Tok} (h : Tok1 .v1 top c t)
    (f : Follow .v1 t R) :
    ∃ x c', c = x :: c' ∧
      ((x = '(' ∧ t = .lp ∧ c' = [] ∧ R.head? ≠ some ';') ∨
       (x = ')' ∧ t = .rp ∧ c' = []) ∨
       (x = '"' ∧ ∃ bs, t = .atom (.str bs) ∧ StringLit c bs) ∨
       (IsIdChar x ∧ (∃ a, t = .atom a ∧ IdRun c a) ∧
         ∀ y, R.head? = some y → ¬ IsIdChar y)) := by
  cases t with
  | lp => exact ⟨'(', [], h, Or.inl ⟨rfl, rfl, rfl, f⟩⟩
  | rp => exact ⟨')', [], h, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  | atom a =>
    cases a with
    | str bs =>
      have hs : StringLit c bs := h
      obtain ⟨u, rfl⟩ := hs.head
      exact ⟨'"', u, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, bs, rfl, hs⟩))⟩
    | sym s =>
      have hi : IdRun c (.sym s) := h
      have hf : ∀ y, R.head? = some y → ¬ IsIdChar y := f
      obtain ⟨hne, hc⟩ := hi.chars
      obtain ⟨x, c', rfl⟩ := List.exists_cons_of_ne_nil hne
      exact ⟨x, c', rfl, Or.inr (Or.inr (Or.inr ⟨hc x (by simp), ⟨_, rfl, hi⟩, hf⟩))⟩
    | id s =>
      have hi : IdRun c (.id s) := h
      have hf : ∀ y, R.head? = some y → ¬ IsIdChar y := f
      obtain ⟨hne, hc⟩ := hi.chars
      obtain ⟨x, c', rfl⟩ := List.exists_cons_of_ne_nil hne
      exact ⟨x, c', rfl, Or.inr (Or.inr (Or.inr ⟨hc x (by simp), ⟨_, rfl, hi⟩, hf⟩))⟩
  | reserved => exact False.elim h
  | punct _ => exact False.elim h

/-- The shape of a Core 3.0 token. -/
theorem tok_view3 {top : Bool} {c R : Chars} {t : Tok} (h : Tok1 .core3 top c t)
    (f : Follow .core3 t R) :
    ∃ x c', c = x :: c' ∧
      ((x = '(' ∧ t = .lp ∧ c' = [] ∧ R.head? ≠ some ';' ∧ R.head? ≠ some '@') ∨
       (x = ')' ∧ t = .rp ∧ c' = []) ∨
       ((IsRunChar x ∨ x = '"') ∧ t ≠ .lp ∧ t ≠ .rp ∧ (∀ d, t ≠ .punct d) ∧ RunPieces c ∧
         ¬ c.take 2 = [';', ';'] ∧ ∀ y, R.head? = some y → ¬ IsRunChar y ∧ y ≠ '"') ∨
       (IsPunct x ∧ t = .punct x ∧ c' = [] ∧ (x = ';' → R.head? ≠ some ';'))) := by
  cases t with
  | lp =>
    have f' : R.head? ≠ some ';' ∧ R.head? ≠ some '@' := f
    exact ⟨'(', [], h, Or.inl ⟨rfl, rfl, rfl, f'.1, f'.2⟩⟩
  | rp => exact ⟨')', [], h, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  | atom a =>
    have h' : RunAtom3 c a ∧ ¬ c.take 2 = [';', ';'] := h
    have f' : ∀ y, R.head? = some y → ¬ IsRunChar y ∧ y ≠ '"' := f
    obtain ⟨x, c', rfl, hx⟩ := h'.1.pieces.head h'.1.ne_nil
    exact ⟨x, c', rfl, Or.inr (Or.inr (Or.inl ⟨hx, by simp, by simp, by simp, h'.1.pieces, h'.2,
      f'⟩))⟩
  | reserved =>
    have h' : top = false ∧ RunPieces c ∧ c ≠ [] ∧ (¬ ∃ a, RunAtom3 c a) ∧
        ¬ c.take 2 = [';', ';'] := h
    have f' : ∀ y, R.head? = some y → ¬ IsRunChar y ∧ y ≠ '"' := f
    obtain ⟨x, c', rfl, hx⟩ := h'.2.1.head h'.2.2.1
    exact ⟨x, c', rfl, Or.inr (Or.inr (Or.inl ⟨hx, by simp, by simp, by simp, h'.2.1, h'.2.2.2.2,
      f'⟩))⟩
  | punct d =>
    have h' : top = false ∧ IsPunct d ∧ c = [d] := h
    have f' : d = ';' → R.head? ≠ some ';' := f
    obtain ⟨-, hd, rfl⟩ := h'
    exact ⟨d, [], rfl, Or.inr (Or.inr (Or.inr ⟨hd, rfl, rfl, f'⟩))⟩

/-- Profile-independent facts about the first character of a token. -/
theorem tok_head {p : Profile} {top : Bool} {c R : Chars} {t : Tok} (h : Tok1 p top c t)
    (f : Follow p t R) :
    ∃ x c', c = x :: c' ∧ (x = '(' ∨ x = ')' ∨ x = '"' ∨ IsRunChar x ∨ IsPunct x) ∧
      (x = '(' → c' = [] ∧ R.head? ≠ some ';' ∧ (p = .core3 → R.head? ≠ some '@')) ∧
      (x = ')' → t = .rp ∧ c' = []) := by
  cases p with
  | v1 =>
    obtain ⟨x, d, rfl, v⟩ := tok_view1 h f
    refine ⟨x, d, rfl, ?_⟩
    rcases v with ⟨rfl, rfl, rfl, hR⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, -⟩ | ⟨hx, -⟩
    · exact ⟨Or.inl rfl, fun _ => ⟨rfl, hR, fun h => nomatch h⟩, fun h => absurd h (by decide)⟩
    · exact ⟨Or.inr (Or.inl rfl), fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
    · refine ⟨Or.inr (Or.inr (Or.inr (Or.inl hx.isRunChar))), fun h => ?_, fun h => ?_⟩ <;>
        (subst h; exact absurd hx (by decide))
  | core3 =>
    obtain ⟨x, d, rfl, v⟩ := tok_view3 h f
    refine ⟨x, d, rfl, ?_⟩
    rcases v with ⟨rfl, rfl, rfl, hR, hR'⟩ | ⟨rfl, rfl, rfl⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact ⟨Or.inl rfl, fun _ => ⟨rfl, hR, fun _ => hR'⟩, fun h => absurd h (by decide)⟩
    · exact ⟨Or.inr (Or.inl rfl), fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩⟩
    · refine ⟨?_, fun h => ?_, fun h => ?_⟩
      · rcases hx with hx | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · exact Or.inr (Or.inr (Or.inl rfl))
      all_goals (subst h; exact absurd hx (by decide))
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr hx))), fun h => absurd h hx.ne_lp,
        fun h => absurd h hx.ne_rp⟩

theorem tok_ne_nil {p : Profile} {top : Bool} {c R : Chars} {t : Tok} (h : Tok1 p top c t)
    (f : Follow p t R) : c ≠ [] := by
  obtain ⟨x, d, rfl, -⟩ := tok_head h f
  simp

/-- A token starting with `)` is `rp`. -/
theorem tok_rp {p : Profile} {top : Bool} {c R m : Chars} {t : Tok} (h : Tok1 p top c t)
    (f : Follow p t R) (hc : c ++ R = ')' :: m) : t = .rp ∧ c = [')'] := by
  obtain ⟨x, d, rfl, -, -, hrp⟩ := tok_head h f
  simp only [List.cons_append, List.cons.injEq] at hc
  obtain ⟨rfl, -⟩ := hc
  obtain ⟨rfl, rfl⟩ := hrp rfl
  exact ⟨rfl, rfl⟩

/-- No token starts with `;;` (the line comment wins the tie with a reserved token). -/
theorem tok_not_semisemi {p : Profile} {top : Bool} {c R z : Chars} {t : Tok}
    (h : Tok1 p top c t) (f : Follow p t R) (hc : c ++ R = ';' :: ';' :: z) : False := by
  cases p with
  | v1 =>
    obtain ⟨x, d, rfl, v⟩ := tok_view1 h f
    simp only [List.cons_append, List.cons.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    rcases v with ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ <;> revert hx <;> decide
  | core3 =>
    obtain ⟨x, d, rfl, v⟩ := tok_view3 h f
    simp only [List.cons_append, List.cons.injEq] at hc
    obtain ⟨rfl, hc⟩ := hc
    rcases v with ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -, -, -, -, hss, fr⟩ | ⟨-, -, rfl, hR⟩
    · revert hx; decide
    · revert hx; decide
    · rcases hx with hx | hx <;> revert hx <;> decide
    · simp only [List.nil_append] at hc
      exact hR rfl (by simp [hc])

theorem tok3_run_func {top : Bool} {c : Chars} {t₁ t₂ : Tok} (h₁ : Tok1 .core3 top c t₁)
    (h₂ : Tok1 .core3 top c t₂) (l₁ : t₁ ≠ .lp) (r₁ : t₁ ≠ .rp) (l₂ : t₂ ≠ .lp)
    (r₂ : t₂ ≠ .rp) : t₁ = t₂ := by
  -- a punctuation token `[d]` is no run
  have punct_run : ∀ {d : Char} {t : Tok}, IsPunct d → Tok1 .core3 top [d] t → t ≠ .lp →
      t ≠ .rp → (∀ e, t ≠ .punct e) → False := by
    intro d t hd ht hl hr hp
    cases t with
    | lp => exact hl rfl
    | rp => exact hr rfl
    | punct e => exact hp e rfl
    | atom a =>
      have ht' : RunAtom3 [d] a ∧ _ := ht
      obtain ⟨x, c', e, hx⟩ := ht'.1.pieces.head ht'.1.ne_nil
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      rcases hx with hx | hx
      · exact hd.not_isRunChar hx
      · exact hd.ne_quote hx
    | reserved =>
      have ht' : top = false ∧ RunPieces [d] ∧ [d] ≠ [] ∧ _ := ht
      obtain ⟨x, c', e, hx⟩ := ht'.2.1.head ht'.2.2.1
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      rcases hx with hx | hx
      · exact hd.not_isRunChar hx
      · exact hd.ne_quote hx
  cases t₁ with
  | lp => exact absurd rfl l₁
  | rp => exact absurd rfl r₁
  | punct d₁ =>
    have h₁' : top = false ∧ IsPunct d₁ ∧ c = [d₁] := h₁
    obtain ⟨-, hd₁, rfl⟩ := h₁'
    cases t₂ with
    | punct d₂ =>
      have h₂' : top = false ∧ IsPunct d₂ ∧ [d₁] = [d₂] := h₂
      simp only [List.cons.injEq, and_true] at h₂'
      rw [h₂'.2.2]
    | _ => exact (punct_run hd₁ h₂ l₂ r₂ (by simp)).elim
  | atom a₁ =>
    have h₁' : RunAtom3 c a₁ ∧ ¬ c.take 2 = [';', ';'] := h₁
    cases t₂ with
    | lp => exact absurd rfl l₂
    | rp => exact absurd rfl r₂
    | atom a₂ =>
      have h₂' : RunAtom3 c a₂ ∧ ¬ c.take 2 = [';', ';'] := h₂
      rw [RunAtom3.func h₁'.1 h₂'.1]
    | reserved =>
      have h₂' : top = false ∧ RunPieces c ∧ c ≠ [] ∧ (¬ ∃ a, RunAtom3 c a) ∧
          ¬ c.take 2 = [';', ';'] := h₂
      exact absurd ⟨a₁, h₁'.1⟩ h₂'.2.2.2.1
    | punct d₂ =>
      have h₂' : top = false ∧ IsPunct d₂ ∧ c = [d₂] := h₂
      obtain ⟨-, hd₂, rfl⟩ := h₂'
      exact (punct_run hd₂ h₁ l₁ r₁ (by simp)).elim
  | reserved =>
    have h₁' : top = false ∧ RunPieces c ∧ c ≠ [] ∧ (¬ ∃ a, RunAtom3 c a) ∧
        ¬ c.take 2 = [';', ';'] := h₁
    cases t₂ with
    | lp => exact absurd rfl l₂
    | rp => exact absurd rfl r₂
    | atom a₂ =>
      have h₂' : RunAtom3 c a₂ ∧ ¬ c.take 2 = [';', ';'] := h₂
      exact absurd ⟨a₂, h₂'.1⟩ h₁'.2.2.2.1
    | reserved => rfl
    | punct d₂ =>
      have h₂' : top = false ∧ IsPunct d₂ ∧ c = [d₂] := h₂
      obtain ⟨-, hd₂, rfl⟩ := h₂'
      exact (punct_run hd₂ h₁ l₁ r₁ (by simp)).elim

/-- **Longest match**: a token followed by its `Follow` context is determined. -/
theorem tok1_unique {p : Profile} {top : Bool} {c₁ c₂ R₁ R₂ : Chars} {t₁ t₂ : Tok}
    (h₁ : Tok1 p top c₁ t₁) (f₁ : Follow p t₁ R₁) (h₂ : Tok1 p top c₂ t₂)
    (f₂ : Follow p t₂ R₂) (h : c₁ ++ R₁ = c₂ ++ R₂) : c₁ = c₂ ∧ t₁ = t₂ := by
  cases p with
  | v1 =>
    obtain ⟨x₁, d₁, rfl, v₁⟩ := tok_view1 h₁ f₁
    obtain ⟨x₂, d₂, rfl, v₂⟩ := tok_view1 h₂ f₂
    have hx : x₁ = x₂ := by
      simp only [List.cons_append, List.cons.injEq] at h; exact h.1
    subst hx
    rcases v₁ with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, bs₁, rfl, hs₁⟩ |
        ⟨hx₁, ⟨a₁, rfl, hi₁⟩, fi₁⟩ <;>
      rcases v₂ with ⟨hx₂, rfl, rfl, -⟩ | ⟨hx₂, rfl, rfl⟩ | ⟨hx₂, bs₂, rfl, hs₂⟩ |
        ⟨hx₂, ⟨a₂, rfl, hi₂⟩, fi₂⟩
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (exfalso; revert hx₂; decide)
      | (exfalso; subst hx₂; revert hx₁; decide)
      | skip
    · obtain ⟨hc, hb⟩ := StringLit.prefix hs₁ hs₂ h
      exact ⟨hc, by rw [hb]⟩
    · have hc := idRun_max hi₁.chars.2 hi₂.chars.2 fi₁ fi₂ h
      refine ⟨hc, ?_⟩
      rw [hc] at hi₁
      rw [IdRun.func hi₁ hi₂]
  | core3 =>
    obtain ⟨x₁, d₁, rfl, v₁⟩ := tok_view3 h₁ f₁
    obtain ⟨x₂, d₂, rfl, v₂⟩ := tok_view3 h₂ f₂
    have hx : x₁ = x₂ := by
      simp only [List.cons_append, List.cons.injEq] at h; exact h.1
    subst hx
    rcases v₁ with ⟨rfl, rfl, rfl, -, -⟩ | ⟨rfl, rfl, rfl⟩ | ⟨hx₁, l₁, r₁, -, hp₁, -, fr₁⟩ |
        ⟨hx₁, rfl, rfl, -⟩ <;>
      rcases v₂ with ⟨hx₂, rfl, rfl, -, -⟩ | ⟨hx₂, rfl, rfl⟩ | ⟨hx₂, l₂, r₂, -, hp₂, -, fr₂⟩ |
        ⟨hx₂, rfl, rfl, -⟩
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (exfalso; revert hx₂; decide)
      | (exfalso; subst hx₂; revert hx₁; decide)
      | (exfalso; rcases hx₁ with hx₁ | hx₁
         · exact hx₂.not_isRunChar hx₁
         · exact hx₂.ne_quote hx₁)
      | (exfalso; rcases hx₂ with hx₂ | hx₂
         · exact hx₁.not_isRunChar hx₂
         · exact hx₁.ne_quote hx₂)
      | skip
    have hc := RunPieces.max hp₁ hp₂ fr₁ fr₂ h
    refine ⟨hc, ?_⟩
    rw [hc] at h₁
    exact tok3_run_func h₁ h₂ l₁ r₁ l₂ r₂

/-- `Follow` only depends on the next character, and `)` follows every token. -/
theorem follow_append_rp {p : Profile} {t : Tok} {R m : Chars} (f : Follow p t R) :
    Follow p t (R ++ ')' :: m) := by
  cases t with
  | punct d =>
    cases p with
    | v1 => trivial
    | core3 =>
      intro hd
      cases R with
      | cons x R => exact f hd
      | nil => simp
  | _ =>
    cases R with
    | cons x R =>
      cases p <;> (try (rename_i a; cases a)) <;> exact f
    | nil =>
      cases p <;> (try (rename_i a; cases a)) <;> simp [Follow] <;> decide

/-! ## Whitespace items -/

theorem BlockTail.ne_nil {t : Chars} (h : BlockTail t) : t ≠ [] := by
  cases h with
  | @nested a r ha _ => cases ha; simp
  | _ => simp

theorem blockTail_prefix : ∀ (n : Nat) {t₁ r₁ t₂ r₂ : Chars}, (t₁ ++ r₁).length < n →
    BlockTail t₁ → BlockTail t₂ → t₁ ++ r₁ = t₂ ++ r₂ → t₁ = t₂
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, t₁, r₁, t₂, r₂, hn, h₁, h₂, h => by
    cases h₁ with
    | close =>
      cases h₂ with
      | close => rfl
      | @plain c r hc _ _ =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1.symm hc
      | @semi r hr hr' =>
        obtain ⟨y, r', rfl⟩ := List.exists_cons_of_ne_nil hr'.ne_nil
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        exact absurd (by rw [← h.2.1]; rfl) hr
      | paren =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 (by decide)
      | @nested a r ha _ =>
        cases ha
        simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
        exact absurd h.1 (by decide)
    | @plain c r hc hc' hr =>
      cases h₂ with
      | close =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 hc
      | @plain c' r' _ _ hr₂ =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        rw [blockTail_prefix n (by simp only [List.cons_append, List.length_cons] at hn; omega)
          hr hr₂ h]
      | semi =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 hc
      | paren =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 hc'
      | @nested a r' ha _ =>
        cases ha
        simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
        exact absurd h.1 hc'
    | @semi r hr hr' =>
      cases h₂ with
      | close =>
        obtain ⟨y, r', rfl⟩ := List.exists_cons_of_ne_nil hr'.ne_nil
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        exact absurd (by rw [h.2.1]; rfl) hr
      | @plain c' r' hc _ _ =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1.symm hc
      | @semi r₂' _ hr₂ =>
        simp only [List.cons_append, List.cons.injEq, true_and] at h
        rw [blockTail_prefix n (by simp only [List.cons_append, List.length_cons] at hn; omega)
          hr' hr₂ h]
      | paren =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 (by decide)
      | @nested a r' ha _ =>
        cases ha
        simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
        exact absurd h.1 (by decide)
    | @paren r hr hr' =>
      cases h₂ with
      | close =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 (by decide)
      | @plain c' r' _ hc _ =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1.symm hc
      | semi =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact absurd h.1 (by decide)
      | @paren r₂' _ hr₂ =>
        simp only [List.cons_append, List.cons.injEq, true_and] at h
        rw [blockTail_prefix n (by simp only [List.cons_append, List.length_cons] at hn; omega)
          hr' hr₂ h]
      | @nested a r' ha _ =>
        cases ha
        obtain ⟨y, r'', rfl⟩ := List.exists_cons_of_ne_nil hr'.ne_nil
        simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
        exact absurd (by rw [h.1]; rfl) hr
    | @nested a r ha hr =>
      cases ha with
      | @mk t ht =>
      cases h₂ with
      | close =>
        simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
        exact absurd h.1 (by decide)
      | @plain c' r' _ hc _ =>
        simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
        exact absurd h.1.symm hc
      | semi =>
        simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
        exact absurd h.1 (by decide)
      | @paren r₂' hr₂ hr₂' =>
        obtain ⟨y, r'', rfl⟩ := List.exists_cons_of_ne_nil hr₂'.ne_nil
        simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
        exact absurd (by rw [← h.1]; rfl) hr₂
      | @nested a' r' ha' hr' =>
        cases ha' with
        | @mk t' ht' =>
        simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
        have hn' : (t ++ (r ++ r₁)).length < n := by
          simp only [List.cons_append, List.append_assoc, List.length_cons,
            List.length_append] at hn ⊢
          omega
        have e := blockTail_prefix n hn' ht ht' h
        subst e
        have h' := List.append_cancel_left h
        have hn'' : (r ++ r₁).length < n := by
          simp only [List.cons_append, List.append_assoc, List.length_cons,
            List.length_append] at hn ⊢
          omega
        rw [blockTail_prefix n hn'' hr hr' h']

theorem SpaceItem.view {p : Profile} {a : Chars} (h : SpaceItem p a) :
    (∃ x, a = [x] ∧ IsSpaceChar x) ∨
    (∃ body nl, a = ';' :: ';' :: (body ++ [nl]) ∧ NoNewline p body ∧ IsNewlineP p nl) ∨
    (∃ t, a = '(' :: ';' :: t ∧ BlockTail t) ∨
    (∃ idc body ts, p = .core3 ∧ a = '(' :: '@' :: (idc ++ body ++ [')']) ∧ AnnotId idc ∧
      (∀ c, body.head? = some c → ¬ IsRunChar c ∧ c ≠ '"') ∧ Lex .core3 false body ts ∧
      Balanced ts) := by
  cases h with
  | @char _ x hx => exact Or.inl ⟨x, rfl, hx⟩
  | @line _ body nl hb hnl => exact Or.inr (Or.inl ⟨body, nl, rfl, hb, hnl⟩)
  | @block _ cs hb =>
    cases hb with
    | @mk t ht => exact Or.inr (Or.inr (Or.inl ⟨t, rfl, ht⟩))
  | @annot idc body ts hi hf hl hbal =>
    exact Or.inr (Or.inr (Or.inr ⟨idc, body, ts, rfl, rfl, hi, hf, hl, hbal⟩))

theorem SpaceItem.cons {p : Profile} {a : Chars} (h : SpaceItem p a) : ∃ x t, a = x :: t := by
  rcases h.view with ⟨x, rfl, -⟩ | ⟨b, nl, rfl, -⟩ | ⟨t, rfl, -⟩ | ⟨i, b, ts, -, rfl, -⟩ <;>
    exact ⟨_, _, rfl⟩

/-- No whitespace item starts at the beginning of `X`. -/
def NoItemStart (p : Profile) (X : Chars) : Prop := ∀ a b, SpaceItem p a → a ++ b = X → False

theorem noItemStart_nil {p : Profile} : NoItemStart p [] := by
  intro a b ha hab
  obtain ⟨x, t, rfl⟩ := ha.cons
  simp at hab

theorem noItemStart_rp {p : Profile} {m : Chars} : NoItemStart p (')' :: m) := by
  intro a b ha hab
  rcases ha.view with ⟨x, rfl, hx⟩ | ⟨b, nl, rfl, -⟩ | ⟨t, rfl, -⟩ | ⟨i, b, ts, -, rfl, -⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hab
    rw [hab.1] at hx
    exact not_tokHead_of_space hx (Or.inr (Or.inl rfl))
  all_goals (simp only [List.cons_append, List.cons.injEq] at hab; exact absurd hab.1 (by decide))

theorem noItemStart_eof {p : Profile} {body : Chars} (hb : NoNewline p body) :
    NoItemStart p (';' :: ';' :: body) := by
  intro a b ha hab
  rcases ha.view with ⟨x, rfl, hx⟩ | ⟨b', nl, rfl, -, hnl⟩ | ⟨t, rfl, -⟩ | ⟨i, b', ts, -, rfl, -⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hab
    rw [hab.1] at hx
    exact not_space_semi hx
  · simp only [List.cons_append, List.append_assoc, List.cons.injEq,
      true_and] at hab
    exact hb nl (by rw [← hab]; simp) hnl
  all_goals (simp only [List.cons_append, List.cons.injEq] at hab; exact absurd hab.1 (by decide))

/-- No whitespace item starts where a token starts. -/
theorem noItemStart_tok {p : Profile} {top : Bool} {c R : Chars} {t : Tok} (h : Tok1 p top c t)
    (f : Follow p t R) : NoItemStart p (c ++ R) := by
  intro a b ha hab
  obtain ⟨x, d, rfl, hx, hlp, -⟩ := tok_head h f
  rcases ha.view with ⟨y, rfl, hy⟩ | ⟨bd, nl, rfl, -, -⟩ | ⟨u, rfl, -⟩ |
      ⟨idc, bd, ts, rfl, rfl, -⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact not_tokHead_of_space hy hx
  · exact tok_not_semisemi (z := bd ++ nl :: b) h f (by rw [← hab]; simp)
  · simp only [List.cons_append, List.cons.injEq] at hab
    obtain ⟨rfl, hab⟩ := hab
    obtain ⟨rfl, hR, -⟩ := hlp rfl
    simp only [List.nil_append] at hab
    exact hR (by rw [← hab]; rfl)
  · simp only [List.cons_append, List.cons.injEq] at hab
    obtain ⟨rfl, hab⟩ := hab
    obtain ⟨rfl, -, hR⟩ := hlp rfl
    simp only [List.nil_append] at hab
    exact hR rfl (by rw [← hab]; rfl)

/-! ## Uniqueness of whitespace items, by induction on the input length -/

/-- Two whitespace items at the start of an input shorter than `N` coincide. -/
def IU (N : Nat) : Prop := ∀ (p : Profile) (a₁ b₁ a₂ b₂ : Chars), (a₁ ++ b₁).length < N →
  SpaceItem p a₁ → SpaceItem p a₂ → a₁ ++ b₁ = a₂ ++ b₂ → a₁ = a₂

theorem space_suffix {N : Nat} (hIU : IU N) : ∀ (n : Nat) {p : Profile} {s y : Chars},
    s.length < n → Space p s → Space p (s ++ y) → (s ++ y).length < N → Space p y
  | 0, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, s, y, hn, hs, hsy, hN => by
    cases hs with
    | nil => simpa using hsy
    | @cons _ a b ha hb =>
      generalize hx : a ++ b ++ y = x at hsy
      cases hsy with
      | nil =>
        obtain ⟨z, t, rfl⟩ := ha.cons
        simp at hx
      | @cons _ a' b' ha' hb' =>
        have e : a = a' := hIU p a (b ++ y) a' b'
          (by simp only [List.length_append] at hN ⊢; omega) ha ha'
          (by rw [← hx, List.append_assoc])
        subst e
        have e : b ++ y = b' := by simpa using hx
        subst e
        obtain ⟨z, t, rfl⟩ := ha.cons
        exact space_suffix hIU n (by simp only [List.cons_append, List.length_cons,
          List.length_append] at hn; omega) hb hb'
          (by simp only [List.cons_append, List.length_cons, List.length_append] at hN ⊢; omega)

theorem space_tail_nil {p : Profile} {k X : Chars} (hs : Space p k)
    (hn : NoItemStart p (k ++ X)) : k = [] := by
  cases hs with
  | nil => rfl
  | @cons _ a b ha _ => exact (hn a (b ++ X) ha (by simp)).elim

/-- Whitespace before two non-whitespace positions of the same input is the same. -/
theorem space_align {N : Nat} (hIU : IU N) {p : Profile} {s₁ s₂ X₁ X₂ : Chars}
    (h₁ : Space p s₁) (h₂ : Space p s₂) (n₁ : NoItemStart p X₁) (n₂ : NoItemStart p X₂)
    (h : s₁ ++ X₁ = s₂ ++ X₂) (hN : (s₁ ++ X₁).length < N) : s₁ = s₂ ∧ X₁ = X₂ := by
  rcases List.append_eq_append_iff.mp h with ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · have hk : Space p k := space_suffix hIU _ (Nat.lt_succ_self _) h₁ h₂
      (by simp only [List.length_append] at hN ⊢; omega)
    have : k = [] := space_tail_nil hk n₁
    subst this; simp
  · have hk : Space p k := space_suffix hIU _ (Nat.lt_succ_self _) h₂ h₁
      (by simp only [List.length_append] at hN ⊢; omega)
    have : k = [] := space_tail_nil hk n₂
    subst this; simp

/-! ## Balanced token lists -/

/-- Bracket depth. -/
def net : List Tok → Int
  | [] => 0
  | .lp :: l => net l + 1
  | .rp :: l => net l - 1
  | .atom _ :: l => net l
  | .reserved :: l => net l
  | .punct _ :: l => net l

theorem net_append (l₁ l₂ : List Tok) : net (l₁ ++ l₂) = net l₁ + net l₂ := by
  induction l₁ with
  | nil => simp [net]
  | cons t l ih => cases t <;> simp [net, ih] <;> omega

theorem Balanced.net_prefix {l : List Tok} (h : Balanced l) :
    net l = 0 ∧ ∀ l₁ l₂, l = l₁ ++ l₂ → 0 ≤ net l₁ := by
  induction h with
  | nil =>
    refine ⟨rfl, fun l₁ l₂ e => ?_⟩
    cases l₁ with
    | nil => simp [net]
    | cons _ _ => simp at e
  | @tok t ts hl hr _ ih =>
    have ht : ∀ l, net (t :: l) = net l := by
      intro l; cases t <;> simp_all [net]
    refine ⟨by rw [ht, ih.1], fun l₁ l₂ e => ?_⟩
    cases l₁ with
    | nil => simp [net]
    | cons u l₁ =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      rw [ht]; exact ih.2 _ _ e
  | @group a b _ _ iha ihb =>
    refine ⟨by simp [net, net_append, iha.1, ihb.1], fun l₁ l₂ e => ?_⟩
    cases l₁ with
    | nil => simp [net]
    | cons u l₁ =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      rcases List.append_eq_append_iff.mp e with ⟨k, rfl, hk⟩ | ⟨k, rfl, -⟩
      · cases k with
        | nil => simp [net, iha.1]
        | cons v k =>
          simp only [List.cons_append, List.cons.injEq] at hk
          obtain ⟨rfl, hk⟩ := hk
          have := ihb.2 k l₂ hk
          simp [net, net_append, iha.1]
          omega
      · have := iha.2 l₁ k rfl
        simp [net]
        omega

theorem Balanced.not_append_rp {l vs : List Tok} (h₁ : Balanced l)
    (h₂ : Balanced (l ++ .rp :: vs)) : False := by
  have := h₂.net_prefix.2 (l ++ [.rp]) vs (by simp)
  rw [net_append, h₁.net_prefix.1] at this
  simp [net] at this

/-! ## Lexing an extended input -/

/-- Lexing `x ++ ")" ++ m` (not at the top level) begins by lexing `x` and then `)`. -/
theorem lex_ext {N : Nat} (hIU : IU N) : ∀ (n : Nat) {p : Profile} {x y m : Chars}
    {ts us : List Tok}, x.length < n → y = x ++ ')' :: m → y.length < N →
    Lex p false x ts → Lex p false y us → ∃ vs, us = ts ++ .rp :: vs
  | 0, _, _, _, _, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, x, y, m, ts, us, hn, hy, hN, h₁, h₂ => by
    cases h₁ with
    | @done _ _ s hs =>
      cases h₂ with
      | @done _ _ s' hs' =>
        exfalso
        obtain ⟨h1, -⟩ := space_align hIU hs hs' noItemStart_rp noItemStart_nil
          (by rw [hy, List.append_nil]) (by rw [← hy]; exact hN)
        have := congrArg List.length (h1.trans hy)
        simp at this
      | @step _ _ s' c rest t us' hs' ht hf hl =>
        obtain ⟨rfl, h2⟩ := space_align hIU hs hs' noItemStart_rp (noItemStart_tok ht hf)
          (by rw [List.append_assoc] at hy; exact hy.symm) (by rw [← hy]; exact hN)
        obtain ⟨rfl, rfl⟩ := tok_rp ht hf h2.symm
        exact ⟨us', rfl⟩
    | @step _ _ s c rest t ts' hs ht hf hl =>
      have hf₀ := follow_append_rp (m := m) hf
      cases h₂ with
      | @done _ _ s' hs' =>
        exfalso
        obtain ⟨-, h2⟩ := space_align hIU hs hs' (noItemStart_tok ht hf₀) noItemStart_nil
          (by rw [hy]; simp) (by rw [hy] at hN; simpa using hN)
        exact tok_ne_nil ht hf (List.append_eq_nil_iff.mp h2).1
      | @step _ _ s' c' rest' t' us' hs' ht' hf' hl' =>
        obtain ⟨rfl, h2⟩ := space_align hIU hs hs' (noItemStart_tok ht hf₀)
          (noItemStart_tok ht' hf') (by simp only [List.append_assoc] at hy ⊢; exact hy.symm)
          (by rw [hy] at hN; simpa using hN)
        obtain ⟨rfl, rfl⟩ := tok1_unique ht hf₀ ht' hf' h2
        have h3 : rest' = rest ++ ')' :: m := (List.append_cancel_left h2).symm
        have hc := len_pos (tok_ne_nil ht hf)
        obtain ⟨vs, rfl⟩ := lex_ext hIU n
          (by simp only [List.length_append] at hn; omega) h3
          (by simp only [List.length_append] at hN ⊢; omega)
          hl hl'
        exact ⟨vs, rfl⟩

/-! ## Uniqueness of whitespace items -/

theorem annotId_unique {i₁ i₂ Y₁ Y₂ : Chars} (h₁ : AnnotId i₁) (h₂ : AnnotId i₂)
    (f₁ : ∀ c, Y₁.head? = some c → ¬ IsRunChar c ∧ c ≠ '"')
    (f₂ : ∀ c, Y₂.head? = some c → ¬ IsRunChar c ∧ c ≠ '"') (h : i₁ ++ Y₁ = i₂ ++ Y₂) :
    i₁ = i₂ := by
  rcases h₁ with ⟨ne₁, hc₁⟩ | ⟨n₁, bs₁, hs₁, -⟩ <;> rcases h₂ with ⟨ne₂, hc₂⟩ | ⟨n₂, bs₂, hs₂, -⟩
  · exact idRun_max hc₁ hc₂ (fun c hc hi => (f₁ c hc).1 hi.isRunChar)
      (fun c hc hi => (f₂ c hc).1 hi.isRunChar) h
  · obtain ⟨t, rfl⟩ := hs₂.head
    obtain ⟨y, t', rfl⟩ := List.exists_cons_of_ne_nil ne₁
    simp only [List.cons_append, List.cons.injEq] at h
    have hy := hc₁ y (by simp)
    rw [h.1] at hy
    exact absurd hy (by decide)
  · obtain ⟨t, rfl⟩ := hs₁.head
    obtain ⟨y, t', rfl⟩ := List.exists_cons_of_ne_nil ne₂
    simp only [List.cons_append, List.cons.injEq] at h
    have hy := hc₂ y (by simp)
    rw [← h.1] at hy
    exact absurd hy (by decide)
  · exact (StringLit.prefix hs₁ hs₂ h).1

theorem annot_follow {body r : Chars} (hf : ∀ c, body.head? = some c → ¬ IsRunChar c ∧ c ≠ '"') :
    ∀ c, (body ++ ')' :: r).head? = some c → ¬ IsRunChar c ∧ c ≠ '"' := by
  cases body with
  | nil =>
    intro c hc
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hc
    subst hc
    exact ⟨not_isRunChar_rp, by decide⟩
  | cons y t => simpa using hf

theorem annot_body {N : Nat} (hIU : IU N) {b₁ b₂ r₁ r₂ : Chars} {ts₁ ts₂ : List Tok}
    (hl₁ : Lex .core3 false b₁ ts₁) (hbal₁ : Balanced ts₁) (hl₂ : Lex .core3 false b₂ ts₂)
    (hbal₂ : Balanced ts₂) (h : b₁ ++ ')' :: r₁ = b₂ ++ ')' :: r₂)
    (hn : (b₁ ++ ')' :: r₁).length < N) : b₁ = b₂ := by
  rcases List.append_eq_append_iff.mp h with ⟨k, rfl, hk⟩ | ⟨k, rfl, hk⟩
  · cases k with
    | nil => simp
    | cons y k =>
      simp only [List.cons_append, List.cons.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      obtain ⟨vs, rfl⟩ := lex_ext hIU _ (Nat.lt_succ_self _) rfl
        (by simp only [List.length_append, List.length_cons] at hn ⊢; omega) hl₁ hl₂
      exact (Balanced.not_append_rp hbal₁ hbal₂).elim
  · cases k with
    | nil => simp
    | cons y k =>
      simp only [List.cons_append, List.cons.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      obtain ⟨vs, rfl⟩ := lex_ext hIU _ (Nat.lt_succ_self _) rfl
        (by simp only [List.length_append, List.length_cons] at hn ⊢; omega) hl₂ hl₁
      exact (Balanced.not_append_rp hbal₂ hbal₁).elim

theorem iu_succ {N : Nat} (hIU : IU N) : IU (N + 1) := by
  intro p a₁ b₁ a₂ b₂ hn h₁ h₂ h
  rcases h₁.view with ⟨x, rfl, hx⟩ | ⟨bd, nl, rfl, hb, hnl⟩ | ⟨t, rfl, ht⟩ |
      ⟨idc, bd, ts, rfl, rfl, hi, hf, hl, hbal⟩ <;>
    rcases h₂.view with ⟨x', rfl, hx'⟩ | ⟨bd', nl', rfl, hb', hnl'⟩ | ⟨t', rfl, ht'⟩ |
      ⟨idc', bd', ts', hp', rfl, hi', hf', hl', hbal'⟩ <;>
    simp only [List.cons_append, List.nil_append, List.append_assoc,
      List.cons.injEq] at h
  all_goals first
    | exact absurd h.1 (by decide)
    | exact absurd h.2.1 (by decide)
    | (rw [h.1] at hx; first | exact absurd hx not_space_semi | exact absurd hx not_space_lp)
    | (rw [← h.1] at hx'; first | exact absurd hx' not_space_semi | exact absurd hx' not_space_lp)
    | rw [h.1]
    | (obtain ⟨-, -, h⟩ := h
       obtain ⟨rfl, rfl, -⟩ := split_first (P := IsNewlineP p) hb hb' hnl hnl' h
       rfl)
    | rw [blockTail_prefix _ (Nat.lt_succ_self _) ht ht' h.2.2]
    | skip
  all_goals
    obtain ⟨-, -, h⟩ := h
    have e := annotId_unique hi hi' (annot_follow hf) (annot_follow hf') h
    subst e
    have h' := List.append_cancel_left h
    have e := annot_body hIU hl hbal hl' hbal' h'
      (by simp only [List.cons_append, List.append_assoc, List.length_append, List.length_cons,
        List.length_nil] at hn ⊢; omega)
    subst e
    rfl

theorem iu_all : ∀ N, IU N
  | 0 => fun _ _ _ _ _ hn => absurd hn (Nat.not_lt_zero _)
  | N + 1 => iu_succ (iu_all N)

/-! ## Functionality of the lexer -/

theorem lex_func : ∀ (n : Nat) {p : Profile} {top : Bool} {x y : Chars} {ts us : List Tok},
    x.length < n → x = y → Lex p top x ts → Lex p top y us → ts = us
  | 0, _, _, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, p, top, x, y, ts, us, hn, hxy, h₁, h₂ => by
    cases h₁ with
    | @done _ _ s hs =>
      cases h₂ with
      | done => rfl
      | doneEof => rfl
      | @step _ _ s' c rest t us' hs' ht hf hl =>
        exfalso
        have := (space_align (iu_all _) hs hs' noItemStart_nil (noItemStart_tok ht hf)
          (by rw [List.append_nil, hxy, List.append_assoc]) (Nat.lt_succ_self _)).2
        exact tok_ne_nil ht hf (List.append_eq_nil_iff.mp this.symm).1
    | @doneEof _ s body hs hb =>
      cases h₂ with
      | done => rfl
      | doneEof => rfl
      | @step _ _ s' c rest t us' hs' ht hf hl =>
        exfalso
        have := (space_align (iu_all _) hs hs' (noItemStart_eof hb) (noItemStart_tok ht hf)
          (by rw [hxy, List.append_assoc]) (Nat.lt_succ_self _)).2
        exact tok_not_semisemi ht hf this.symm
    | @step _ _ s c rest t ts' hs ht hf hl =>
      cases h₂ with
      | @done _ _ s' hs' =>
        exfalso
        have := (space_align (iu_all _) hs hs' (noItemStart_tok ht hf) noItemStart_nil
          (by rw [List.append_nil, ← hxy, List.append_assoc]) (Nat.lt_succ_self _)).2
        exact tok_ne_nil ht hf (List.append_eq_nil_iff.mp this).1
      | @doneEof _ s' body hs' hb =>
        exfalso
        have := (space_align (iu_all _) hs hs' (noItemStart_tok ht hf) (noItemStart_eof hb)
          (by rw [← hxy, List.append_assoc]) (Nat.lt_succ_self _)).2
        exact tok_not_semisemi ht hf this
      | @step _ _ s' c' rest' t' us' hs' ht' hf' hl' =>
        obtain ⟨rfl, h2⟩ := space_align (iu_all _) hs hs' (noItemStart_tok ht hf)
          (noItemStart_tok ht' hf') (by simp only [List.append_assoc] at hxy ⊢; exact hxy)
          (Nat.lt_succ_self _)
        obtain ⟨rfl, rfl⟩ := tok1_unique ht hf ht' hf' h2
        have hc := len_pos (tok_ne_nil ht hf)
        rw [lex_func n (by simp only [List.length_append] at hn; omega)
          (List.append_cancel_left h2) hl hl']

/-- Longest match makes tokenization unique. -/
theorem lex_functional {p : Profile} {top : Bool} {x : Chars} {ts us : List Tok}
    (h₁ : Lex p top x ts) (h₂ : Lex p top x us) : ts = us :=
  lex_func _ (Nat.lt_succ_self _) rfl h₁ h₂

end Silmaril.Formats.SExpEncoding.Wat
