module

public import Silmaril.Semantics.CPort.Formats.SExp.EncodingScheme.Defs

/-!
# Soundness of the existing Lisp parser for Scheme conventions

The existing reader `Formats.SExpParser.parseLexemes?` works on a byte cursor
(`String.Pos.Raw`) with explicit fuel.  This file relates it to the Scheme
relation `Scheme.sexpScheme` (`EncodingScheme.lean`) on the *safe fragment*
recognized by the scanner `lispSafe`, without modifying the parser:

* `At inp r` says that the cursor `inp` stands before the characters `r`;
  `current` and `next` are then `List.head?` and `List.tail`;
* the safety scanner state is threaded through the parse (`SafeFrom`);
* `Seg pre toks after` is a Scheme token segment `pre` followed by `after`;
* `ws`, `quoted`, `bare` and the mutually recursive `expr`/`list` are each
  shown to consume a segment that the Scheme lexer tokenizes the same way.

The main result is `parseDoc_sound_of_safe`.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding

open Silmaril

/-- The existing parser as a (single-datum) document decoder. -/
def parseDoc? (s : String) : Option SExp :=
  (fun x => doc [x.map Lexeme.toAtom]) <$> SExpParser.parseLexemes? s

/-- Scanner state for `lispSafe`. -/
inductive SafeState where
  /-- Outside strings and comments; the flag records that the previous character
  was a delimiter, the start of the text, or the end of a comment. -/
  | outside (atBoundary : Bool)
  | inString
  /-- Just closed a string: the next character must be a delimiter or the end. -/
  | closed
  /-- Inside a `;` line comment (both readers skip it up to `\n`). -/
  | comment
  deriving DecidableEq

/-- One step of the safety scanner (`none` = unsafe). -/
def safeStep : SafeState → Char → Option SafeState
  | .inString, '"' => some .closed
  | .inString, c => if c = '\\' ∨ c = '\r' then none else some .inString
  -- Scheme ends a comment at CR as well, the existing parser does not.
  | .comment, c => if c = '\n' then some (.outside true) else if c = '\r' then none
      else some .comment
  | .closed, c =>
      if c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '(' ∨ c = ')' then some (.outside true)
      else if c = ';' then some .comment else none
  | .outside b, '"' => if b then some .inString else none
  | .outside _, c =>
      if c ∈ ['#', '|', '\'', '`', ',', '\\', '\r'] then none
      else if c = ';' then some .comment
      else if c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '(' ∨ c = ')' then some (.outside true)
      else some (.outside false)

/-- The safety scanner over a whole text. -/
def lispSafe (cs : Chars) : Bool :=
  match cs.foldlM safeStep (.outside true) with
  | some (.outside _) | some .closed | some .comment => true
  | _ => false

/-- Does the S-expression contain the symbol `.`?  The existing parser reads a
lone `.` as a symbol where it is not a dotted-pair marker (at the top level,
and as the datum after a marker), whereas for Scheme it is always the `dot`
token. -/
def hasDotSym : SExp → Bool
  | .atom a => a == .sym "."
  | .nil => false
  | .cons a b => hasDotSym a || hasDotSym b

namespace ParserSound

open SExpParser

/-! ## Cursors -/

/-- UTF-8 byte length of a character list. -/
def blen : Chars → Nat
  | [] => 0
  | c :: cs => c.utf8Size + blen cs

@[simp] theorem blen_append (a b : Chars) : blen (a ++ b) = blen a + blen b := by
  induction a with
  | nil => simp [blen]
  | cons c a ih => simp [blen, ih]; omega

theorem getAux?_at (l r : Chars) (i : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux? (l ++ r) i ⟨i.byteIdx + blen l⟩ = r.head? := by
  induction l generalizing i with
  | nil =>
    cases r with
    | nil => rfl
    | cons c r => simp [String.Pos.Raw.utf8GetAux?, blen]
  | cons c l ih =>
    have hpos := c.utf8Size_pos
    have hne : i ≠ ⟨i.byteIdx + blen (c :: l)⟩ := by
      intro h
      have := congrArg String.Pos.Raw.byteIdx h
      simp [blen] at this; omega
    simp only [List.cons_append, String.Pos.Raw.utf8GetAux?, hne, ite_false]
    have := ih (i + c)
    have he : (⟨(i + c).byteIdx + blen l⟩ : String.Pos.Raw) = ⟨i.byteIdx + blen (c :: l)⟩ := by
      simp only [blen, String.Pos.Raw.ext_iff]
      show i.byteIdx + c.utf8Size + blen l = _
      omega
    rw [he] at this
    exact this

theorem getAux_at (l r : Chars) (c : Char) (i : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (l ++ c :: r) i ⟨i.byteIdx + blen l⟩ = c := by
  induction l generalizing i with
  | nil => simp [String.Pos.Raw.utf8GetAux, blen]
  | cons d l ih =>
    have hpos := d.utf8Size_pos
    have hne : i ≠ ⟨i.byteIdx + blen (d :: l)⟩ := by
      intro h
      have := congrArg String.Pos.Raw.byteIdx h
      simp [blen] at this; omega
    simp only [List.cons_append, String.Pos.Raw.utf8GetAux, hne, ite_false]
    have := ih (i + d)
    have he : (⟨(i + d).byteIdx + blen l⟩ : String.Pos.Raw) = ⟨i.byteIdx + blen (d :: l)⟩ := by
      simp only [blen, String.Pos.Raw.ext_iff]
      show i.byteIdx + d.utf8Size + blen l = _
      omega
    rw [he] at this
    exact this

/-- The cursor `inp` stands before the characters `r` (a suffix of its source). -/
def At (inp : Input) (r : Chars) : Prop :=
  ∃ l, inp.source.toList = l ++ r ∧ inp.pos.byteIdx = blen l

theorem At.current {inp : Input} {r : Chars} (h : At inp r) : inp.current = r.head? := by
  obtain ⟨l, hs, hp⟩ := h
  have := getAux?_at l r 0
  simp only [String.Pos.Raw.byteIdx_zero, Nat.zero_add] at this
  simp only [Input.current, String.Pos.Raw.get?, hs]
  rw [← this]; congr 1; exact String.Pos.Raw.ext hp

theorem At.next {inp : Input} {c : Char} {r : Chars} (h : At inp (c :: r)) : At inp.next r := by
  obtain ⟨l, hs, hp⟩ := h
  refine ⟨l ++ [c], by simp [Input.next, hs], ?_⟩
  have := getAux_at l r c 0
  simp only [String.Pos.Raw.byteIdx_zero, Nat.zero_add] at this
  have hpos : inp.pos = ⟨blen l⟩ := String.Pos.Raw.ext hp
  simp only [Input.next, String.Pos.Raw.next, String.Pos.Raw.get, hs, hpos, this]
  show blen l + c.utf8Size = _
  simp [blen]

theorem At.length {inp : Input} {r : Chars} (h : At inp r) : r.length ≤ inp.source.length := by
  obtain ⟨l, hs, -⟩ := h
  rw [← String.length_toList, hs]; simp

theorem At.start (s : String) : At ⟨s, 0⟩ s.toList := ⟨[], by simp, rfl⟩

/-! ## The safety scanner along the text -/

/-- Accepting final states. -/
def accOk : Option SafeState → Bool
  | some (.outside _) | some .closed | some .comment => true
  | _ => false

/-- The rest `r` of the text is accepted from state `st`. -/
def SafeFrom (st : SafeState) (r : Chars) : Prop := accOk (r.foldlM safeStep st) = true

theorem lispSafe_iff (cs : Chars) : lispSafe cs = true ↔ SafeFrom (.outside true) cs := by
  unfold lispSafe SafeFrom accOk
  rfl

theorem SafeFrom.cons {st : SafeState} {c : Char} {r : Chars} (h : SafeFrom st (c :: r)) :
    ∃ st', safeStep st c = some st' ∧ SafeFrom st' r := by
  unfold SafeFrom at h
  simp only [List.foldlM_cons] at h
  cases hs : safeStep st c with
  | none => simp [hs, accOk] at h
  | some st' => exact ⟨st', rfl, by simpa [hs, SafeFrom] using h⟩

theorem SafeFrom.step {st st' : SafeState} {c : Char} {r : Chars} (h : SafeFrom st (c :: r))
    (hs : safeStep st c = some st') : SafeFrom st' r := by
  obtain ⟨st'', h1, h2⟩ := h.cons
  rw [hs] at h1; cases h1; exact h2

theorem SafeFrom.append {st : SafeState} {a b : Chars} (h : SafeFrom st (a ++ b)) :
    ∃ st', a.foldlM safeStep st = some st' ∧ SafeFrom st' b := by
  induction a generalizing st with
  | nil => exact ⟨st, rfl, h⟩
  | cons c a ih =>
    obtain ⟨st', h1, h2⟩ := SafeFrom.cons h
    obtain ⟨st'', h3, h4⟩ := ih h2
    exact ⟨st'', by simp [h1, h3], h4⟩

theorem SafeFrom.not_inString_nil : ¬ SafeFrom .inString [] := by
  simp [SafeFrom, accOk]

/-- Scanner states at token boundaries. -/
def Out (st : SafeState) : Prop := (∃ b, st = .outside b) ∨ st = .closed

theorem Out.semicolon {st : SafeState} (h : Out st) : safeStep st ';' = some .comment := by
  rcases h with ⟨b, rfl⟩ | rfl
  · cases b <;> decide
  · decide

/-! ## Whitespace and comments -/

theorem ws_comment (r : Chars) : ∀ (fuel : Nat) (inp : Input), At inp r → r.length < fuel →
    SafeFrom .comment r →
    (∃ body r2 fuel' inp2, r = body ++ '\n' :: r2 ∧ Scheme.NoLineEnd body ∧ r2.length < fuel' ∧
      wsFuel fuel true inp = wsFuel fuel' false inp2 ∧ At inp2 r2 ∧
      SafeFrom (.outside true) r2) ∨
    (Scheme.NoLineEnd r ∧ At (wsFuel fuel true inp) []) := by
  induction r with
  | nil =>
    intro fuel inp h hl _
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
    right
    refine ⟨by simp [Scheme.NoLineEnd], ?_⟩
    simp only [wsFuel, h.current, List.head?]
    exact h
  | cons c r ih =>
    intro fuel inp h hl hs
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
    simp only [wsFuel, h.current, List.head?, ite_true]
    by_cases hc : c = '\n'
    · subst hc
      left
      exact ⟨[], r, f, inp.next, rfl, by simp [Scheme.NoLineEnd], by simp at hl; omega,
        by simp, h.next, hs.step (by decide)⟩
    · have hr : c ≠ '\r' := by
        rintro rfl
        obtain ⟨st', h1, -⟩ := hs.cons
        simp [safeStep] at h1
      have hs' : SafeFrom .comment r := hs.step (by simp [safeStep, hc, hr])
      have hcd : decide (c ≠ '\n') = true := by simp [hc]
      rw [hcd]
      rcases ih f inp.next h.next (by simp at hl; omega) hs' with
        ⟨body, r2, fuel', inp2, rfl, hb, hl2, he, ha, hs2⟩ | ⟨hb, ha⟩
      · left
        refine ⟨c :: body, r2, fuel', inp2, rfl, ?_, hl2, he, ha, hs2⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨hc, hr⟩
        · exact hb x hx
      · right
        refine ⟨?_, ha⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨hc, hr⟩
        · exact hb x hx

/-- The trailing part of a text: whitespace, possibly ending in a comment at the
end of the input. -/
def Trailing (pre : Chars) : Prop :=
  ∃ s body, pre = s ++ ';' :: body ∧ Scheme.Space s ∧ Scheme.NoLineEnd body

theorem space_append {a b : Chars} (ha : Scheme.Space a) (hb : Scheme.Space b) :
    Scheme.Space (a ++ b) := by
  induction ha with
  | nil => exact hb
  | cons hi _ ih => rw [List.append_assoc]; exact Scheme.Space.cons hi ih

theorem ws_main (n : Nat) : ∀ (r : Chars), r.length = n → ∀ (fuel : Nat) (inp : Input)
    (st : SafeState), At inp r → r.length < fuel → SafeFrom st r → Out st →
    ∃ pre r', r = pre ++ r' ∧ At (wsFuel fuel false inp) r' ∧
      ((Scheme.Space pre ∧ ∃ st', SafeFrom st' r' ∧ Out st') ∨ (r' = [] ∧ Trailing pre)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r hn fuel inp st h hl hs hout
  obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  cases r with
  | nil =>
    refine ⟨[], [], rfl, ?_, Or.inl ⟨Scheme.Space.nil, st, hs, hout⟩⟩
    simp only [wsFuel, h.current, List.head?]
    exact h
  | cons c r =>
    simp only [wsFuel, h.current, List.head?, Bool.false_eq_true, ite_false]
    by_cases hc : c = ';'
    · subst hc
      simp only [ite_true]
      have hs1 : SafeFrom .comment r := hs.step hout.semicolon
      rcases ws_comment r f inp.next h.next (by simp at hl; omega) hs1 with
        ⟨body, r2, fuel', inp2, rfl, hb, hl2, he, ha, hs2⟩ | ⟨hb, ha⟩
      · rw [he]
        obtain ⟨pre2, r', rfl, ha', hd⟩ :=
          ih r2.length (by subst hn; simp; omega) r2 rfl fuel' inp2 _ ha hl2 hs2
            (Or.inl ⟨true, rfl⟩)
        refine ⟨';' :: (body ++ ['\n']) ++ pre2, r', by simp, ha', ?_⟩
        have hi : Scheme.SpaceItem (';' :: (body ++ ['\n'])) :=
          Scheme.SpaceItem.line hb (Or.inl rfl)
        rcases hd with ⟨hsp, hrest⟩ | ⟨rfl, s, body2, rfl, hsp, hb2⟩
        · exact Or.inl ⟨Scheme.Space.cons hi hsp, hrest⟩
        · exact Or.inr ⟨rfl, ';' :: (body ++ ['\n']) ++ s, body2, by simp,
            Scheme.Space.cons hi hsp, hb2⟩
      · exact ⟨';' :: r, [], by simp, ha, Or.inr ⟨rfl, [], r, rfl, Scheme.Space.nil, hb⟩⟩
    · simp only [hc, ite_false]
      by_cases hsp : space c = true
      · simp only [hsp, ite_true]
        have hws : Scheme.IsWs c := by
          simp [space] at hsp; unfold Scheme.IsWs; tauto
        have hcr : c ≠ '\r' := by
          rintro rfl
          obtain ⟨st', h1, -⟩ := hs.cons
          rcases hout with ⟨b, rfl⟩ | rfl <;> simp [safeStep] at h1
        have hs1 : SafeFrom (.outside true) r := by
          refine hs.step ?_
          rcases hws with rfl | rfl | rfl | rfl
          all_goals first
            | exact absurd rfl hcr
            | (rcases hout with ⟨b, rfl⟩ | rfl <;> [cases b <;> decide; decide])
        obtain ⟨pre2, r', rfl, ha', hd⟩ :=
          ih r.length (by subst hn; simp) r rfl f inp.next _ h.next (by simp at hl; omega) hs1
            (Or.inl ⟨true, rfl⟩)
        refine ⟨c :: pre2, r', by simp, ha', ?_⟩
        have hi : Scheme.SpaceItem [c] := Scheme.SpaceItem.ws hws
        rcases hd with ⟨hsp', hrest⟩ | ⟨rfl, s, body2, rfl, hsp', hb2⟩
        · exact Or.inl ⟨Scheme.Space.cons (a := [c]) hi hsp', hrest⟩
        · exact Or.inr ⟨rfl, c :: s, body2, by simp, Scheme.Space.cons (a := [c]) hi hsp', hb2⟩
      · simp only [hsp, Bool.false_eq_true, ite_false]
        exact ⟨[], c :: r, rfl, h, Or.inl ⟨Scheme.Space.nil, st, hs, hout⟩⟩

theorem ws_spec {inp : Input} {r : Chars} {st : SafeState} (h : At inp r) (hs : SafeFrom st r)
    (hout : Out st) :
    ∃ pre r', r = pre ++ r' ∧ At (ws inp) r' ∧
      ((Scheme.Space pre ∧ ∃ st', SafeFrom st' r' ∧ Out st') ∨ (r' = [] ∧ Trailing pre)) :=
  ws_main _ r rfl _ inp st h (by have := h.length; omega) hs hout

/-! ## Strings and bare tokens -/

theorem quoted_spec (fuel : Nat) : ∀ (inp : Input) (r tok : Chars) (out : Input),
    quoted fuel inp = some (tok, out) → At inp r → SafeFrom .inString r →
    ∃ r', r = tok ++ '"' :: r' ∧ At out r' ∧ (∀ c ∈ tok, c ≠ '"' ∧ c ≠ '\\') ∧
      SafeFrom .closed r' := by
  induction fuel with
  | zero => intro inp r tok out hq; simp [quoted] at hq
  | succ f ih =>
    intro inp r tok out hq h hs
    simp only [quoted, h.current] at hq
    cases r with
    | nil => simp at hq
    | cons c r1 =>
      simp only [List.head?] at hq
      split at hq
      · simp at hq
      · rename_i heq
        simp only [Option.some.injEq] at heq hq; subst heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq.symm
        exact ⟨r1, rfl, h.next, by simp, hs.step (by decide)⟩
      · rename_i heq
        simp only [Option.some.injEq] at heq; subst heq
        obtain ⟨st', h1, -⟩ := hs.cons
        simp [safeStep] at h1
      · rename_i c' h1 h2 heq
        simp only [Option.some.injEq] at heq; subst heq
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hq
        obtain ⟨⟨tail, rest⟩, hq1, hq2⟩ := hq
        simp only [Option.some.injEq, Prod.mk.injEq] at hq2
        obtain ⟨rfl, rfl⟩ := hq2
        obtain ⟨st', hst, hs'⟩ := hs.cons
        have hcr : c ≠ '\\' ∧ c ≠ '\r' ∧ st' = .inString := by
          rw [safeStep.eq_2 _ h1] at hst
          by_cases hb : c = '\\' ∨ c = '\r'
          · simp [hb] at hst
          · simp only [hb, ite_false, Option.some.injEq] at hst
            exact ⟨fun e => hb (Or.inl e), fun e => hb (Or.inr e), hst.symm⟩
        obtain ⟨-, -, rfl⟩ := hcr
        obtain ⟨r', rfl, ha, hc, hs2⟩ := ih _ _ _ _ hq1 h.next hs'
        refine ⟨r', rfl, ha, ?_, hs2⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨h1, h2⟩
        · exact hc x hx

theorem bare_go_spec (r : Chars) : ∀ (fuel : Nat) (inp : Input), At inp r → r.length < fuel →
    ∃ tok out r', bare.go fuel inp = (tok, out) ∧ r = tok ++ r' ∧ At out r' ∧
      (∀ c ∈ tok, delimiter c = false) ∧ (∀ c, r'.head? = some c → delimiter c = true) := by
  induction r with
  | nil =>
    intro fuel inp h hl
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
    exact ⟨[], inp, [], by simp [bare.go, h.current], rfl, h, by simp, by simp⟩
  | cons c r ih =>
    intro fuel inp h hl
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
    by_cases hd : delimiter c = true
    · exact ⟨[], inp, c :: r, by simp [bare.go, h.current, hd], rfl, h, by simp,
        by simpa using hd⟩
    · obtain ⟨tok, out, r', he, rfl, ha, hn, hh⟩ := ih f inp.next h.next (by simp at hl; omega)
      refine ⟨c :: tok, out, r', ?_, rfl, ha, ?_, hh⟩
      · simp [bare.go, h.current, hd, he]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using hd
        · exact hn x hx

theorem bare_spec {inp : Input} {r : Chars} (h : At inp r) :
    ∃ tok out r', bare inp = (tok, out) ∧ r = tok ++ r' ∧ At out r' ∧
      (∀ c ∈ tok, delimiter c = false) ∧ (∀ c, r'.head? = some c → delimiter c = true) :=
  bare_go_spec r _ inp h (by have := h.length; omega)

/-- Characters that may not occur in safe bare tokens. -/
def badBare : List Char := ['#', '|', '\'', '`', ',', '\\', '\r', '"']

theorem not_delimiter {c : Char} (h : delimiter c = false) :
    c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ ';' := by
  simp only [delimiter, space, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  tauto

theorem safe_bare_step {st st' : SafeState} {c : Char} (hout : Out st)
    (hs : safeStep st c = some st') (hd : delimiter c = false)
    (hq : c ≠ '"' ∨ st = .outside false) :
    c ∉ badBare ∧ st' = .outside false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := not_delimiter hd
  rcases hout with ⟨b, rfl⟩ | rfl
  · by_cases hc : c = '"'
    · subst hc
      rcases hq with hq | hq
      · exact absurd rfl hq
      · cases hq; simp [safeStep] at hs
    · have hs' : (if c ∈ ['#', '|', '\'', '`', ',', '\\', '\r'] then none
          else if c = ';' then some SafeState.comment
          else if c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '(' ∨ c = ')' then some (.outside true)
          else some (.outside false)) = some st' := by
        rw [← hs, safeStep.eq_6 _ _ hc]
      by_cases hm : c ∈ ['#', '|', '\'', '`', ',', '\\', '\r']
      · simp [hm] at hs'
      · simp only [hm, h7, h1, h2, h3, h5, h6, ite_false, or_self, Option.some.injEq] at hs'
        refine ⟨?_, hs'.symm⟩
        simp only [badBare, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        tauto
  · exfalso
    rw [safeStep.eq_4] at hs
    simp [h1, h2, h3, h5, h6, h7] at hs

theorem safe_bare {tok r : Chars} : ∀ {st : SafeState}, Out st → SafeFrom st (tok ++ r) →
    (∀ c, tok.head? = some c → c ≠ '"' ∨ st = .outside false) →
    (∀ c ∈ tok, delimiter c = false) → tok ≠ [] →
    (∀ c ∈ tok, c ∉ badBare) ∧ SafeFrom (.outside false) r := by
  induction tok with
  | nil => intro _ _ _ _ _ h; exact absurd rfl h
  | cons c tok ih =>
    intro st hout hs hq hd _
    obtain ⟨st1, h1, hs1⟩ := SafeFrom.cons hs
    obtain ⟨hc, rfl⟩ := safe_bare_step hout h1 (hd c (by simp)) (hq c rfl)
    by_cases ht : tok = []
    · subst ht
      exact ⟨by simpa using hc, hs1⟩
    · obtain ⟨hall, hr⟩ := ih (Or.inl ⟨false, rfl⟩) hs1 (fun _ _ => Or.inr rfl)
        (fun x hx => hd x (List.mem_cons_of_mem _ hx)) ht
      refine ⟨?_, hr⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hc
      · exact hall x hx

theorem strBody_of : ∀ (body : Chars), (∀ c ∈ body, c ≠ '"' ∧ c ≠ '\\') →
    Scheme.StrBody body body
  | [], _ => Scheme.StrBody.nil
  | c :: body, h => by
    have hc := h c (by simp)
    exact Scheme.StrBody.char hc.1 hc.2
      (strBody_of body fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem delimiter_isDelim {c : Char} (h : delimiter c = true) : Scheme.IsDelim c := by
  simp only [delimiter, space, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold Scheme.IsDelim Scheme.IsWs
  tauto

theorem bare_tok1 {tok r : Chars} (hne : tok ≠ []) (hbad : ∀ c ∈ tok, c ∉ badBare)
    (hdl : ∀ c ∈ tok, delimiter c = false) (hdot : tok ≠ ['.'])
    (hn : ∀ c, r.head? = some c → delimiter c = true) :
    Scheme.Tok1 tok (.atom (.sym (String.ofList tok))) r := by
  have hhash : '#' ∉ tok := fun h => hbad _ h (by simp [badBare])
  have hhead : ∀ c, tok.head? = some c → c ∈ tok := fun c hc => List.mem_of_head? hc
  refine Or.inr ⟨Or.inl ⟨hne, ?_, hdot, ?_, ?_, ?_⟩, rfl, fun c hc => delimiter_isDelim (hn c hc),
    fun h => absurd (hhead _ h) hhash⟩
  · intro c hc hd
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := not_delimiter (hdl c hc)
    have hb := hbad c hc
    simp only [badBare, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    unfold Scheme.IsDelim Scheme.IsWs at hd
    tauto
  · intro c hc
    have hb := hbad c (hhead c hc)
    simp only [badBare, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    exact ⟨hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1⟩
  · intro h; exact absurd (hhead _ h) hhash
  · intro h
    exact hhash (List.mem_of_mem_take (i := 2) (by rw [h]; simp))

/-! ## Token segments -/

/-- `pre` is a Scheme token segment with tokens `toks`, followed by the text `after`
(which the follow conditions of the tokens may inspect). -/
inductive Seg (after : Chars) : Chars → List Scheme.Tok → Prop where
  | nil {s : Chars} : Scheme.Space s → Seg after s []
  | step {s c rest : Chars} {t : Scheme.Tok} {ts : List Scheme.Tok} :
      Scheme.Space s → Scheme.Tok1 c t (rest ++ after) → Seg after rest ts →
      Seg after (s ++ c ++ rest) (t :: ts)

theorem Seg.space_prefix {after s b : Chars} {ts : List Scheme.Tok} (hs : Scheme.Space s)
    (h : Seg after b ts) : Seg after (s ++ b) ts := by
  cases h with
  | nil hs' => exact Seg.nil (space_append hs hs')
  | @step s' c rest t ts hs' ht hr =>
    rw [show s ++ (s' ++ c ++ rest) = (s ++ s') ++ c ++ rest by simp]
    exact Seg.step (space_append hs hs') ht hr

theorem Seg.append {after a b : Chars} {ts₁ ts₂ : List Scheme.Tok} (h₁ : Seg (b ++ after) a ts₁)
    (h₂ : Seg after b ts₂) : Seg after (a ++ b) (ts₁ ++ ts₂) := by
  induction h₁ with
  | nil hs => exact Seg.space_prefix hs h₂
  | @step s c rest t ts hs ht _ ih =>
    rw [show s ++ c ++ rest ++ b = s ++ c ++ (rest ++ b) by simp]
    exact Seg.step hs (by simpa using ht) ih

theorem Seg.tok {after s c : Chars} {t : Scheme.Tok} (hs : Scheme.Space s)
    (ht : Scheme.Tok1 c t after) : Seg after (s ++ c) [t] := by
  have := Seg.step (rest := []) hs (by simpa using ht) (Seg.nil (after := after) Scheme.Space.nil)
  simpa using this

theorem Seg.lex {b a : Chars} {ts : List Scheme.Tok} (h : Seg b a ts)
    (hb : Scheme.Space b ∨ Trailing b) : Scheme.Lex (a ++ b) ts := by
  induction h with
  | nil hs =>
    rcases hb with hb | ⟨s', body, rfl, hs', hn⟩
    · exact Scheme.Lex.done (space_append hs hb)
    · rw [← List.append_assoc]; exact Scheme.Lex.doneEof (space_append hs hs') hn
  | @step s c rest t ts hs ht _ ih =>
    rw [show s ++ c ++ rest ++ b = s ++ c ++ (rest ++ b) by simp]
    exact Scheme.Lex.step hs ht ih

/-! ## Results as Scheme data -/

/-- Atoms of the parser's results. -/
abbrev M (v : SExp2 Lexeme) : SExp := v.map Lexeme.toAtom

theorem M_foldr (l : List (SExp2 Lexeme)) (T : SExp2 Lexeme) :
    M (l.foldr .cons T) = (l.map M).foldr .cons (M T) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldr_cons, List.map_cons]; rw [← ih]; rfl

theorem M_foldr_nil (l : List (SExp2 Lexeme)) : M (l.foldr .cons .nil) = listOf (l.map M) := by
  rw [M_foldr]; rfl

theorem hasDotSym_foldr (l : List SExp) (T : SExp) :
    hasDotSym (l.foldr .cons T) = false ↔ (∀ x ∈ l, hasDotSym x = false) ∧ hasDotSym T = false := by
  induction l with
  | nil => simp
  | cons x l ih => simp [hasDotSym, ih, and_assoc]

/-! ## `expr` and `list` -/

/-- What `expr fuel` does. -/
def ExprSpec (fuel : Nat) : Prop :=
  ∀ (inp : Input) (r : Chars) (st : SafeState) (v : SExp2 Lexeme) (out : Input),
    expr fuel inp = some (v, out) → At inp r → SafeFrom st r → Out st →
    ∃ pre r' st', r = pre ++ r' ∧ At out r' ∧ SafeFrom st' r' ∧ Out st' ∧
      (hasDotSym (M v) = false → ∃ toks, Seg r' pre toks ∧ Scheme.Datum toks (M v))

/-- The shape of the tokens read by `list` after the opening parenthesis. -/
def ListShape (acc : List (SExp2 Lexeme)) (res : SExp2 Lexeme) (toks : List Scheme.Tok) : Prop :=
  ∃ items ts, Scheme.Data ts (items.map M) ∧
    ((toks = ts ++ [.rp] ∧ res = (acc ++ items).foldr .cons .nil) ∨
      (∃ d tail, acc ++ items ≠ [] ∧ toks = ts ++ .dot :: (d ++ [.rp]) ∧
        Scheme.Datum d (M tail) ∧ res = (acc ++ items).foldr .cons tail))

/-- What `list fuel acc` does. -/
def ListSpec (fuel : Nat) : Prop :=
  ∀ (acc : List (SExp2 Lexeme)) (inp : Input) (r : Chars) (st : SafeState)
    (res : SExp2 Lexeme) (out : Input),
    list fuel acc inp = some (res, out) → At inp r → SafeFrom st r → Out st →
    ∃ pre r' st', r = pre ++ r' ∧ At out r' ∧ SafeFrom st' r' ∧ Out st' ∧
      (hasDotSym (M res) = false → ∃ toks, Seg r' pre toks ∧ ListShape acc res toks)

theorem Out.paren {st : SafeState} (h : Out st) {c : Char} (hc : c = '(' ∨ c = ')') :
    safeStep st c = some (.outside true) := by
  rcases hc with rfl | rfl <;> rcases h with ⟨b, rfl⟩ | rfl <;> (try cases b) <;> decide

theorem expr_step {f : Nat} (ihL : ListSpec f) : ExprSpec (f + 1) := by
  intro inp r st v out he h hs hout
  obtain ⟨pre0, r0, rfl, h0, hw⟩ := ws_spec h hs hout
  simp only [expr] at he
  rw [h0.current] at he
  rcases hw with ⟨hsp, st0, hs0, hout0⟩ | ⟨rfl, -⟩
  swap
  · simp at he
  cases r0 with
  | nil => simp at he
  | cons c r1 =>
  simp only [List.head?] at he
  split at he
  · simp at he
  · simp at he
  · -- a list
    rename_i heq
    simp only [Option.some.injEq] at heq; subst heq
    have hs1 : SafeFrom (.outside true) r1 := hs0.step (hout0.paren (Or.inl rfl))
    obtain ⟨pre1, r', st', rfl, ha, hs', hout', ht⟩ :=
      ihL [] _ r1 _ v out he h0.next hs1 (Or.inl ⟨true, rfl⟩)
    refine ⟨pre0 ++ ['('] ++ pre1, r', st', by simp, ha, hs', hout', ?_⟩
    intro hd
    obtain ⟨toks, hseg, items, ts, hdata, hshape⟩ := ht hd
    refine ⟨.lp :: toks, Seg.step hsp rfl hseg, ?_⟩
    rcases hshape with ⟨rfl, rfl⟩ | ⟨d, tail, hne, rfl, hdd, rfl⟩
    · have := Scheme.Datum.list (s := []) hdata Scheme.Skip.nil
      rw [List.nil_append, M_foldr_nil]; simpa using this
    · have := Scheme.Datum.dotted (s₁ := []) (s₂ := []) hdata (by simpa using hne)
        Scheme.Skip.nil hdd Scheme.Skip.nil
      rw [List.nil_append, M_foldr]; simpa using this
  · -- a string
    rename_i heq
    simp only [Option.some.injEq] at heq; subst heq
    obtain ⟨st1, h1, hs1⟩ := hs0.cons
    have hst1 : st1 = .inString := by
      rcases hout0 with ⟨b, rfl⟩ | rfl
      · cases b <;> simp [safeStep] at h1; exact h1.symm
      · simp [safeStep] at h1
    subst hst1
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨tok, rest⟩, hq, he'⟩ := he
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    obtain ⟨r', rfl, ha, hc, hs2⟩ := quoted_spec f _ r1 tok rest hq h0.next hs1
    refine ⟨pre0 ++ ('"' :: (tok ++ ['"'])), r', .closed, by simp, ha, hs2, Or.inr rfl,
      fun _ => ⟨[.atom (.str (Unicode.utf8 (String.ofList tok)))], Seg.tok hsp ?_,
        Scheme.Datum.atom _⟩⟩
    exact ⟨String.ofList tok, ⟨tok, rfl, by rw [String.toList_ofList]; exact strBody_of tok hc⟩,
      rfl⟩
  · -- a bare token
    rename_i c' hc1 hc2 hc3 heq
    simp only [Option.some.injEq] at heq; subst heq
    obtain ⟨tok, out1, r', hb, hr, ha, hdl, hn⟩ := bare_spec h0
    rw [hb] at he
    cases tok with
    | nil => simp at he
    | cons c0 tok' =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.some.injEq,
      Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.cons_append, List.cons.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨hbad, hs'⟩ := safe_bare (tok := c :: tok') hout0 hs0
      (fun x hx => by simp at hx; subst hx; exact Or.inl hc3) hdl (by simp)
    refine ⟨pre0 ++ (c :: tok'), r', .outside false, by simp, ha, hs', Or.inl ⟨false, rfl⟩, ?_⟩
    intro hd
    have hdot : c :: tok' ≠ ['.'] := by
      rintro h
      rw [h] at hd
      revert hd; decide
    exact ⟨_, Seg.tok hsp (bare_tok1 (by simp) hbad hdl hdot hn), Scheme.Datum.atom _⟩

theorem list_generic {f : Nat} {acc : List (SExp2 Lexeme)} {inp : Input} {pre0 r0 : Chars}
    {st0 : SafeState} {head res : SExp2 Lexeme} {rest out : Input}
    (ihE : ExprSpec f) (ihL : ListSpec f) (hsp : Scheme.Space pre0) (h0 : At inp r0)
    (hs0 : SafeFrom st0 r0) (hout0 : Out st0) (he : expr f inp = some (head, rest))
    (hl : list f (acc ++ [head]) rest = some (res, out)) :
    ∃ pre r' st', pre0 ++ r0 = pre ++ r' ∧ At out r' ∧ SafeFrom st' r' ∧ Out st' ∧
      (hasDotSym (M res) = false → ∃ toks, Seg r' pre toks ∧ ListShape acc res toks) := by
  obtain ⟨pre_e, r_e, st_e, rfl, ha_e, hs_e, hout_e, hte⟩ := ihE _ _ _ _ _ he h0 hs0 hout0
  obtain ⟨pre_l, r', st', rfl, ha, hs', hout', htl⟩ := ihL _ _ _ _ _ _ hl ha_e hs_e hout_e
  refine ⟨pre0 ++ pre_e ++ pre_l, r', st', by simp, ha, hs', hout', ?_⟩
  intro hd
  obtain ⟨toks_l, hseg_l, items, ts, hdata, hshape⟩ := htl hd
  have hhead : hasDotSym (M head) = false := by
    rcases hshape with ⟨-, rfl⟩ | ⟨d, tail, -, -, -, rfl⟩
    all_goals
      rw [M_foldr] at hd
      exact ((hasDotSym_foldr _ _).1 hd).1 _ (by simp)
  obtain ⟨toks_e, hseg_e, hdat_e⟩ := hte hhead
  refine ⟨toks_e ++ toks_l, ?_, head :: items, toks_e ++ ts, ?_, ?_⟩
  · rw [List.append_assoc]; exact Seg.space_prefix hsp (Seg.append hseg_e hseg_l)
  · have := Scheme.Data.cons (s := []) Scheme.Skip.nil hdat_e hdata
    simpa using this
  · rcases hshape with ⟨rfl, rfl⟩ | ⟨d, tail, hne, rfl, hdd, rfl⟩
    · left; simp
    · right; exact ⟨d, tail, by simp, by simp, hdd, by simp⟩

theorem list_step {f : Nat} (ihE : ExprSpec f) (ihL : ListSpec f) : ListSpec (f + 1) := by
  intro acc inp r st res out hl h hs hout
  obtain ⟨pre0, r0, rfl, h0, hw⟩ := ws_spec h hs hout
  simp only [list] at hl
  rw [h0.current] at hl
  rcases hw with ⟨hsp, st0, hs0, hout0⟩ | ⟨rfl, -⟩
  swap
  · simp at hl
  cases r0 with
  | nil => simp at hl
  | cons c r1 =>
  simp only [List.head?] at hl
  split at hl
  · simp at hl
  · -- the closing parenthesis
    rename_i heq
    simp only [Option.some.injEq] at heq; subst heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨pre0 ++ [')'], r1, .outside true, by simp, h0.next,
      hs0.step (hout0.paren (Or.inr rfl)), Or.inl ⟨true, rfl⟩,
      fun _ => ⟨[.rp], Seg.tok hsp rfl, [], [], Scheme.Data.nil, Or.inl ⟨rfl, by simp⟩⟩⟩
  · -- a dot
    rename_i heq
    simp only [Option.some.injEq] at heq; subst heq
    split at hl
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
      obtain ⟨⟨head, rest⟩, he, hl⟩ := hl
      exact list_generic ihE ihL hsp h0 hs0 hout0 he hl
    · rename_i hm
      split at hl
      · simp at hl
      · rename_i hacc
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
        obtain ⟨⟨tail, rest⟩, he, hl⟩ := hl
        have hdn : ∀ x, r1.head? = some x → delimiter x = true := by
          intro x hx
          cases r1 with
          | nil => simp at hx
          | cons y ys =>
            simp only [List.head?, Option.some.injEq] at hx; subst hx
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hm
            simpa [dottedMarker, h0.current, h0.next.current] using hm
        obtain ⟨st1, h1, hs1⟩ := hs0.cons
        have hst1 : st1 = .outside false := by
          rcases hout0 with ⟨b, rfl⟩ | rfl
          · cases b <;> simp [safeStep] at h1 <;> exact h1.symm
          · simp [safeStep] at h1
        subst hst1
        obtain ⟨pre_e, r2, st2, rfl, ha2, hs2, hout2, hte⟩ :=
          ihE _ _ _ _ _ he h0.next hs1 (Or.inl ⟨false, rfl⟩)
        obtain ⟨pre_w, r3, rfl, ha3, hw3⟩ := ws_spec ha2 hs2 hout2
        split at hl
        · rename_i hcur
          rw [ha3.current] at hcur
          cases r3 with
          | nil => simp at hcur
          | cons c3 r' =>
          simp only [List.head?, Option.some.injEq] at hcur
          subst hcur
          simp only [Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          rcases hw3 with ⟨hspw, st3, hs3, hout3⟩ | ⟨h3, -⟩
          swap
          · simp at h3
          refine ⟨pre0 ++ ['.'] ++ (pre_e ++ (pre_w ++ [')'])), r', .outside true, by simp,
            ha3.next, hs3.step (hout3.paren (Or.inr rfl)), Or.inl ⟨true, rfl⟩, ?_⟩
          intro hd
          have htl : hasDotSym (M tail) = false := by
            rw [M_foldr] at hd; exact ((hasDotSym_foldr _ _).1 hd).2
          obtain ⟨toks_e, hseg_e, hdat_e⟩ := hte htl
          have heq : (pre_e ++ (pre_w ++ [')'])) ++ r' = pre_e ++ (pre_w ++ ')' :: r') := by simp
          refine ⟨.dot :: (toks_e ++ [.rp]), Seg.step hsp ⟨rfl, ?_⟩
            (Seg.append (by simpa using hseg_e) (Seg.tok (t := .rp) hspw rfl)), [], [],
            Scheme.Data.nil,
            Or.inr ⟨toks_e, tail, ?_, by simp, hdat_e, by simp⟩⟩
          · rw [heq]; exact fun x hx => delimiter_isDelim (hdn x hx)
          · simpa using hacc
        · simp at hl
  · -- any other datum
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
    obtain ⟨⟨head, rest⟩, he, hl⟩ := hl
    exact list_generic ihE ihL hsp h0 hs0 hout0 he hl

theorem specs (fuel : Nat) : ExprSpec fuel ∧ ListSpec fuel := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ _ h => by simp [expr] at h, fun _ _ _ _ _ _ h => by simp [list] at h⟩
  | succ f ih => exact ⟨expr_step ih.2, list_step ih.1 ih.2⟩

/-- **Soundness of the existing parser on safe texts**: if the scanner accepts the
text and the parser's reading has no `.` symbol, the reading is the Scheme
reading. -/
theorem parseDoc_sound_of_safe {s : String} {x : SExp} (hx : parseDoc? s = some x)
    (hsafe : lispSafe s.toList = true) (hdot : hasDotSym x = false) :
    Scheme.sexpScheme s x := by
  obtain ⟨v, hv, rfl⟩ : ∃ v, parseLexemes? s = some v ∧ doc [M v] = x := by
    simpa [parseDoc?] using hx
  simp only [parseLexemes?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv
  obtain ⟨⟨value, rest⟩, he, hv⟩ := hv
  split at hv
  swap
  · simp at hv
  rename_i hcur
  simp only [Option.some.injEq] at hv
  subst hv
  obtain ⟨pre, r', st', heq, ha, hs', hout', ht⟩ :=
    (specs _).1 _ _ _ _ _ he (At.start s) ((lispSafe_iff _).1 hsafe) (Or.inl ⟨true, rfl⟩)
  obtain ⟨pre_w, r'', rfl, ha2, hw⟩ := ws_spec ha hs' hout'
  have hr : r'' = [] := by
    rw [ha2.current] at hcur
    cases r'' with
    | nil => rfl
    | cons _ _ => simp at hcur
  subst hr
  have hd : hasDotSym (M value) = false := by
    simpa [hasDotSym, listOf] using hdot
  obtain ⟨toks, hseg, hdat⟩ := ht hd
  simp only [List.append_nil] at heq hseg
  have hb : Scheme.Space pre_w ∨ Trailing pre_w := by
    rcases hw with ⟨hsp, -⟩ | ⟨-, htr⟩
    · exact Or.inl hsp
    · exact Or.inr htr
  have hlex : Scheme.Lex s.toList toks := by
    rw [heq]; exact hseg.lex hb
  refine ⟨toks, hlex, toks, [], [M value], by simp, ?_, Scheme.Skip.nil, rfl⟩
  have := Scheme.Data.cons (s := []) Scheme.Skip.nil hdat Scheme.Data.nil
  simpa using this

end ParserSound

end Silmaril.Formats.SExpEncoding
