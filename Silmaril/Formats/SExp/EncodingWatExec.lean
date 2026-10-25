module

public import Silmaril.Formats.SExp.EncodingWat

/-!
# An executable lexer and bracketer for `sexpWat`, with soundness

`sexpWat p` (`EncodingWat.lean`) is a relation and is not decidable as stated.
For *concrete* texts, facts `sexpWat p s x` are reduced to a computation:

* `lexExec? p : Chars → Option (List Tok)` — a simple lexer covering
  whitespace, parentheses, `Tidchar` runs (keywords, numbers, identifiers),
  *plain* string literals (printable characters, no escapes), line comments and
  nested block comments.  Annotations, escapes, quoted identifiers and reserved
  tokens are not supported (the lexer returns `none`).
  Soundness: `lexExec?_sound : lexExec? p cs = some ts → Lex p true cs ts`.
* `treesExec? : List Tok → Option (List SExp)` — bracketing, sound for
  `Trees` (`treesExec?_sound`) and `treesRel` (`bracketExec?_sound`).
* `sexpWat_of_exec : sexpWatExec? p s = some x → sexpWat p s x`, so that a
  concrete fact is discharged by `sexpWat_of_exec (by decide +kernel)`.

The lexer is complete only for the supported fragment; completeness is not
claimed.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

/-! ## Decidability of the character classes -/

instance (c : Char) : Decidable (IsSpaceChar c) :=
  inferInstanceAs (Decidable (c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'))

instance (p : Profile) (c : Char) : Decidable (IsNewlineP p c) :=
  match p with
  | .v1 => inferInstanceAs (Decidable (c = '\n'))
  | .core3 => inferInstanceAs (Decidable (c = '\n' ∨ c = '\r'))

/-- Characters of a plain string literal (`Tstringchar` without escapes). -/
def PlainStrChar (c : Char) : Prop :=
  0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ c ≠ '"' ∧ c ≠ '\\'

instance (c : Char) : Decidable (PlainStrChar c) := by
  unfold PlainStrChar; infer_instance

/-- Does the head of `cs` (if any) satisfy `P`? -/
def headOk (P : Char → Prop) [DecidablePred P] : Chars → Bool
  | [] => true
  | c :: _ => decide (P c)

theorem headOk_spec {P : Char → Prop} [DecidablePred P] {cs : Chars} (h : headOk P cs = true) :
    ∀ c, cs.head? = some c → P c := by
  intro c hc
  cases cs with
  | nil => simp at hc
  | cons d r =>
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst hc
    simpa [headOk] using h

/-! ## Pieces -/

/-- Split off a line-comment body: the characters before the first newline,
and the newline with the rest (if any). -/
def splitLine (p : Profile) : Chars → Chars × Option (Char × Chars)
  | [] => ([], none)
  | c :: r =>
      if IsNewlineP p c then ([], some (c, r))
      else (c :: (splitLine p r).1, (splitLine p r).2)

theorem splitLine_noNewline (p : Profile) (cs : Chars) : NoNewline p (splitLine p cs).1 := by
  induction cs with
  | nil => intro c hc; simp [splitLine] at hc
  | cons c r ih =>
    unfold splitLine
    by_cases h : IsNewlineP p c
    · simp only [h, ↓reduceIte]; intro d hd; simp at hd
    · simp only [h, ↓reduceIte]
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h
      · exact ih d hd

theorem splitLine_none (p : Profile) (cs : Chars) (h : (splitLine p cs).2 = none) :
    cs = (splitLine p cs).1 := by
  induction cs with
  | nil => rfl
  | cons c r ih =>
    unfold splitLine at h ⊢
    by_cases hc : IsNewlineP p c
    · simp [hc] at h
    · simp only [hc, ↓reduceIte] at h ⊢
      rw [← ih h]

theorem splitLine_some (p : Profile) (cs : Chars) {nl : Char} {rest : Chars}
    (h : (splitLine p cs).2 = some (nl, rest)) :
    cs = (splitLine p cs).1 ++ nl :: rest ∧ IsNewlineP p nl := by
  induction cs with
  | nil => simp [splitLine] at h
  | cons c r ih =>
    unfold splitLine at h ⊢
    by_cases hc : IsNewlineP p c
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hc⟩
    · simp only [hc, ↓reduceIte] at h ⊢
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by rw [List.cons_append, ← h1], h2⟩

/-- The rest of a block comment after `(;`, returning what follows `;)`. -/
def blockTail? : Nat → Chars → Option Chars
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: r =>
      if c = ';' then
        if r.head? = some ')' then some r.tail else blockTail? n r
      else if c = '(' then
        if r.head? = some ';' then (blockTail? n r.tail).bind (blockTail? n)
        else blockTail? n r
      else blockTail? n r

theorem blockTail?_sound : ∀ (n : Nat) (cs rest : Chars), blockTail? n cs = some rest →
    ∃ t, cs = t ++ rest ∧ BlockTail t := by
  intro n
  induction n with
  | zero => intro cs rest h; simp [blockTail?] at h
  | succ n ih =>
    intro cs rest h
    cases cs with
    | nil => simp [blockTail?] at h
    | cons c r =>
      unfold blockTail? at h
      by_cases hs : c = ';'
      · subst hs
        simp only [↓reduceIte] at h
        by_cases hr : r.head? = some ')'
        · simp only [hr, ↓reduceIte, Option.some.injEq] at h
          subst h
          cases r with
          | nil => simp at hr
          | cons d r =>
            simp only [List.head?_cons, Option.some.injEq] at hr
            subst hr
            exact ⟨[';', ')'], rfl, BlockTail.close⟩
        · simp only [hr, ↓reduceIte] at h
          obtain ⟨t, rfl, ht⟩ := ih r rest h
          exact ⟨';' :: t, rfl, BlockTail.semi (by
            cases t with
            | nil => simp
            | cons d t' => simpa using hr) ht⟩
      · simp only [hs, ↓reduceIte] at h
        by_cases hp : c = '('
        · subst hp
          simp only [↓reduceIte] at h
          by_cases hr : r.head? = some ';'
          · simp only [hr, ↓reduceIte] at h
            cases hb : blockTail? n r.tail with
            | none => simp [hb] at h
            | some mid =>
              simp only [hb, Option.bind_some] at h
              obtain ⟨t₁, h₁, ht₁⟩ := ih r.tail mid hb
              obtain ⟨t₂, rfl, ht₂⟩ := ih mid rest h
              cases r with
              | nil => simp at hr
              | cons d r =>
                simp only [List.head?_cons, Option.some.injEq] at hr
                subst hr
                simp only [List.tail_cons] at h₁
                subst h₁
                refine ⟨('(' :: ';' :: t₁) ++ t₂, by simp, ?_⟩
                exact BlockTail.nested (BlockComment.mk ht₁) ht₂
          · simp only [hr, ↓reduceIte] at h
            obtain ⟨t, rfl, ht⟩ := ih r rest h
            exact ⟨'(' :: t, rfl, BlockTail.paren (by
              cases t with
              | nil => simp
              | cons d t' => simpa using hr) ht⟩
        · simp only [hp, ↓reduceIte] at h
          obtain ⟨t, rfl, ht⟩ := ih r rest h
          exact ⟨c :: t, rfl, BlockTail.plain hs hp ht⟩

/-- A plain string body up to the closing quote: the body and the rest. -/
def strBody? : Chars → Option (Chars × Chars)
  | [] => none
  | c :: r =>
      if c = '"' then some ([], r)
      else if PlainStrChar c then (strBody? r).map (fun br => (c :: br.1, br.2))
      else none

theorem strBody?_sound : ∀ (cs b rest : Chars), strBody? cs = some (b, rest) →
    cs = b ++ '"' :: rest ∧ ∀ c ∈ b, PlainStrChar c := by
  intro cs
  induction cs with
  | nil => intro b rest h; simp [strBody?] at h
  | cons c r ih =>
    intro b rest h
    unfold strBody? at h
    by_cases hq : c = '"'
    · simp only [hq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [hq], by simp⟩
    · simp only [hq, ↓reduceIte] at h
      by_cases hp : PlainStrChar c
      · simp only [hp, ↓reduceIte] at h
        cases hr : strBody? r with
        | none => simp [hr] at h
        | some br =>
          obtain ⟨b', rest'⟩ := br
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := ih b' rest' hr
          refine ⟨by rw [h1]; rfl, ?_⟩
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hp
          · exact h2 d hd
      · simp [hp] at h

theorem charUtf8_eq (c : Char) : charUtf8 c = String.utf8EncodeChar c := by
  simp [charUtf8, Unicode.utf8, String.toUTF8_eq_toByteArray, List.utf8Encode_singleton]

theorem stringBody_plain : ∀ (b : Chars), (∀ c ∈ b, PlainStrChar c) →
    StringBody b (b.flatMap String.utf8EncodeChar) := by
  intro b
  induction b with
  | nil => intro _; exact StringBody.nil
  | cons c r ih =>
    intro h
    have hc := h c (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := hc
    have := StringBody.cons (e := [c]) (rest := r)
      (StringElem.char h1 h2 h3 h4) (ih (fun d hd => h d (by simp [hd])))
    simpa [charUtf8_eq] using this

/-- A maximal run of `Tidchar`s. -/
def idRun : Chars → Chars × Chars
  | [] => ([], [])
  | c :: r => if IsIdChar c then (c :: (idRun r).1, (idRun r).2) else ([], c :: r)

theorem idRun_append (cs : Chars) : (idRun cs).1 ++ (idRun cs).2 = cs := by
  induction cs with
  | nil => rfl
  | cons c r ih =>
    unfold idRun
    by_cases h : IsIdChar c
    · simp only [h, ↓reduceIte, List.cons_append, ih]
    · simp [h]

theorem idRun_idChar (cs : Chars) : ∀ c ∈ (idRun cs).1, IsIdChar c := by
  induction cs with
  | nil => intro c hc; simp [idRun] at hc
  | cons c r ih =>
    unfold idRun
    by_cases h : IsIdChar c
    · simp only [h, ↓reduceIte]
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h
      · exact ih d hd
    · simp [h]

/-- Identifier-or-bare-token classification of a run. -/
def classify (cs : Chars) : Atom :=
  match cs with
  | c :: d :: ds => if c = '$' then .id (String.ofList (d :: ds)) else .sym (String.ofList cs)
  | _ => .sym (String.ofList cs)

theorem classify_sound {cs : Chars} (hne : cs ≠ []) (hid : ∀ c ∈ cs, IsIdChar c) :
    IdRun cs (classify cs) := by
  match cs, hne, hid with
  | [c], _, hid =>
    exact IdRun.sym (by simp) hid (by simp)
  | c :: d :: ds, _, hid =>
    unfold classify
    by_cases h : c = '$'
    · subst h
      simp only [↓reduceIte]
      exact IdRun.id (by simp) (fun x hx => hid x (List.mem_cons_of_mem _ hx))
    · simp only [h, ↓reduceIte]
      exact IdRun.sym (by simp) hid (by simp [h])

/-! ## The lexer -/

/-- The follow condition of an atom (`isStr`: a string literal). -/
def followAtomB (p : Profile) (isStr : Bool) (rest : Chars) : Bool :=
  match p with
  | .core3 => headOk (fun c => ¬ IsRunChar c ∧ c ≠ '"') rest
  | .v1 => isStr || headOk (fun c => ¬ IsIdChar c) rest

theorem follow_atom_of {p : Profile} {a : Atom} {rest : Chars}
    (h : followAtomB p (match a with | .str _ => true | _ => false) rest = true) :
    Follow p (.atom a) rest := by
  cases p with
  | core3 => exact headOk_spec h
  | v1 =>
    cases a with
    | str bs => trivial
    | sym s => exact headOk_spec (by simpa [followAtomB] using h)
    | id s => exact headOk_spec (by simpa [followAtomB] using h)

/-- The lexer loop with fuel. -/
def lexGo (p : Profile) : Nat → Chars → Option (List Tok)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: r =>
      if IsSpaceChar c then lexGo p n r
      else if c = ';' ∧ r.head? = some ';' then
        match (splitLine p r.tail).2 with
        | none => some []
        | some (_, rest) => lexGo p n rest
      else if c = '(' ∧ r.head? = some ';' then
        match blockTail? (r.length + 1) r.tail with
        | none => none
        | some rest => lexGo p n rest
      else if c = '(' then
        if p = .core3 ∧ r.head? = some '@' then none else (Tok.lp :: ·) <$> lexGo p n r
      else if c = ')' then (Tok.rp :: ·) <$> lexGo p n r
      else if c = '"' then
        match strBody? r with
        | none => none
        | some (b, rest) =>
          if (b.flatMap String.utf8EncodeChar).length < 2 ^ 32 ∧
              followAtomB p true rest = true then
            (Tok.atom (.str (b.flatMap String.utf8EncodeChar)) :: ·) <$> lexGo p n rest
          else none
      else if IsIdChar c then
        if followAtomB p false (idRun r).2 = true then
          (Tok.atom (classify (c :: (idRun r).1)) :: ·) <$> lexGo p n (idRun r).2
        else none
      else none

/-- **Executable lexer** for the supported fragment. -/
def lexExec? (p : Profile) (cs : Chars) : Option (List Tok) := lexGo p (cs.length + 1) cs

/-! ### Soundness -/

theorem lex_space {p : Profile} {top : Bool} {a r : Chars} {ts : List Tok} (ha : SpaceItem p a)
    (h : Lex p top r ts) : Lex p top (a ++ r) ts := by
  cases h with
  | done hs => exact Lex.done (Space.cons ha hs)
  | doneEof hs hb =>
    rw [← List.append_assoc]; exact Lex.doneEof (Space.cons ha hs) hb
  | step hs ht hf hl =>
    rw [← List.append_assoc, ← List.append_assoc]
    have := Lex.step (Space.cons ha hs) ht hf hl
    simpa [List.append_assoc] using this

theorem lex_tok {p : Profile} {top : Bool} {c rest : Chars} {t : Tok} {ts : List Tok}
    (h1 : Tok1 p top c t) (h2 : Follow p t rest) (h3 : Lex p top rest ts) :
    Lex p top (c ++ rest) (t :: ts) := by
  simpa using Lex.step (s := []) Space.nil h1 h2 h3

theorem idChar_ne_semi {c : Char} (h : IsIdChar c) : c ≠ ';' := by
  rintro rfl; revert h; decide

theorem lexGo_sound (p : Profile) : ∀ (n : Nat) (cs : Chars) (ts : List Tok),
    lexGo p n cs = some ts → Lex p true cs ts := by
  intro n
  induction n with
  | zero => intro cs ts h; simp [lexGo] at h
  | succ n ih =>
    intro cs ts h
    cases cs with
    | nil =>
      simp only [lexGo, Option.some.injEq] at h
      subst h; exact Lex.done Space.nil
    | cons c r =>
      unfold lexGo at h
      by_cases hsp : IsSpaceChar c
      · simp only [hsp, ↓reduceIte] at h
        exact lex_space (a := [c]) (SpaceItem.char hsp) (ih r ts h)
      simp only [hsp, ↓reduceIte] at h
      by_cases hlc : c = ';' ∧ r.head? = some ';'
      · simp only [hlc, and_self, ↓reduceIte] at h
        obtain ⟨rfl, hr⟩ := hlc
        cases r with
        | nil => simp at hr
        | cons d r =>
          simp only [List.head?_cons, Option.some.injEq] at hr
          subst hr
          simp only [List.tail_cons] at h
          cases hs : (splitLine p r).2 with
          | none =>
            simp only [hs, Option.some.injEq] at h
            subst h
            have e := splitLine_none p r hs
            have := Lex.doneEof (p := p) (s := []) Space.nil (splitLine_noNewline p r)
            rw [e]; simpa using this
          | some nr =>
            obtain ⟨nl, rest⟩ := nr
            simp only [hs] at h
            obtain ⟨e, hnl⟩ := splitLine_some p r hs
            have hi : SpaceItem p (';' :: ';' :: ((splitLine p r).1 ++ [nl])) :=
              SpaceItem.line (splitLine_noNewline p r) hnl
            have := lex_space hi (ih rest ts h)
            rw [e]; simpa using this
      simp only [hlc, ↓reduceIte] at h
      by_cases hbc : c = '(' ∧ r.head? = some ';'
      · simp only [hbc, and_self, ↓reduceIte] at h
        obtain ⟨rfl, hr⟩ := hbc
        cases hb : blockTail? (r.length + 1) r.tail with
        | none => simp [hb] at h
        | some rest =>
          simp only [hb] at h
          obtain ⟨t, e, ht⟩ := blockTail?_sound _ _ _ hb
          cases r with
          | nil => simp at hr
          | cons d r =>
            simp only [List.head?_cons, Option.some.injEq] at hr
            subst hr
            simp only [List.tail_cons] at e
            subst e
            have hi : SpaceItem p ('(' :: ';' :: t) := SpaceItem.block (BlockComment.mk ht)
            simpa using lex_space hi (ih rest ts h)
      simp only [hbc, ↓reduceIte] at h
      by_cases hlp : c = '('
      · subst hlp
        simp only [↓reduceIte] at h
        by_cases ha : p = .core3 ∧ r.head? = some '@'
        · simp [ha] at h
        simp only [ha, ↓reduceIte] at h
        cases hg : lexGo p n r with
        | none => simp [hg] at h
        | some ts' =>
          simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          subst h
          refine lex_tok (c := ['(']) (by cases p <;> rfl) ?_ (ih r ts' hg)
          have h1 : r.head? ≠ some ';' := fun e => hbc ⟨rfl, e⟩
          cases p with
          | v1 => exact h1
          | core3 => exact ⟨h1, fun e => ha ⟨rfl, e⟩⟩
      simp only [hlp, ↓reduceIte] at h
      by_cases hrp : c = ')'
      · subst hrp
        simp only [↓reduceIte] at h
        cases hg : lexGo p n r with
        | none => simp [hg] at h
        | some ts' =>
          simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          subst h
          exact lex_tok (c := [')']) (by cases p <;> rfl) (by cases p <;> trivial) (ih r ts' hg)
      simp only [hrp, ↓reduceIte] at h
      by_cases hq : c = '"'
      · subst hq
        simp only [↓reduceIte] at h
        cases hs : strBody? r with
        | none => simp [hs] at h
        | some br =>
          obtain ⟨b, rest⟩ := br
          simp only [hs] at h
          obtain ⟨e, hb⟩ := strBody?_sound r b rest hs
          by_cases hc : (b.flatMap String.utf8EncodeChar).length < 2 ^ 32 ∧
              followAtomB p true rest = true
          · simp only [hc, and_self, ↓reduceIte] at h
            cases hg : lexGo p n rest with
            | none => simp [hg] at h
            | some ts' =>
              simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
              subst h
              have hlit : StringLit ('"' :: (b ++ ['"'])) (b.flatMap String.utf8EncodeChar) :=
                ⟨b, rfl, stringBody_plain b hb, hc.1⟩
              have h1 : Tok1 p true ('"' :: (b ++ ['"']))
                  (.atom (.str (b.flatMap String.utf8EncodeChar))) := by
                cases p with
                | v1 => exact hlit
                | core3 => exact ⟨RunAtom3.str hlit, by simp⟩
              have := lex_tok h1 (follow_atom_of hc.2) (ih rest ts' hg)
              rw [e]; simpa using this
          · simp only [hc, ↓reduceIte, reduceCtorEq] at h
      simp only [hq, ↓reduceIte] at h
      by_cases hid : IsIdChar c
      · simp only [hid, ↓reduceIte] at h
        by_cases hf : followAtomB p false (idRun r).2 = true
        · simp only [hf, ↓reduceIte] at h
          cases hg : lexGo p n (idRun r).2 with
          | none => simp [hg] at h
          | some ts' =>
            simp only [hg, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
            subst h
            have hall : ∀ x ∈ c :: (idRun r).1, IsIdChar x := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hid
              · exact idRun_idChar r x hx
            have hrun := classify_sound (cs := c :: (idRun r).1) (by simp) hall
            have h1 : Tok1 p true (c :: (idRun r).1) (.atom (classify (c :: (idRun r).1))) := by
              cases p with
              | core3 =>
                refine ⟨RunAtom3.idRun hrun, ?_⟩
                have := idChar_ne_semi hid
                cases hh : (idRun r).1 <;> simp [this]
              | v1 =>
                -- the atom is not a string
                revert hrun
                generalize classify (c :: (idRun r).1) = a
                intro hrun
                cases a with
                | str bs => cases hrun
                | sym s => exact hrun
                | id s => exact hrun
            have hf' : Follow p (.atom (classify (c :: (idRun r).1))) (idRun r).2 := by
              apply follow_atom_of
              revert hf
              generalize classify (c :: (idRun r).1) = a
              intro hf
              cases a <;> first | exact hf | (cases p <;> simp_all [followAtomB])
            have e : c :: r = (c :: (idRun r).1) ++ (idRun r).2 := by
              rw [List.cons_append, idRun_append]
            rw [e]; exact lex_tok h1 hf' (ih _ ts' hg)
        · simp [hf] at h
      · simp [hid] at h

theorem lexExec?_sound {p : Profile} {cs : Chars} {ts : List Tok} (h : lexExec? p cs = some ts) :
    Lex p true cs ts :=
  lexGo_sound p _ cs ts h

/-! ## The bracketer -/

/-- Parse a sequence of trees, stopping at `)` or the end; returns the trees and
the remaining tokens. -/
def treesGo : Nat → List Tok → Option (List SExp × List Tok)
  | 0, _ => none
  | _ + 1, [] => some ([], [])
  | _ + 1, .rp :: r => some ([], .rp :: r)
  | _ + 1, .reserved :: _ => none
  | _ + 1, .punct _ :: _ => none
  | n + 1, .atom a :: r => (treesGo n r).map fun xr => (.atom a :: xr.1, xr.2)
  | n + 1, .lp :: r =>
      match treesGo n r with
      | some (ys, .rp :: r') => (treesGo n r').map fun xr => (listOf ys :: xr.1, xr.2)
      | _ => none

theorem treesGo_sound : ∀ (n : Nat) (ts : List Tok) (xs : List SExp) (rest : List Tok),
    treesGo n ts = some (xs, rest) → ∃ pre, ts = pre ++ rest ∧ Trees pre xs := by
  intro n
  induction n with
  | zero => intro ts xs rest h; simp [treesGo] at h
  | succ n ih =>
    intro ts xs rest h
    match ts, h with
    | [], h =>
      simp only [treesGo, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, Trees.nil⟩
    | .rp :: r, h =>
      simp only [treesGo, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, Trees.nil⟩
    | .reserved :: r, h => simp [treesGo] at h
    | .punct _ :: r, h => simp [treesGo] at h
    | .atom a :: r, h =>
      simp only [treesGo] at h
      cases hg : treesGo n r with
      | none => simp [hg] at h
      | some yr =>
        obtain ⟨ys, rest'⟩ := yr
        simp only [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, rfl, hp⟩ := ih r ys rest' hg
        exact ⟨.atom a :: pre, rfl, Trees.cons (a := [.atom a]) (Tree.atom a) hp⟩
    | .lp :: r, h =>
      simp only [treesGo] at h
      cases hg : treesGo n r with
      | none => simp [hg] at h
      | some yr =>
        obtain ⟨ys, r₁⟩ := yr
        cases r₁ with
        | nil => simp [hg] at h
        | cons t r' =>
          cases t with
          | rp =>
            simp only [hg] at h
            cases hg' : treesGo n r' with
            | none => simp [hg'] at h
            | some zr =>
              obtain ⟨zs, rest'⟩ := zr
              simp only [hg', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨pre₁, e₁, hp₁⟩ := ih r ys (.rp :: r') hg
              obtain ⟨pre₂, rfl, hp₂⟩ := ih r' zs rest' hg'
              subst e₁
              refine ⟨(.lp :: (pre₁ ++ [.rp])) ++ pre₂, by simp, ?_⟩
              exact Trees.cons (Tree.list hp₁) hp₂
          | lp => simp [hg] at h
          | atom _ => simp [hg] at h
          | reserved => simp [hg] at h
          | punct _ => simp [hg] at h

/-- **Executable bracketing**: the whole token list as a sequence of trees. -/
def treesExec? (ts : List Tok) : Option (List SExp) :=
  match treesGo (ts.length + 1) ts with
  | some (xs, []) => some xs
  | _ => none

theorem treesExec?_sound {ts : List Tok} {xs : List SExp} (h : treesExec? ts = some xs) :
    Trees ts xs := by
  unfold treesExec? at h
  cases hg : treesGo (ts.length + 1) ts with
  | none => simp [hg] at h
  | some yr =>
    obtain ⟨ys, rest⟩ := yr
    cases rest with
    | nil =>
      simp only [hg, Option.some.injEq] at h
      subst h
      obtain ⟨pre, e, hp⟩ := treesGo_sound _ _ _ _ hg
      rw [List.append_nil] at e
      rw [e]; exact hp
    | cons _ _ => simp [hg] at h

/-- Bracketing into a document. -/
def bracketExec? (ts : List Tok) : Option SExp := (treesExec? ts).map doc

theorem bracketExec?_sound {ts : List Tok} {x : SExp} (h : bracketExec? ts = some x) :
    treesRel ts x := by
  unfold bracketExec? at h
  cases hg : treesExec? ts with
  | none => simp [hg] at h
  | some xs =>
    simp only [hg, Option.map_some, Option.some.injEq] at h
    exact ⟨xs, treesExec?_sound hg, h.symm⟩

/-! ## Concrete `sexpWat` facts -/

/-- Lex and bracket a text. -/
def sexpWatExec? (p : Profile) (s : String) : Option SExp :=
  (lexExec? p s.toList).bind bracketExec?

/-- **Reduction of concrete `sexpWat` facts to computation.** -/
theorem sexpWat_of_exec {p : Profile} {s : String} {x : SExp} (h : sexpWatExec? p s = some x) :
    sexpWat p s x := by
  unfold sexpWatExec? at h
  cases hl : lexExec? p s.toList with
  | none => simp [hl] at h
  | some ts =>
    simp only [hl, Option.bind_some] at h
    exact ⟨ts, lexExec?_sound hl, bracketExec?_sound h⟩

example : sexpWat .core3 "(module (;a;;) (func)) ;; c" (doc [listOf [kw "module", listOf [kw "func"]]]) :=
  sexpWat_of_exec (by decide +kernel)

example : sexpWat .v1 "(data \"hi\" $x)"
    (doc [listOf [kw "data", .atom (.str [104, 105]), .atom (.id "x")]]) :=
  sexpWat_of_exec (by decide +kernel)

end Silmaril.Formats.SExpEncoding.Wat
