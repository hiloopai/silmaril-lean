module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Lexical

/-!
# A verified reader for the `--ast` lexical convention

`Silmaril/SpecTec/SExp/Lexical.lean` specifies the lexical convention of a
`spectec --ast` file as the inductive relations `LexesPre`, `LexesSeq` and
`LexesStream`, and proves them deterministic, but defines no decoder:
`Silmaril/SpecTec/SExp/Parse.lean` has one, written with `partial def` for
speed at elaboration time, and it is deliberately opaque.  This module closes
the gap with a *total* reader that is proved sound and complete against the
specification.

## Shape of the reader

The three scanners `dropSpaces`, `takeBare` and `takeQuoted` are structurally
recursive on the input and implement maximal munch directly; `takeBare_eq`,
`dropSpaces_eq` and `takeQuoted_complete` are the lemmas that say each scanner
takes exactly the split the corresponding rule of `Lexical.lean` describes, and
they are what the completeness proof runs on.

`lexOne?` and `lexSeq?` are mutually recursive, and the recursion is *not*
structural in the input — after a node's tag is read, what is left is a suffix
of the input rather than a subterm — so they take an explicit `Nat` fuel
argument and recurse structurally on it.  Well-founded recursion is avoided on
purpose: it does not reduce in the kernel, and the `example`s at the end of
this file are checked by `rfl` and by `decide`.  `lex?` supplies
`l.length + 1`, which `lexStream?_complete` shows is always enough.

## What is proved

* `lex?_sound` : `lex? l = some es → LexesStream l es`;
* `lex?_complete` : `LexesStream l es → lex? l = some es`;
* hence `streamRel.DecoderSound parseStream?`,
  `streamRel.DecoderComplete parseStream?` and
  `streamRel = EncRel.ofDecoder parseStream?` (`streamRel_eq_ofDecoder`), in
  the vocabulary of `Silmaril/Encoding/Relation.lean`.

The single-expression convention `lexicalRel` is covered too, through
`lexesStream_singleton_iff`: a stream that holds exactly one S-expression is
the same thing as a `Lexes` derivation, so `parse?` is a sound and complete
decoder for `lexicalRel`.

Everything works on `List Char`; `parseStream?` and `parse?`, the only
declarations that mention `String`, are at the very end.  That is forced by
`String.toList` costing about a millisecond per character to reduce in the
kernel (`docs/projects/spectec/README.md`).
-/

@[expose] public section

namespace Silmaril.SpecTec.SExp

/-! ## Character classes, as `Bool` tests -/

/-- Boolean test for `IsSpace`: the two layout characters
(`spectec/src/util/sexpr.ml:21-22`). -/
def isSpaceB (c : Char) : Bool := c == ' ' || c == '\n'

/-- `isSpaceB` decides `IsSpace`. -/
@[simp] theorem isSpaceB_eq_true {c : Char} : isSpaceB c = true ↔ IsSpace c := by
  simp [isSpaceB, IsSpace]

/-- Boolean test for `IsBare`: a character that may occur in an unquoted
token. -/
def isBareB (c : Char) : Bool := !isSpaceB c && c != '(' && c != ')' && c != '"'

/-- `isBareB` decides `IsBare`. -/
@[simp] theorem isBareB_eq_true {c : Char} : isBareB c = true ↔ IsBare c := by
  simp [isBareB, IsBare, isSpaceB, IsSpace, and_assoc]

/-- `isBareB` refutes `IsBare`. -/
theorem isBareB_eq_false {c : Char} : isBareB c = false ↔ ¬ IsBare c := by
  rw [← isBareB_eq_true, Bool.not_eq_true]

/-! ## The three scanners -/

/-- Drop a leading run of layout characters. -/
def dropSpaces : List Char → List Char
  | [] => []
  | c :: cs => if isSpaceB c then dropSpaces cs else c :: cs

/-- `dropSpaces` removes nothing but layout. -/
theorem dropSpaces_split : ∀ l : List Char, ∃ w, Spaces w ∧ l = w ++ dropSpaces l
  | [] => ⟨[], spaces_nil, rfl⟩
  | c :: cs => by
      rw [dropSpaces]
      by_cases h : isSpaceB c
      · obtain ⟨w, hw, heq⟩ := dropSpaces_split cs
        refine ⟨c :: w, ?_, ?_⟩
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact isSpaceB_eq_true.mp h
          · exact hw d hd
        · simp [h, ← heq]
      · exact ⟨[], spaces_nil, by simp [h]⟩

/-- Whatever `dropSpaces` leaves does not start with layout. -/
theorem headNot_dropSpaces : ∀ l : List Char, HeadNot IsSpace (dropSpaces l)
  | [] => trivial
  | c :: cs => by
      rw [dropSpaces]
      by_cases h : isSpaceB c
      · simpa [h] using headNot_dropSpaces cs
      · simpa [h, HeadNot] using fun hc => h (isSpaceB_eq_true.mpr hc)

/-- `dropSpaces` never lengthens its input. -/
theorem dropSpaces_length_le : ∀ l : List Char, (dropSpaces l).length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
      rw [dropSpaces]
      by_cases h : isSpaceB c
      · simpa [h] using Nat.le_succ_of_le (dropSpaces_length_le cs)
      · simp [h]

/-- **Maximal munch for layout.**  `dropSpaces` takes exactly the split that
`Spaces`/`HeadNot IsSpace` describes. -/
theorem dropSpaces_eq {w r : List Char} (hw : Spaces w) (hr : HeadNot IsSpace r) :
    dropSpaces (w ++ r) = r := by
  induction w with
  | nil =>
      cases r with
      | nil => rfl
      | cons c cs =>
          have : ¬ isSpaceB c := fun h => hr (isSpaceB_eq_true.mp h)
          simp [dropSpaces, this]
  | cons c w ih =>
      have hc : isSpaceB c := isSpaceB_eq_true.mpr (hw c (List.mem_cons_self ..))
      rw [List.cons_append, dropSpaces, ite_eq_left hc]
      exact ih fun d hd => hw d (List.mem_cons_of_mem _ hd)

/-- A pure layout run is dropped entirely. -/
theorem dropSpaces_eq_nil {l : List Char} (h : Spaces l) : dropSpaces l = [] := by
  simpa using dropSpaces_eq h (r := []) trivial

/-- Split a character list at the end of its maximal bare prefix. -/
def takeBare : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if isBareB c then ((takeBare cs).1.cons c, (takeBare cs).2) else ([], c :: cs)

/-- `takeBare` splits its input. -/
theorem takeBare_append : ∀ l : List Char, (takeBare l).1 ++ (takeBare l).2 = l
  | [] => rfl
  | c :: cs => by
      rw [takeBare]
      by_cases h : isBareB c
      · simpa [h] using takeBare_append cs
      · simp [h]

/-- Everything `takeBare` takes is bare. -/
theorem takeBare_bare : ∀ (l : List Char), ∀ c ∈ (takeBare l).1, IsBare c
  | [], c, hc => by simp [takeBare] at hc
  | d :: ds, c, hc => by
      rw [takeBare] at hc
      by_cases h : isBareB d
      · simp only [h, ite_true] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact isBareB_eq_true.mp h
        · exact takeBare_bare ds c hc
      · simp [h] at hc

/-- Whatever `takeBare` leaves cannot continue a bare token. -/
theorem takeBare_headNot : ∀ l : List Char, HeadNot IsBare (takeBare l).2
  | [] => trivial
  | c :: cs => by
      rw [takeBare]
      by_cases h : isBareB c
      · simpa [h] using takeBare_headNot cs
      · simpa [h, HeadNot] using isBareB_eq_false.mp (Bool.not_eq_true _ ▸ h)

/-- `takeBare` takes a leading bare character. -/
theorem takeBare_cons {c : Char} (h : isBareB c) (cs : List Char) :
    takeBare (c :: cs) = (c :: (takeBare cs).1, (takeBare cs).2) := by
  rw [takeBare, ite_eq_left h]

/-- **Maximal munch for bare tokens.**  `takeBare` takes exactly the split that
`LexesPre.bare` describes; this is `run_split` of `Lexical.lean` in action. -/
theorem takeBare_eq {w r : List Char} (hw : ∀ c ∈ w, IsBare c) (hr : HeadNot IsBare r) :
    takeBare (w ++ r) = (w, r) := by
  obtain ⟨h₁, h₂⟩ :=
    run_split (takeBare_bare (w ++ r)) hw (takeBare_headNot (w ++ r)) hr
      (takeBare_append (w ++ r))
  exact Prod.ext h₁ h₂

/-- Scan the body of a quoted token, starting just after the opening quote.
Returns the body and what follows the closing quote; `none` when the token is
never closed. -/
def takeQuoted : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
      if c = '"' then some ([], cs)
      else if c = '\\' then
        match cs with
        | [] => none
        | d :: cs' => (takeQuoted cs').map fun p => ('\\' :: d :: p.1, p.2)
      else (takeQuoted cs).map fun p => (c :: p.1, p.2)

/-- `takeQuoted` on the empty input. -/
@[simp] theorem takeQuoted_nil : takeQuoted [] = none := rfl

/-- One unconditional unfolding step for `takeQuoted`. -/
theorem takeQuoted_cons (c : Char) (cs : List Char) :
    takeQuoted (c :: cs) =
      if c = '"' then some ([], cs)
      else if c = '\\' then
        match cs with
        | [] => none
        | d :: cs' => (takeQuoted cs').map fun p => ('\\' :: d :: p.1, p.2)
      else (takeQuoted cs).map fun p => (c :: p.1, p.2) := by
  rw [takeQuoted.eq_def]

/-- `takeQuoted` at the closing quotation mark. -/
@[simp] theorem takeQuoted_quote (cs : List Char) : takeQuoted ('"' :: cs) = some ([], cs) := by
  rw [takeQuoted_cons]; simp

/-- `takeQuoted` across a two-character escape. -/
@[simp] theorem takeQuoted_esc (d : Char) (cs : List Char) :
    takeQuoted ('\\' :: d :: cs) = (takeQuoted cs).map fun p => ('\\' :: d :: p.1, p.2) := by
  rw [takeQuoted_cons]; simp

/-- `takeQuoted` across an ordinary character. -/
theorem takeQuoted_lit {c : Char} (h₁ : c ≠ '"') (h₂ : c ≠ '\\') (cs : List Char) :
    takeQuoted (c :: cs) = (takeQuoted cs).map fun p => (c :: p.1, p.2) := by
  rw [takeQuoted_cons]; simp [h₁, h₂]

/-- **Soundness of `takeQuoted`.**  What it returns is a `QuotedBody` followed
by the closing quotation mark. -/
theorem takeQuoted_sound : ∀ (l : List Char) {b r : List Char},
    takeQuoted l = some (b, r) → QuotedBody b ∧ l = b ++ '"' :: r := by
  intro l
  induction l using takeQuoted.induct with
  | case1 => intro b r h; simp at h
  | case2 cs =>
      intro b r h
      rw [takeQuoted_quote] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨.nil, rfl⟩
  | case3 _ => intro b r h; rw [takeQuoted_cons] at h; simp at h
  | case4 d cs _ ih =>
      intro b r h
      rw [takeQuoted_esc] at h
      rcases hq : takeQuoted cs with _ | ⟨b', r'⟩ <;> rw [hq] at h
      · simp at h
      · obtain ⟨hqb, he⟩ := ih hq
        simp only [Option.map_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨.esc d hqb, by rw [he]; rfl⟩
  | case5 d cs h₁ h₂ ih =>
      intro b r h
      rw [takeQuoted_lit h₁ h₂] at h
      rcases hq : takeQuoted cs with _ | ⟨b', r'⟩ <;> rw [hq] at h
      · simp at h
      · obtain ⟨hqb, he⟩ := ih hq
        simp only [Option.map_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨.lit h₁ h₂ hqb, by rw [he]; rfl⟩

/-- **Completeness of `takeQuoted`.**  Maximal munch for quoted tokens: a body
is terminated by the first quotation mark that is not part of an escape. -/
theorem takeQuoted_complete {b : List Char} (hb : QuotedBody b) (r : List Char) :
    takeQuoted (b ++ '"' :: r) = some (b, r) := by
  induction hb with
  | nil => simp
  | esc c _ ih => rw [List.cons_append, List.cons_append, takeQuoted_esc, ih]; rfl
  | lit h₁ h₂ _ ih => rw [List.cons_append, takeQuoted_lit h₁ h₂, ih]; rfl

/-! ## How much a derivation consumes

The two bounds below are what makes the fuel accounting work: a spelling
consumes at least one character, so the remainder of a `LexesPre` derivation is
strictly shorter than its input. -/

mutual

/-- Every spelling consumes at least one character. -/
theorem lexesPre_length_lt {l : List Char} {e : SExp} {r : List Char}
    (h : LexesPre l e r) : r.length < l.length := by
  match h with
  | @LexesPre.bare s rest hs _ =>
      obtain ⟨c, cs, hl, -⟩ := hs.head
      rw [hl]; simp; omega
  | @LexesPre.quoted s rest hs =>
      obtain ⟨t, hl⟩ := hs.head
      rw [hl]; simp; omega
  | @LexesPre.node t es body rest _ _ hseq =>
      have h2 := @lexesSeq_length_le _ _ _ hseq
      simp only [List.length_cons, List.length_append] at h2 ⊢
      omega

/-- A sequence of children never lengthens what is left. -/
theorem lexesSeq_length_le {l : List Char} {es : List SExp} {r : List Char}
    (h : LexesSeq l es r) : r.length ≤ l.length := by
  match h with
  | @LexesSeq.nil w rest _ => simp
  | @LexesSeq.cons w body rest rest' e es _ hpre hseq =>
      have h1 := @lexesPre_length_lt _ _ _ hpre
      have h2 := @lexesSeq_length_le _ _ _ hseq
      simp only [List.length_append]
      omega

end

/-! ## The reader

`lexOne?` reads one S-expression and `lexSeq?` reads the children of a node up
to and including the closing parenthesis, returning what follows it.  Both
recurse structurally on the `Nat` fuel; `lex?` below shows that
`l.length + 1` is always enough. -/

mutual

/-- Read one S-expression from the front of `l`, returning it and the
remainder.  The three branches are the three tokens of the convention: a node
(`spectec/src/util/sexpr.ml:23`, whose tag abuts the `(`), a quoted atom whose
stored spelling includes the quotation marks
(`spectec/src/backend-ast/print.ml:12`), and a bare atom. -/
def lexOne? : Nat → List Char → Option (SExp × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, c :: cs =>
      if c = '(' then
        match takeBare cs with
        | ([], _) => none
        | (t :: tg, body) =>
            (lexSeq? fuel body).map fun p => (SExp.node (String.ofList (t :: tg)) p.1, p.2)
      else if c = '"' then
        (takeQuoted cs).map fun p => (SExp.atom (String.ofList ('"' :: (p.1 ++ ['"']))), p.2)
      else if isBareB c then
        some (SExp.atom (String.ofList (takeBare (c :: cs)).1), (takeBare (c :: cs)).2)
      else none

/-- Read the children of a node, up to and including the closing parenthesis;
the remainder is what follows that parenthesis. -/
def lexSeq? : Nat → List Char → Option (List SExp × List Char)
  | 0, _ => none
  | fuel + 1, l =>
      match dropSpaces l with
      | [] => none
      | c :: cs =>
          if c = ')' then some ([], cs)
          else (lexOne? fuel (c :: cs)).bind fun p =>
            (lexSeq? fuel p.2).map fun q => (p.1 :: q.1, q.2)

end

/-- `lexOne?` runs out of fuel. -/
@[simp] theorem lexOne?_zero (l : List Char) : lexOne? 0 l = none := rfl

/-- `lexOne?` at the end of the input. -/
@[simp] theorem lexOne?_nil (fuel : Nat) : lexOne? (fuel + 1) [] = none := rfl

/-- One unfolding step for `lexOne?`. -/
theorem lexOne?_cons (fuel : Nat) (c : Char) (cs : List Char) :
    lexOne? (fuel + 1) (c :: cs) =
      (if c = '(' then
        match takeBare cs with
        | ([], _) => none
        | (t :: tg, body) =>
            (lexSeq? fuel body).map fun p => (SExp.node (String.ofList (t :: tg)) p.1, p.2)
      else if c = '"' then
        (takeQuoted cs).map fun p => (SExp.atom (String.ofList ('"' :: (p.1 ++ ['"']))), p.2)
      else if isBareB c then
        some (SExp.atom (String.ofList (takeBare (c :: cs)).1), (takeBare (c :: cs)).2)
      else none) := rfl

/-- `lexOne?` at a node whose tag is empty: rejected, because
`spectec/src/util/sexpr.ml:23` prints a node as `"(" ^+ s` with a nonempty
bare tag. -/
theorem lexOne?_node_nil (fuel : Nat) {cs body : List Char}
    (h : takeBare cs = ([], body)) : lexOne? (fuel + 1) ('(' :: cs) = none := by
  rw [lexOne?_cons, ite_eq_left (rfl : ('(' : Char) = '('), h]

/-- `lexOne?` at a node. -/
theorem lexOne?_node (fuel : Nat) {cs : List Char} {t : Char} {tg body : List Char}
    (h : takeBare cs = (t :: tg, body)) :
    lexOne? (fuel + 1) ('(' :: cs) =
      (lexSeq? fuel body).map fun p => (SExp.node (String.ofList (t :: tg)) p.1, p.2) := by
  rw [lexOne?_cons, ite_eq_left (rfl : ('(' : Char) = '('), h]

/-- `lexOne?` at a quoted atom. -/
theorem lexOne?_quoted (fuel : Nat) (cs : List Char) :
    lexOne? (fuel + 1) ('"' :: cs) =
      (takeQuoted cs).map fun p => (SExp.atom (String.ofList ('"' :: (p.1 ++ ['"']))), p.2) := by
  rw [lexOne?_cons, ite_eq_right (by decide : ¬ ('"' : Char) = '('),
    ite_eq_left (rfl : ('"' : Char) = '"')]

/-- `lexOne?` at a bare atom. -/
theorem lexOne?_bare (fuel : Nat) {c : Char} (hc : IsBare c) (cs : List Char) :
    lexOne? (fuel + 1) (c :: cs) =
      some (SExp.atom (String.ofList (takeBare (c :: cs)).1), (takeBare (c :: cs)).2) := by
  rw [lexOne?_cons, ite_eq_right hc.2.1, ite_eq_right hc.2.2.2,
    ite_eq_left (isBareB_eq_true.mpr hc)]

/-- `lexOne?` rejects every other character: layout, a closing parenthesis, or
the end of the input. -/
theorem lexOne?_reject (fuel : Nat) {c : Char} (hc : ¬ IsBare c) (h1 : ¬ c = '(')
    (h2 : ¬ c = '"') (cs : List Char) : lexOne? (fuel + 1) (c :: cs) = none := by
  rw [lexOne?_cons, ite_eq_right h1, ite_eq_right h2,
    ite_eq_right (by simpa using hc)]

/-- `lexSeq?` runs out of fuel. -/
@[simp] theorem lexSeq?_zero (l : List Char) : lexSeq? 0 l = none := rfl

/-- One unfolding step for `lexSeq?`. -/
theorem lexSeq?_succ (fuel : Nat) (l : List Char) :
    lexSeq? (fuel + 1) l =
      (match dropSpaces l with
      | [] => none
      | c :: cs =>
          if c = ')' then some ([], cs)
          else (lexOne? fuel (c :: cs)).bind fun p =>
            (lexSeq? fuel p.2).map fun q => (p.1 :: q.1, q.2)) := rfl

/-- `lexSeq?` fails when the input runs out before the closing parenthesis. -/
theorem lexSeq?_succ_nil (fuel : Nat) {l : List Char} (h : dropSpaces l = []) :
    lexSeq? (fuel + 1) l = none := by rw [lexSeq?_succ, h]

/-- One unfolding step for `lexSeq?`, with the layout already skipped. -/
theorem lexSeq?_succ_cons (fuel : Nat) {l : List Char} {c : Char} {cs : List Char}
    (h : dropSpaces l = c :: cs) :
    lexSeq? (fuel + 1) l =
      (if c = ')' then some ([], cs)
      else (lexOne? fuel (c :: cs)).bind fun p =>
        (lexSeq? fuel p.2).map fun q => (p.1 :: q.1, q.2)) := by
  rw [lexSeq?_succ, h]

/-! ## Soundness

Everything `lexOne?` and `lexSeq?` return is a derivation of the specification.
The two statements are proved together by induction on the fuel, because the
functions are mutually recursive. -/

/-- **Soundness**, both halves at once: induction on the fuel. -/
theorem lex_sound (fuel : Nat) :
    (∀ {l : List Char} {e : SExp} {r : List Char},
        lexOne? fuel l = some (e, r) → LexesPre l e r) ∧
      (∀ {l : List Char} {es : List SExp} {r : List Char},
        lexSeq? fuel l = some (es, r) → LexesSeq l es (')' :: r)) := by
  induction fuel with
  | zero => exact ⟨fun h => by simp at h, fun h => by simp at h⟩
  | succ fuel ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · intro l e r h
        match l with
        | [] => simp at h
        | c :: cs =>
          by_cases hc : c = '('
          · subst hc
            rcases hb : takeBare cs with ⟨tag, body⟩
            have happ : tag ++ body = cs := by
              have h0 := takeBare_append cs; rw [hb] at h0; exact h0
            have hbare : ∀ d ∈ tag, IsBare d := by
              have h0 := takeBare_bare cs; rw [hb] at h0; exact h0
            have hhead : HeadNot IsBare body := by
              have h0 := takeBare_headNot cs; rw [hb] at h0; exact h0
            cases tag with
            | nil => rw [lexOne?_node_nil fuel hb] at h; simp at h
            | cons t tg =>
              rw [lexOne?_node fuel hb] at h
              rcases hq : lexSeq? fuel body with _ | ⟨es, r'⟩ <;> rw [hq] at h
              · simp at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ht : IsBareToken (String.ofList (t :: tg)) := by
                rw [IsBareToken, String.toList_ofList]
                exact ⟨by simp, hbare⟩
              have hpre := LexesPre.node ht hhead (ih2 hq)
              rw [String.toList_ofList, happ] at hpre
              exact hpre
          · by_cases hq : c = '"'
            · subst hq
              rw [lexOne?_quoted] at h
              rcases hk : takeQuoted cs with _ | ⟨b, r'⟩ <;> rw [hk] at h
              · simp at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hqb, hcs⟩ := takeQuoted_sound cs hk
              have hs : IsQuotedToken (String.ofList ('"' :: (b ++ ['"']))) :=
                ⟨b, by rw [String.toList_ofList], hqb⟩
              have hpre := LexesPre.quoted (rest := r') hs
              rw [String.toList_ofList] at hpre
              rw [hcs]
              simpa using hpre
            · by_cases hbc : IsBare c
              · rw [lexOne?_bare fuel hbc] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
                have happ := takeBare_append (c :: cs)
                have hbare := takeBare_bare (c :: cs)
                have hhead := takeBare_headNot (c :: cs)
                have hne : (takeBare (c :: cs)).1 ≠ [] := by
                  rw [takeBare_cons (isBareB_eq_true.mpr hbc)]; simp
                have ht : IsBareToken (String.ofList (takeBare (c :: cs)).1) := by
                  rw [IsBareToken, String.toList_ofList]
                  exact ⟨hne, hbare⟩
                have hpre := LexesPre.bare ht hhead
                rw [String.toList_ofList, happ] at hpre
                exact hpre
              · rw [lexOne?_reject fuel hbc hc hq] at h
                simp at h
      · intro l es r h
        obtain ⟨w, hw, hl⟩ := dropSpaces_split l
        rcases hd : dropSpaces l with _ | ⟨c, cs⟩ <;> rw [hd] at hl
        · rw [lexSeq?_succ_nil fuel hd] at h
          simp at h
        · rw [lexSeq?_succ_cons fuel hd] at h
          by_cases hc : c = ')'
          · subst hc
            rw [ite_eq_left (rfl : (')' : Char) = ')')] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            rw [hl]
            exact .nil hw
          · rw [ite_eq_right hc] at h
            rcases ho : lexOne? fuel (c :: cs) with _ | ⟨e, r₀⟩ <;> rw [ho] at h
            · simp at h
            rw [Option.bind_some] at h
            rcases hq : lexSeq? fuel r₀ with _ | ⟨es', r'⟩ <;> rw [hq] at h
            · simp at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [hl]
            exact .cons hw (ih1 ho) (ih2 hq)

/-- **Soundness of `lexOne?`.**  Whatever it reads is a spelling. -/
theorem lexOne?_sound {fuel : Nat} {l : List Char} {e : SExp} {r : List Char}
    (h : lexOne? fuel l = some (e, r)) : LexesPre l e r := (lex_sound fuel).1 h

/-- **Soundness of `lexSeq?`.**  Whatever it reads is a spelling of a child
list that stops at a closing parenthesis. -/
theorem lexSeq?_sound {fuel : Nat} {l : List Char} {es : List SExp} {r : List Char}
    (h : lexSeq? fuel l = some (es, r)) : LexesSeq l es (')' :: r) := (lex_sound fuel).2 h

/-! ## Completeness

Every derivation of the specification is found by the reader, provided the fuel
covers the input.  As with soundness the two halves go together, by induction
on the fuel; the inner case analysis is on the derivation, through the
inversion lemmas `LexesPre.inv` and `LexesSeq.inv` of `Lexical.lean`.  Each
case is the same two steps: invert the derivation, then check that the scanner
takes exactly the split the rule describes — which is what `takeBare_eq`,
`dropSpaces_eq` and `takeQuoted_complete` say. -/

/-- **Completeness**, both halves at once: induction on the fuel. -/
theorem lex_complete (fuel : Nat) :
    (∀ {l : List Char} {e : SExp} {r : List Char},
        LexesPre l e r → l.length ≤ fuel → lexOne? fuel l = some (e, r)) ∧
      (∀ {l : List Char} {es : List SExp} {tail : List Char},
        LexesSeq l es (')' :: tail) → l.length < fuel → lexSeq? fuel l = some (es, tail)) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro l e r h hlen
        obtain ⟨c, t, rfl, -, -⟩ := h.start
        simp at hlen
      · intro l es tail _ hlen
        omega
  | succ fuel ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · intro l e r h hlen
        rcases h.inv with ⟨s, hs, hnb, rfl, rfl⟩ | ⟨s, hs, rfl, rfl⟩ |
          ⟨t, es, body, ht, hnb, hseq, rfl, rfl⟩
        · obtain ⟨c, cs, hsl, hcb⟩ := hs.head
          have hb : takeBare (c :: (cs ++ r)) = (s.toList, r) := by
            rw [← List.cons_append, ← hsl]; exact takeBare_eq hs.2 hnb
          have hos : String.ofList s.toList = s := String.ofList_toList
          rw [hsl, List.cons_append, lexOne?_bare fuel hcb, hb, hos]
        · obtain ⟨b, hsl, hqb⟩ := hs
          have hsplit : s.toList ++ r = '"' :: (b ++ '"' :: r) := by rw [hsl]; simp
          have hos : String.ofList ('"' :: (b ++ ['"'])) = s := by
            rw [← hsl, String.ofList_toList]
          rw [hsplit, lexOne?_quoted, takeQuoted_complete hqb, Option.map_some, hos]
        · obtain ⟨tc, tcs, htl, -⟩ := ht.head
          have hb : takeBare (t.toList ++ body) = (tc :: tcs, body) := by
            rw [← htl]; exact takeBare_eq ht.2 hnb
          have hlen' : body.length < fuel := by
            simp only [List.length_cons, List.length_append] at hlen
            have : t.toList.length = tcs.length + 1 := by rw [htl]; simp
            omega
          have hot : String.ofList (tc :: tcs) = t := by rw [← htl, String.ofList_toList]
          rw [lexOne?_node fuel hb, ih2 hseq hlen', Option.map_some, hot]
      · intro l es tail h hlen
        rcases h.inv with ⟨w, rest, hw, rfl, rfl, heq⟩ |
          ⟨w, body, rest, e, es', hw, hpre, hseq, rfl, rfl⟩
        · simp only [List.cons.injEq, true_and] at heq
          subst heq
          have hd : dropSpaces (w ++ ')' :: tail) = ')' :: tail :=
            dropSpaces_eq hw (by exact not_isSpace_rparen)
          rw [lexSeq?_succ_cons fuel hd, ite_eq_left (rfl : (')' : Char) = ')')]
        · obtain ⟨c, cs, hbody, -, hne⟩ := hpre.start
          have hd : dropSpaces (w ++ body) = c :: cs := by
            rw [← hbody]; exact dropSpaces_eq hw hpre.headNot_isSpace
          have hlb : body.length ≤ fuel := by
            simp only [List.length_append] at hlen; omega
          have hlr : rest.length < fuel :=
            Nat.lt_of_lt_of_le (lexesPre_length_lt hpre) hlb
          rw [lexSeq?_succ_cons fuel hd, ite_eq_right hne, ← hbody,
            ih1 hpre hlb, Option.bind_some, ih2 hseq hlr, Option.map_some]

/-- **Completeness of `lexOne?`.**  Every spelling is read, given enough
fuel. -/
theorem lexOne?_complete {l : List Char} {e : SExp} {r : List Char} (h : LexesPre l e r)
    {fuel : Nat} (hlen : l.length ≤ fuel) : lexOne? fuel l = some (e, r) :=
  (lex_complete fuel).1 h hlen

/-- **Completeness of `lexSeq?`.**  Every spelling of a child list is read,
given enough fuel. -/
theorem lexSeq?_complete {l : List Char} {es : List SExp} {tail : List Char}
    (h : LexesSeq l es (')' :: tail)) {fuel : Nat} (hlen : l.length < fuel) :
    lexSeq? fuel l = some (es, tail) := (lex_complete fuel).2 h hlen

/-! ## Whole streams

`Backend_ast.Print.output_script` (`spectec/src/backend-ast/print.ml:235`)
emits one top-level S-expression per line and
`spectec/src/exe-spectec/main.ml:257` adds a final newline, so a stream is a
layout-separated sequence that may end in layout. -/

/-- Read a whole `--ast` stream: top-level S-expressions separated by layout,
with layout allowed at either end. -/
def lexStream? : Nat → List Char → Option (List SExp)
  | 0, _ => none
  | fuel + 1, l =>
      match dropSpaces l with
      | [] => some []
      | c :: cs =>
          (lexOne? fuel (c :: cs)).bind fun p => (lexStream? fuel p.2).map fun es => p.1 :: es

/-- `lexStream?` runs out of fuel. -/
@[simp] theorem lexStream?_zero (l : List Char) : lexStream? 0 l = none := rfl

/-- One unfolding step for `lexStream?`. -/
theorem lexStream?_succ (fuel : Nat) (l : List Char) :
    lexStream? (fuel + 1) l =
      (match dropSpaces l with
      | [] => some []
      | c :: cs =>
          (lexOne? fuel (c :: cs)).bind fun p =>
            (lexStream? fuel p.2).map fun es => p.1 :: es) := rfl

/-- A stream of nothing but layout is the empty stream. -/
theorem lexStream?_succ_nil (fuel : Nat) {l : List Char} (h : dropSpaces l = []) :
    lexStream? (fuel + 1) l = some [] := by rw [lexStream?_succ, h]

/-- One unfolding step for `lexStream?`, with the layout already skipped. -/
theorem lexStream?_succ_cons (fuel : Nat) {l : List Char} {c : Char} {cs : List Char}
    (h : dropSpaces l = c :: cs) :
    lexStream? (fuel + 1) l =
      (lexOne? fuel (c :: cs)).bind fun p =>
        (lexStream? fuel p.2).map fun es => p.1 :: es := by
  rw [lexStream?_succ, h]

/-- **Soundness of `lexStream?`.** -/
theorem lexStream?_sound : ∀ (fuel : Nat) {l : List Char} {es : List SExp},
    lexStream? fuel l = some es → LexesStream l es := by
  intro fuel
  induction fuel with
  | zero => intro l es h; simp at h
  | succ fuel ih =>
      intro l es h
      obtain ⟨w, hw, hl⟩ := dropSpaces_split l
      rcases hd : dropSpaces l with _ | ⟨c, cs⟩ <;> rw [hd] at hl
      · rw [lexStream?_succ_nil fuel hd] at h
        obtain rfl := Option.some.inj h
        rw [hl, List.append_nil]
        exact .nil hw
      · rw [lexStream?_succ_cons fuel hd] at h
        rcases ho : lexOne? fuel (c :: cs) with _ | ⟨e, r₀⟩ <;> rw [ho] at h
        · simp at h
        rw [Option.bind_some] at h
        rcases hq : lexStream? fuel r₀ with _ | es' <;> rw [hq] at h
        · simp at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rw [hl]
        exact .cons hw (lexOne?_sound ho) (ih hq)

/-- **Completeness of `lexStream?`.** -/
theorem lexStream?_complete {l : List Char} {es : List SExp} (h : LexesStream l es) :
    ∀ fuel : Nat, l.length < fuel → lexStream? fuel l = some es := by
  induction h with
  | @nil w hw =>
      intro fuel hlen
      cases fuel with
      | zero => omega
      | succ fuel => rw [lexStream?_succ_nil fuel (dropSpaces_eq_nil hw)]
  | @cons w body rest e es hw hpre _ ih =>
      intro fuel hlen
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨c, cs, hbody, -, -⟩ := hpre.start
          have hd : dropSpaces (w ++ body) = c :: cs := by
            rw [← hbody]; exact dropSpaces_eq hw hpre.headNot_isSpace
          have hlb : body.length ≤ fuel := by
            simp only [List.length_append] at hlen; omega
          have hlr : rest.length < fuel :=
            Nat.lt_of_lt_of_le (lexesPre_length_lt hpre) hlb
          rw [lexStream?_succ_cons fuel hd, ← hbody, lexOne?_complete hpre hlb,
            Option.bind_some, ih fuel hlr, Option.map_some]

/-- The verified reader: read a whole `--ast` stream from a character list.
`l.length + 1` is always enough fuel, by `lexStream?_complete`. -/
def lex? (l : List Char) : Option (List SExp) := lexStream? (l.length + 1) l

/-- **Soundness.**  Whatever `lex?` returns is spelled by its input. -/
theorem lex?_sound {l : List Char} {es : List SExp} (h : lex? l = some es) :
    LexesStream l es := lexStream?_sound _ h

/-- **Completeness.**  `lex?` reads every stream the convention admits. -/
theorem lex?_complete {l : List Char} {es : List SExp} (h : LexesStream l es) :
    lex? l = some es := lexStream?_complete h _ (Nat.lt_succ_self _)

/-- `lex?` returns the unique stream its input spells, or `none` when the input
spells nothing. -/
theorem lex?_eq_some_iff {l : List Char} {es : List SExp} :
    lex? l = some es ↔ LexesStream l es := ⟨lex?_sound, lex?_complete⟩

/-! ## One S-expression at a time

A stream that holds exactly one S-expression is the same thing as a `Lexes`
derivation: `LexesStream.cons` followed by `LexesStream.nil` is `Lexes.intro`,
because `LexesStream.nil` is exactly the trailing-layout condition. -/

/-- A one-element stream is a single S-expression surrounded by layout. -/
theorem lexesStream_singleton_iff {l : List Char} {e : SExp} :
    LexesStream l [e] ↔ Lexes l e := by
  constructor
  · intro h
    rcases h.inv with ⟨-, hnil⟩ | ⟨w, body, rest, e', es', hw, hpre, hs, rfl, hes⟩
    · exact absurd hnil (by simp)
    · simp only [List.cons.injEq] at hes
      obtain ⟨rfl, rfl⟩ := hes
      rcases hs.inv with ⟨hsp, -⟩ | hcon
      · exact .intro hw hsp hpre
      · obtain ⟨w', body', rest', e₂, es₂, hw', hpre', hs', hl', hcon⟩ := hcon
        simp at hcon
  · intro h
    obtain ⟨w, body, rest, hw, hrest, hpre, rfl⟩ := h.inv
    exact .cons hw hpre (.nil hrest)

/-- The one-element stream, as a partial function. -/
def theOne : List SExp → Option SExp
  | [e] => some e
  | _ => none

/-- `theOne` succeeds exactly on one-element streams. -/
theorem theOne_eq_some_iff {es : List SExp} {e : SExp} : theOne es = some e ↔ es = [e] := by
  match es with
  | [] => simp [theOne]
  | [e'] => simp [theOne]
  | _ :: _ :: _ => simp [theOne]

/-! ## The `String` wrapper and the `EncRel` consequences -/

/-- Read a whole `--ast` file.  This is the only declaration in this module
that mentions `String`, because `String.toList` is expensive to reduce in the
kernel (`docs/projects/spectec/README.md`). -/
def parseStream? (s : String) : Option (List SExp) := lex? s.toList

/-- Read a single S-expression, rejecting trailing input. -/
def parse? (s : String) : Option SExp := (parseStream? s).bind theOne

/-- `parse?` succeeds exactly when the stream holds one S-expression. -/
theorem parse?_eq_some_iff {s : String} {e : SExp} :
    parse? s = some e ↔ parseStream? s = some [e] := by
  rw [parse?, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨es, hes, he⟩
    rw [hes, theOne_eq_some_iff.mp he]
  · intro h
    exact ⟨[e], h, rfl⟩

/-- **`parseStream?` is a sound decoder for `streamRel`.** -/
theorem streamRel_decoderSound : streamRel.DecoderSound parseStream? :=
  fun _ _ h => lex?_sound h

/-- **`parseStream?` is a complete decoder for `streamRel`.** -/
theorem streamRel_decoderComplete : streamRel.DecoderComplete parseStream? :=
  fun _ _ h => lex?_complete h

/-- **The stream convention is exactly the graph of `parseStream?`.**  This is
the statement that `Lexical.lean` left open: the specification and the reader
are the same relation, so `streamRel` inherits every property of
`EncRel.ofDecoder`. -/
theorem streamRel_eq_ofDecoder : streamRel = EncRel.ofDecoder parseStream? := by
  ext s es
  exact ⟨fun h => streamRel_decoderComplete s es h, fun h => streamRel_decoderSound s es h⟩

/-- **`parse?` is a sound decoder for `lexicalRel`.** -/
theorem lexicalRel_decoderSound : lexicalRel.DecoderSound parse? := by
  intro s e h
  exact lexesStream_singleton_iff.mp (lex?_sound (parse?_eq_some_iff.mp h))

/-- **`parse?` is a complete decoder for `lexicalRel`.** -/
theorem lexicalRel_decoderComplete : lexicalRel.DecoderComplete parse? := by
  intro s e h
  exact parse?_eq_some_iff.mpr (lex?_complete (lexesStream_singleton_iff.mpr h))

/-- **The single-expression convention is exactly the graph of `parse?`.** -/
theorem lexicalRel_eq_ofDecoder : lexicalRel = EncRel.ofDecoder parse? := by
  ext s e
  exact ⟨fun h => lexicalRel_decoderComplete s e h, fun h => lexicalRel_decoderSound s e h⟩

/-- **Round trip.**  The exact contents of `spectec --ast -o FILE` are read
back as the list of definitions that produced them, at every `--ast-width`.
This composes `streamRel_astFile` (printer soundness, `Lexical.lean`) with
reader completeness. -/
theorem parseStream?_astFile (width : Nat) (es : List SExp) (h : PrintableList es) :
    parseStream? (astFile width es) = some es :=
  streamRel_decoderComplete _ _ (streamRel_astFile width es h)

/-! ## Worked examples

These are checked by kernel reduction, which is why the inputs are character
lists: `lex? s.toList` makes the kernel re-reduce `String.toList s` at every
recursive step, and that is exponential in the length of `s`.  One `String`
example is kept, deliberately tiny. -/

/-- The empty input is the empty stream, not an empty atom. -/
example : lex? [] = some [] := by rfl

/-- A bare atom. -/
example : lex? ['a', 'b'] = some [.atom "ab"] := by rfl

/-- A node, whose tag abuts the opening parenthesis
(`spectec/src/util/sexpr.ml:23`). -/
example : lex? ['(', 'a', ' ', 'b', ')'] = some [.node "a" [.atom "b"]] := by rfl

/-- Layout is free: leading spaces and the trailing newline that
`spectec/src/exe-spectec/main.ml:257` adds change nothing. -/
example : lex? [' ', '(', 'a', ' ', 'b', ')', '\n'] = some [.node "a" [.atom "b"]] := by rfl

/-- Nesting, and a node with no children. -/
example : lex? ['(', 'a', ' ', '(', 'b', ')', ')'] = some [.node "a" [.node "b" []]] := by rfl

/-- A quoted atom containing a space and an escaped quotation mark; its stored
spelling includes the delimiters (`spectec/src/backend-ast/print.ml:12`). -/
example : lex? ['"', 'a', ' ', 'b', '\\', '"', 'c', '"'] =
    some [.atom "\"a b\\\"c\""] := by rfl

/-- The same thing by `decide`, through `SExp.decEq`. -/
example : lex? ['(', 'a', ')'] = some [.node "a" []] := by decide

/-- Rejected: an unclosed node. -/
example : lex? ['(', 'a'] = none := by rfl

/-- Rejected: a closing parenthesis with no node to close. -/
example : lex? ['a', ')'] = none := by rfl

/-- Rejected: a space between `(` and the tag. -/
example : lex? ['(', ' ', 'a', ')'] = none := by rfl

/-- Rejected: an empty bare atom, here as a node with no tag. -/
example : lex? ['(', ')'] = none := by rfl

/-- Rejected: an unterminated string. -/
example : lex? ['"', 'a', 'b'] = none := by rfl

/-- The `String` wrapper, on an input short enough for the kernel. -/
example : parseStream? "(a)" = some [.node "a" []] := by rfl

end Silmaril.SpecTec.SExp

