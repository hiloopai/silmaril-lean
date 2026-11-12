module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Printer
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Escape
public import Silmaril.Encoding.Lattice

/-!
# The lexical convention of the `--ast` stream

`Util.Sexpr` (`spectec/src/util/sexpr.ml`) has a printer but no reader, so the
lexical convention of a `spectec --ast` file exists only implicitly, in the
shape of what `pp` emits.  This module writes it down as an encoding relation
`lexicalRel : EncRel String SExp` (and `streamRel` for a whole file) and places
it in the lattice of `Silmaril.Encoding.Lattice`.  It is a *specification*: a
verified byte parser is deliberately not in scope, and no decoder is defined
here.

## The convention

A token is `(`, `)`, or an atom; the only layout characters are `' '` and
`'\n'` (`spectec/src/util/sexpr.ml:21-22`), and any run of them is accepted
between tokens, so one relation covers every `--ast-width` setting.

* A **bare** token is a nonempty maximal run of characters other than `' '`,
  `'\n'`, `(`, `)` and `"` (`IsBare`, `IsBareToken`).
* A **quoted** token is `"`, an OCaml-escaped body, `"` (`QuotedBody`,
  `IsQuotedToken`).  Quoting is significant to the lexer because an escaped
  body may contain spaces.  The atom that `--ast` stores already *contains* the
  quotation marks — `let text t = Atom ("\"" ^ String.escaped t ^ "\"")`
  (`spectec/src/backend-ast/print.ml:11`) — so the relation maps a quoted token
  to the atom spelled by exactly those characters, and
  `Silmaril.SpecTec.Escape` is what interprets the body afterwards.
* A **node** is `(`, a bare token, the children, `)`.  The printer emits
  `"(" ^+ s` with no space in between (`spectec/src/util/sexpr.ml:23`), so a
  tag is lexed exactly like a bare atom but must follow the `(` directly.

Maximal munch is built into the rules: `LexesPre.bare` and `LexesPre.node`
require the next character not to be bare, and `QuotedBody.split` shows that a
quoted token ends at its first unescaped `"`.  `lexicalRel_functional` is the
main theorem: one string spells at most one S-expression.

## The empty atom

The relation does **not** accept an empty bare atom, and therefore
`SExp.Printable` excludes `SExp.atom ""`.  Printing one loses it altogether:
`Atom ""` contributes no characters and lexes as nothing at all
(`not_lexicalRel_empty`, `render_atom_empty`).

`Backend_ast.Print` has one source of it: `def` on a `HintD`
(`spectec/src/backend-ast/print.ml:218-219`).  `Backend_ast.Print.script`
filters such atoms out at the top level
(`spectec/src/backend-ast/print.ml:225`) but `RecD` does not
(`spectec/src/backend-ast/print.ml:216`), so a hint inside a recursion group
would survive.  The Lean transcription of the IL has a *second* source, which
the OCaml does not: `IL.Num.realN` stores an unchecked `String` that `numS`
emits as a bare atom (`spectec/src/backend-ast/print.ml:20`), so
`IL.defS` applied to a definition containing `Num.realN ""` prints
`(real )`.  No OCaml value can be that one — the payload comes from
`Printf.sprintf "%.17g"` (`spectec/src/xl/num.ml:25`), which never returns the
empty string — and it is the one point at which the Lean type is strictly
larger than the image of `il/ast.ml` under the printer's erasure; see
`Silmaril/SpecTec/IL/Ast.lean` and the side condition
`AllToken (realsScript s)` of `Silmaril/SpecTec/IL/Printable.lean`, which
rules exactly that out.

No stream at the pinned revision contains an empty atom: the three files in
`specs/spectec/` lex with no empty atom and re-print byte-for-byte at
`--ast-width 80`.

## Relation to the other S-expression conventions in this library

`Silmaril/Formats/SExp/` has a total Lisp-style parser
(`Silmaril.Formats.SExpParser`, in `Parser.lean`) and the canonical
Rivest/Eastlake byte encoding (`Rivest.lean`), and `Silmaril/Wasm/Wat/Lexer.lean`
has the WAT lexer used by the quotation elaborator.  Neither of those is
phrased as an `EncRel`, and there is no `Silmaril/Formats/SExp/Wat.lean` or
`Silmaril/Formats/SExp/Scheme.lean` at the time of writing, so the formal
comparison — WAT comments and `$`-identifiers, Scheme's `#` syntax and dotted
pairs, versus the convention here, which has no comment syntax and no dotted
pairs and whose node head is a string rather than an expression — is stated
in the last section of this file as prose, with the few character-class facts
that distinguish the three conventions proved, and left as future work rather
than invented here.
-/

@[expose] public section

namespace Silmaril.SpecTec

/-! ## Character classes -/

/-- The two layout characters that `Util.Sexpr.pp` emits
(`spectec/src/util/sexpr.ml:21-22`): the flat separator `" "` and the broken
separator `"\n" ^ String.make off ' '`. -/
def IsSpace (c : Char) : Prop := c = ' ' ∨ c = '\n'

instance (c : Char) : Decidable (IsSpace c) := by unfold IsSpace; infer_instance

/-- A character that may occur inside a bare (unquoted) token: anything that is
neither layout, nor a parenthesis, nor the quotation mark that opens a quoted
token. -/
def IsBare (c : Char) : Prop := ¬ IsSpace c ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '"'

instance (c : Char) : Decidable (IsBare c) := by unfold IsBare; infer_instance

/-- Bare characters are not layout. -/
theorem IsBare.not_isSpace {c : Char} (h : IsBare c) : ¬ IsSpace c := h.1

/-- Layout characters are not bare. -/
theorem not_isBare_of_isSpace {c : Char} (h : IsSpace c) : ¬ IsBare c := fun hb => hb.1 h

/-- `'('` is not bare. -/
theorem not_isBare_lparen : ¬ IsBare '(' := fun h => h.2.1 rfl

/-- `')'` is not bare. -/
theorem not_isBare_rparen : ¬ IsBare ')' := fun h => h.2.2.1 rfl

/-- `'"'` is not bare. -/
theorem not_isBare_quote : ¬ IsBare '"' := fun h => h.2.2.2 rfl

/-- `'('` is not layout. -/
theorem not_isSpace_lparen : ¬ IsSpace '(' := by decide

/-- `')'` is not layout. -/
theorem not_isSpace_rparen : ¬ IsSpace ')' := by decide

/-- `'"'` is not layout. -/
theorem not_isSpace_quote : ¬ IsSpace '"' := by decide

/-! ## Runs of characters -/

/-- A (possibly empty) run of layout characters. -/
def Spaces (l : List Char) : Prop := ∀ c ∈ l, IsSpace c

/-- `l` does not begin with a character satisfying `P`; vacuously true for the
empty list.  This is how maximal munch is expressed below. -/
def HeadNot (P : Char → Prop) : List Char → Prop
  | [] => True
  | c :: _ => ¬ P c

instance (P : Char → Prop) [DecidablePred P] (l : List Char) :
    Decidable (HeadNot P l) := by
  cases l <;> (unfold HeadNot; infer_instance)

instance (l : List Char) : Decidable (Spaces l) := by unfold Spaces; infer_instance

/-- The empty run. -/
@[simp] theorem spaces_nil : Spaces [] := by simp [Spaces]

/-- `Spaces` is closed under concatenation. -/
theorem Spaces.append {a b : List Char} (ha : Spaces a) (hb : Spaces b) :
    Spaces (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h
  · exact hb c h

/-- Prefixing a layout run cannot create a `P`-initial string when `P` excludes
layout. -/
theorem Spaces.headNot {P : Char → Prop} (hP : ∀ c, IsSpace c → ¬ P c)
    {a b : List Char} (ha : Spaces a) (hb : HeadNot P b) : HeadNot P (a ++ b) := by
  cases a with
  | nil => exact hb
  | cons c _ => exact hP c (ha c (List.mem_cons_self ..))

/-- A nonempty layout run blocks any `P`-initial reading, when `P` excludes
layout. -/
theorem Spaces.headNot_of_ne_nil {P : Char → Prop} (hP : ∀ c, IsSpace c → ¬ P c)
    {a : List Char} (ha : Spaces a) (hne : a ≠ []) (b : List Char) : HeadNot P (a ++ b) := by
  cases a with
  | nil => exact absurd rfl hne
  | cons c _ => exact hP c (ha c (List.mem_cons_self ..))

/-- Maximal munch, as a splitting principle: a maximal run of `P`-characters is
determined by the string it starts. -/
theorem run_split {P : Char → Prop} {w₁ w₂ r₁ r₂ : List Char}
    (h₁ : ∀ c ∈ w₁, P c) (h₂ : ∀ c ∈ w₂, P c)
    (hr₁ : HeadNot P r₁) (hr₂ : HeadNot P r₂)
    (h : w₁ ++ r₁ = w₂ ++ r₂) : w₁ = w₂ ∧ r₁ = r₂ := by
  induction w₁ generalizing w₂ with
  | nil =>
      cases w₂ with
      | nil => exact ⟨rfl, by simpa using h⟩
      | cons b w =>
          rw [List.nil_append, List.cons_append] at h
          subst h
          exact absurd (h₂ b (List.mem_cons_self ..)) hr₁
  | cons a w ih =>
      cases w₂ with
      | nil =>
          rw [List.nil_append, List.cons_append] at h
          subst h
          exact absurd (h₁ a (List.mem_cons_self ..)) hr₂
      | cons b w' =>
          rw [List.cons_append, List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨rfl, rfl⟩ :=
            ih (fun c hc => h₁ c (List.mem_cons_of_mem _ hc))
              (fun c hc => h₂ c (List.mem_cons_of_mem _ hc)) h
          exact ⟨rfl, rfl⟩

/-! ## Tokens -/

/-- The body of a quoted token: the characters between the two delimiting
quotation marks, scanned the way `String.escaped`
(`Silmaril.SpecTec.Escape.escape`) writes them.  A backslash always consumes
the character after it, so `\"` does not end the token; every other character
is literal and therefore different from `'"'`. -/
inductive QuotedBody : List Char → Prop where
  /-- The empty body. -/
  | nil : QuotedBody []
  /-- A two-character escape `\c`, for any `c`. -/
  | esc (c : Char) {cs : List Char} : QuotedBody cs → QuotedBody ('\\' :: c :: cs)
  /-- A literal character, which is neither the delimiter nor a backslash. -/
  | lit {c : Char} {cs : List Char} (h₁ : c ≠ '"') (h₂ : c ≠ '\\') :
      QuotedBody cs → QuotedBody (c :: cs)

/-- Decision procedure for `QuotedBody`. -/
def quotedBodyB : List Char → Bool
  | [] => true
  | c :: cs =>
      if c = '\\' then
        match cs with
        | [] => false
        | _ :: cs' => quotedBodyB cs'
      else c != '"' && quotedBodyB cs

/-- `quotedBodyB` on the empty body. -/
@[simp] theorem quotedBodyB_nil : quotedBodyB [] = true := rfl

/-- `quotedBodyB` skips a two-character escape. -/
@[simp] theorem quotedBodyB_esc (c : Char) (cs : List Char) :
    quotedBodyB ('\\' :: c :: cs) = quotedBodyB cs := by simp [quotedBodyB]

/-- `quotedBodyB` on a literal character. -/
theorem quotedBodyB_lit {c : Char} (h : ¬ c = '\\') (cs : List Char) :
    quotedBodyB (c :: cs) = (c != '"' && quotedBodyB cs) := by
  conv_lhs => rw [quotedBodyB.eq_def]
  simp [h]

/-- A dangling backslash is not a body. -/
theorem quotedBodyB_backslash : quotedBodyB ['\\'] = false := by decide

/-- `quotedBodyB` decides `QuotedBody`. -/
theorem quotedBodyB_eq_true_iff (cs : List Char) :
    quotedBodyB cs = true ↔ QuotedBody cs := by
  constructor
  · induction cs using quotedBodyB.induct with
    | case1 => exact fun _ => .nil
    | case2 => exact fun hb => absurd (quotedBodyB_backslash ▸ hb) (by decide)
    | case3 c cs ih => exact fun hb => .esc _ (ih ((quotedBodyB_esc c cs).symm.trans hb))
    | case4 c cs h ih =>
        intro hb
        rw [quotedBodyB_lit h] at hb
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
        exact .lit hb.1 h (ih hb.2)
  · intro h
    induction h with
    | nil => rfl
    | esc c _ ih => simpa using ih
    | lit h₁ h₂ _ ih => simp [quotedBodyB_lit h₂, h₁, ih]

instance (cs : List Char) : Decidable (QuotedBody cs) :=
  decidable_of_iff _ (quotedBodyB_eq_true_iff cs)

/-- Maximal munch for quoted tokens: a quoted body is terminated by the first
quotation mark that is not part of an escape, so the body and the remainder are
determined by the concatenation. -/
theorem QuotedBody.split {a b r r' : List Char} (ha : QuotedBody a) (hb : QuotedBody b)
    (h : a ++ '"' :: r = b ++ '"' :: r') : a = b ∧ r = r' := by
  induction ha generalizing b r r' with
  | nil =>
      cases hb with
      | nil => exact ⟨rfl, by simpa using h⟩
      | esc => exact absurd h (by simp)
      | lit h₁ _ _ =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact absurd h.1.symm h₁
  | esc c _ ih =>
      cases hb with
      | nil => exact absurd h (by simp)
      | esc c' hcs' =>
          simp only [List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨rfl, rfl⟩ := ih hcs' h
          exact ⟨rfl, rfl⟩
      | lit _ h₂ _ =>
          simp only [List.cons_append, List.cons.injEq] at h
          exact absurd h.1.symm h₂
  | lit h₁ h₂ _ ih =>
      cases hb with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact absurd h.1 h₁
      | esc =>
          simp only [List.cons_append, List.cons.injEq] at h
          exact absurd h.1 h₂
      | lit _ _ hcs' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨rfl, rfl⟩ := ih hcs' h
          exact ⟨rfl, rfl⟩

/-- A bare token: a nonempty string of bare characters. -/
def IsBareToken (s : String) : Prop := s.toList ≠ [] ∧ ∀ c ∈ s.toList, IsBare c

instance (s : String) : Decidable (IsBareToken s) := by unfold IsBareToken; infer_instance

/-- A quoted token: `"`, an escaped body, `"`.  Note that the atoms the
`--ast` backend builds for identifiers and texts *contain* the quotation marks
(`let text t = Atom ("\"" ^ String.escaped t ^ "\"")`,
`spectec/src/backend-ast/print.ml:11`), so this is a predicate on the atom's
own string. -/
def IsQuotedToken (s : String) : Prop :=
  ∃ body, s.toList = '"' :: (body ++ ['"']) ∧ QuotedBody body

/-- Decision procedure for `IsQuotedToken`. -/
def isQuotedTokenB (l : List Char) : Bool :=
  match l with
  | '"' :: rest =>
      match rest.reverse with
      | '"' :: body => quotedBodyB body.reverse
      | _ => false
  | _ => false

/-- `isQuotedTokenB` decides `IsQuotedToken`. -/
theorem isQuotedTokenB_eq_true_iff (s : String) :
    isQuotedTokenB s.toList = true ↔ IsQuotedToken s := by
  constructor
  · intro h
    unfold isQuotedTokenB at h
    split at h
    · next rest heq =>
        split at h
        · next body hrev =>
            refine ⟨body.reverse, ?_, (quotedBodyB_eq_true_iff _).mp h⟩
            rw [heq, ← List.reverse_reverse rest, hrev]
            simp
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro ⟨body, hs, hb⟩
    rw [hs]
    unfold isQuotedTokenB
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.reverse_reverse]
    exact (quotedBodyB_eq_true_iff _).mpr hb

instance (s : String) : Decidable (IsQuotedToken s) :=
  decidable_of_iff _ (isQuotedTokenB_eq_true_iff s)

/-- A token: either a bare token or a quoted token.  This is exactly what the
lexer accepts in place of an `Atom`. -/
def IsToken (s : String) : Prop := IsBareToken s ∨ IsQuotedToken s

instance (s : String) : Decidable (IsToken s) := by unfold IsToken; infer_instance

/-- A bare token begins with a bare character. -/
theorem IsBareToken.headNot_not {s : String} (h : IsBareToken s) :
    ¬ HeadNot IsBare s.toList := by
  cases hl : s.toList with
  | nil => exact absurd hl h.1
  | cons c cs => exact fun hn => hn (h.2 c (hl ▸ List.mem_cons_self ..))

/-- A quoted token begins with `'"'`. -/
theorem IsQuotedToken.head {s : String} (h : IsQuotedToken s) :
    ∃ t, s.toList = '"' :: t := by
  obtain ⟨body, hs, -⟩ := h
  exact ⟨body ++ ['"'], hs⟩

/-! ## The grammar -/

mutual

/-- `LexesPre l e r`: the character list `l` begins with a spelling of the
S-expression `e` and `r` is what is left over.

The three rules are the three tokens of the convention.  `bare` and `node`
carry maximal-munch side conditions (`HeadNot IsBare`): a bare token runs to
the first character that cannot occur in one, and a node's tag is lexed exactly
like a bare atom but must follow the `(` immediately, as
`"(" ^+ s` (`spectec/src/util/sexpr.ml:23`) prints it. -/
inductive LexesPre : List Char → SExp → List Char → Prop where
  /-- A bare atom: a maximal nonempty run of bare characters. -/
  | bare {s : String} {rest : List Char} :
      IsBareToken s → HeadNot IsBare rest → LexesPre (s.toList ++ rest) (.atom s) rest
  /-- A quoted atom.  Its stored value includes the quotation marks. -/
  | quoted {s : String} {rest : List Char} :
      IsQuotedToken s → LexesPre (s.toList ++ rest) (.atom s) rest
  /-- A node: `(`, the tag, the children, `)`. -/
  | node {t : String} {es : List SExp} {body rest : List Char} :
      IsBareToken t → HeadNot IsBare body → LexesSeq body es (')' :: rest) →
      LexesPre ('(' :: (t.toList ++ body)) (.node t es) rest

/-- `LexesSeq l es r`: `l` begins with the children `es` of a node, each
preceded by a (possibly empty) layout run, and runs up to the closing
parenthesis, which is the first character of `r`. -/
inductive LexesSeq : List Char → List SExp → List Char → Prop where
  /-- The end of the children: layout, then the closing parenthesis. -/
  | nil {w rest : List Char} : Spaces w → LexesSeq (w ++ ')' :: rest) [] (')' :: rest)
  /-- One more child, preceded by a layout run. -/
  | cons {w body rest rest' : List Char} {e : SExp} {es : List SExp} :
      Spaces w → LexesPre body e rest → LexesSeq rest es rest' →
      LexesSeq (w ++ body) (e :: es) rest'

end

/-- A bare token starts with a bare character. -/
theorem IsBareToken.head {s : String} (h : IsBareToken s) :
    ∃ c cs, s.toList = c :: cs ∧ IsBare c := by
  cases hl : s.toList with
  | nil => exact absurd hl h.1
  | cons c cs => exact ⟨c, cs, rfl, h.2 c (hl ▸ List.mem_cons_self ..)⟩

/-- Every spelling of an S-expression starts with a character that is neither
layout nor a closing parenthesis.  This is what tells the two `LexesSeq` rules
apart. -/
theorem LexesPre.start {l : List Char} {e : SExp} {r : List Char} (h : LexesPre l e r) :
    ∃ c t, l = c :: t ∧ ¬ IsSpace c ∧ c ≠ ')' := by
  cases h with
  | bare hs _ =>
      obtain ⟨c, cs, hl, hb⟩ := hs.head
      exact ⟨c, cs ++ r, by rw [hl]; rfl, hb.1, hb.2.2.1⟩
  | quoted hs =>
      obtain ⟨t, hl⟩ := hs.head
      exact ⟨'"', t ++ r, by rw [hl]; rfl, not_isSpace_quote, by decide⟩
  | node => exact ⟨'(', _, rfl, not_isSpace_lparen, by decide⟩

/-- A spelling never begins with layout. -/
theorem LexesPre.headNot_isSpace {l : List Char} {e : SExp} {r : List Char}
    (h : LexesPre l e r) : HeadNot IsSpace l := by
  obtain ⟨c, t, rfl, hc, -⟩ := h.start
  exact hc

/-- Inversion for `LexesPre`, in a form that can be used after the goal's
indices have been specialized. -/
theorem LexesPre.inv {l : List Char} {e : SExp} {r : List Char} (h : LexesPre l e r) :
    (∃ s, IsBareToken s ∧ HeadNot IsBare r ∧ l = s.toList ++ r ∧ e = .atom s) ∨
      (∃ s, IsQuotedToken s ∧ l = s.toList ++ r ∧ e = .atom s) ∨
      (∃ t es body, IsBareToken t ∧ HeadNot IsBare body ∧ LexesSeq body es (')' :: r) ∧
        l = '(' :: (t.toList ++ body) ∧ e = .node t es) := by
  cases h with
  | bare hs hnb => exact Or.inl ⟨_, hs, hnb, rfl, rfl⟩
  | quoted hs => exact Or.inr (Or.inl ⟨_, hs, rfl, rfl⟩)
  | node ht hnb hseq => exact Or.inr (Or.inr ⟨_, _, _, ht, hnb, hseq, rfl, rfl⟩)

/-- Inversion for `LexesSeq`. -/
theorem LexesSeq.inv {l : List Char} {es : List SExp} {r : List Char} (h : LexesSeq l es r) :
    (∃ w rest, Spaces w ∧ l = w ++ ')' :: rest ∧ es = [] ∧ r = ')' :: rest) ∨
      (∃ w body rest e es', Spaces w ∧ LexesPre body e rest ∧ LexesSeq rest es' r ∧
        l = w ++ body ∧ es = e :: es') := by
  cases h with
  | nil hw => exact Or.inl ⟨_, _, hw, rfl, rfl, rfl⟩
  | cons hw hpre hseq => exact Or.inr ⟨_, _, _, _, _, hw, hpre, hseq, rfl, rfl⟩

mutual

/-- One character list spells at most one S-expression, with one remainder.
This is maximal munch: the `HeadNot IsBare` side conditions of `LexesPre.bare`
and `LexesPre.node` pin down where a bare token ends, and `QuotedBody.split`
pins down where a quoted token ends. -/
theorem LexesPre.det {l : List Char} {e e' : SExp} {r r' : List Char}
    (h : LexesPre l e r) (h' : LexesPre l e' r') : e = e' ∧ r = r' := by
  match h with
  | @LexesPre.bare s rest hs hnb =>
      rcases h'.inv with ⟨s₂, hs₂, hnb₂, heq, rfl⟩ | ⟨s₂, hs₂, heq, rfl⟩ |
        ⟨t₂, es₂, body₂, -, -, -, heq, rfl⟩
      · obtain ⟨hl, rfl⟩ := run_split hs.2 hs₂.2 hnb hnb₂ heq
        exact ⟨congrArg SExp.atom (String.toList_inj.mp hl), rfl⟩
      · obtain ⟨c, cs, hl, hb⟩ := hs.head
        obtain ⟨t₂, hl₂⟩ := hs₂.head
        rw [hl, hl₂] at heq
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd (heq.1 ▸ hb) not_isBare_quote
      · obtain ⟨c, cs, hl, hb⟩ := hs.head
        rw [hl] at heq
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd (heq.1 ▸ hb) not_isBare_lparen
  | @LexesPre.quoted s rest hs =>
      rcases h'.inv with ⟨s₂, hs₂, -, heq, rfl⟩ | ⟨s₂, hs₂, heq, rfl⟩ |
        ⟨t₂, es₂, body₂, -, -, -, heq, rfl⟩
      · obtain ⟨c, cs, hl₂, hb⟩ := hs₂.head
        obtain ⟨t, hl⟩ := hs.head
        rw [hl, hl₂] at heq
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd (heq.1.symm ▸ hb) not_isBare_quote
      · obtain ⟨body, hl, hq⟩ := hs
        obtain ⟨body₂, hl₂, hq₂⟩ := hs₂
        rw [hl, hl₂] at heq
        simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at heq
        obtain ⟨rfl, rfl⟩ := hq.split hq₂ heq
        exact ⟨congrArg SExp.atom (String.toList_inj.mp (hl.trans hl₂.symm)), rfl⟩
      · obtain ⟨t, hl⟩ := hs.head
        rw [hl] at heq
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd heq.1 (by decide)
  | @LexesPre.node t es body rest ht hnb hseq =>
      rcases h'.inv with ⟨s₂, hs₂, -, heq, rfl⟩ | ⟨s₂, hs₂, heq, rfl⟩ |
        ⟨t₂, es₂, body₂, ht₂, hnb₂, hseq₂, heq, rfl⟩
      · obtain ⟨c, cs, hl₂, hb⟩ := hs₂.head
        rw [hl₂] at heq
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd (heq.1.symm ▸ hb) not_isBare_lparen
      · obtain ⟨t₂, hl₂⟩ := hs₂.head
        rw [hl₂] at heq
        simp only [List.cons_append, List.cons.injEq] at heq
        exact absurd heq.1.symm (by decide)
      · simp only [List.cons.injEq, true_and] at heq
        obtain ⟨hl, rfl⟩ := run_split ht.2 ht₂.2 hnb hnb₂ heq
        obtain rfl := String.toList_inj.mp hl
        obtain ⟨rfl, hr⟩ := @LexesSeq.det _ _ _ _ _ hseq hseq₂
        exact ⟨rfl, (List.cons.injEq .. ▸ hr).2⟩

/-- One character list spells at most one sequence of children. -/
theorem LexesSeq.det {l : List Char} {es es' : List SExp} {r r' : List Char}
    (h : LexesSeq l es r) (h' : LexesSeq l es' r') : es = es' ∧ r = r' := by
  match h with
  | @LexesSeq.nil w rest hw =>
      rcases h'.inv with ⟨w₂, rest₂, hw₂, heq, rfl, rfl⟩ |
        ⟨w₂, body₂, rest₂, e₂, es₂, hw₂, hpre₂, -, heq, rfl⟩
      · obtain ⟨-, hr⟩ := run_split hw hw₂ (by exact not_isSpace_rparen)
          (by exact not_isSpace_rparen) heq
        exact ⟨rfl, hr⟩
      · obtain ⟨-, rfl⟩ := run_split hw hw₂ (by exact not_isSpace_rparen)
          hpre₂.headNot_isSpace heq
        obtain ⟨c, t, hc, -, hne⟩ := hpre₂.start
        exact absurd (List.cons.injEq .. ▸ hc).1.symm hne
  | @LexesSeq.cons w body rest rest' e es₀ hw hpre hseq =>
      rcases h'.inv with ⟨w₂, rest₂, hw₂, heq, rfl, rfl⟩ |
        ⟨w₂, body₂, rest₂, e₂, es₂, hw₂, hpre₂, hseq₂, heq, rfl⟩
      · obtain ⟨-, rfl⟩ := run_split hw hw₂ hpre.headNot_isSpace
          (by exact not_isSpace_rparen) heq
        obtain ⟨c, t, hc, -, hne⟩ := hpre.start
        exact absurd (List.cons.injEq .. ▸ hc).1.symm hne
      · obtain ⟨-, rfl⟩ := run_split hw hw₂ hpre.headNot_isSpace hpre₂.headNot_isSpace heq
        obtain ⟨rfl, rfl⟩ := @LexesPre.det _ _ _ _ _ hpre hpre₂
        obtain ⟨rfl, rfl⟩ := @LexesSeq.det _ _ _ _ _ hseq hseq₂
        exact ⟨rfl, rfl⟩

end

/-! ## The encoding relations -/

/-- A layout run cannot contain a spelling. -/
theorem LexesPre.not_spaces {l : List Char} {e : SExp} {r : List Char} (h : LexesPre l e r)
    {w : List Char} (hw : Spaces (w ++ l)) : False := by
  obtain ⟨c, t, rfl, hc, -⟩ := h.start
  exact hc (hw c (by simp))

/-- One S-expression, surrounded by optional layout: the carrier side of
`lexicalRel`. -/
inductive Lexes : List Char → SExp → Prop where
  /-- Leading layout, the expression, trailing layout. -/
  | intro {w body rest : List Char} {e : SExp} :
      Spaces w → Spaces rest → LexesPre body e rest → Lexes (w ++ body) e

/-- A whole `--ast` file: a layout-separated sequence of top-level
S-expressions.  `Backend_ast.Print.output_script`
(`spectec/src/backend-ast/print.ml:236`) emits one per line, and
`spectec/src/exe-spectec/main.ml:255` adds a final newline, so the trailing
layout run matters. -/
inductive LexesStream : List Char → List SExp → Prop where
  /-- The end of the stream: nothing but layout left. -/
  | nil {w : List Char} : Spaces w → LexesStream w []
  /-- One more top-level expression, preceded by a layout run. -/
  | cons {w body rest : List Char} {e : SExp} {es : List SExp} :
      Spaces w → LexesPre body e rest → LexesStream rest es →
      LexesStream (w ++ body) (e :: es)

/-- Inversion for `Lexes`. -/
theorem Lexes.inv {l : List Char} {e : SExp} (h : Lexes l e) :
    ∃ w body rest, Spaces w ∧ Spaces rest ∧ LexesPre body e rest ∧ l = w ++ body := by
  cases h with
  | intro hw hrest hpre => exact ⟨_, _, _, hw, hrest, hpre, rfl⟩

/-- Inversion for `LexesStream`. -/
theorem LexesStream.inv {l : List Char} {es : List SExp} (h : LexesStream l es) :
    (Spaces l ∧ es = []) ∨
      (∃ w body rest e es', Spaces w ∧ LexesPre body e rest ∧ LexesStream rest es' ∧
        l = w ++ body ∧ es = e :: es') := by
  cases h with
  | nil hw => exact Or.inl ⟨hw, rfl⟩
  | cons hw hpre hs => exact Or.inr ⟨_, _, _, _, _, hw, hpre, hs, rfl, rfl⟩

/-- One character list spells at most one S-expression. -/
theorem Lexes.det {l : List Char} {e e' : SExp} (h : Lexes l e) (h' : Lexes l e') : e = e' := by
  obtain ⟨w, body, rest, hw, -, hpre, rfl⟩ := h.inv
  obtain ⟨w₂, body₂, rest₂, hw₂, -, hpre₂, heq⟩ := h'.inv
  obtain ⟨-, rfl⟩ := run_split hw hw₂ hpre.headNot_isSpace hpre₂.headNot_isSpace heq
  exact (LexesPre.det hpre hpre₂).1

/-- One character list spells at most one stream. -/
theorem LexesStream.det {l : List Char} {es : List SExp} (h : LexesStream l es) :
    ∀ {es' : List SExp}, LexesStream l es' → es = es' := by
  induction h with
  | nil hw =>
      intro es' h'
      rcases h'.inv with ⟨-, rfl⟩ | ⟨w₂, body₂, rest₂, e₂, es₂, -, hpre₂, -, rfl, -⟩
      · rfl
      · exact (hpre₂.not_spaces hw).elim
  | @cons w body rest e es₀ hw hpre _ ih =>
      intro es' h'
      rcases h'.inv with ⟨hsp, rfl⟩ | ⟨w₂, body₂, rest₂, e₂, es₂, hw₂, hpre₂, hs₂, heq, rfl⟩
      · exact (hpre.not_spaces hsp).elim
      · obtain ⟨-, rfl⟩ := run_split hw hw₂ hpre.headNot_isSpace hpre₂.headNot_isSpace heq
        obtain ⟨rfl, rfl⟩ := LexesPre.det hpre hpre₂
        exact congrArg _ (ih hs₂)

/-- SpecTec's `--ast` lexical convention, as an encoding of one S-expression
in Unicode text. -/
def lexicalRel : EncRel String SExp := fun s e => Lexes s.toList e

/-- The same convention for a whole `--ast` file. -/
def streamRel : EncRel String (List SExp) := fun s es => LexesStream s.toList es

/-- **Main theorem.**  The convention is unambiguous: one string spells at most
one S-expression. -/
theorem lexicalRel_functional : lexicalRel.Functional := fun _ _ _ h h' => h.det h'

/-- A whole `--ast` file determines its sequence of definitions. -/
theorem streamRel_functional : streamRel.Functional := fun _ _ _ h h' => h.det h'

/-! ## Printable S-expressions -/

namespace Rope

/-- `flattens` is a monoid homomorphism from `List Rope` to `String`. -/
theorem flattens_append : ∀ (a b : List Rope), flattens (a ++ b) = flattens a ++ flattens b
  | [], b => by simp
  | r :: a, b => by simp [flattens_append a b, String.append_assoc]

end Rope

namespace SExp

mutual

/-- The S-expressions whose layout the lexer reads back: every atom is a
well-formed token and every tag is a bare token.  `Util.Sexpr.pp` is injective
on these; see the module docstring for the one atom it is not injective on. -/
def Printable : SExp → Prop
  | .atom s => IsToken s
  | .node t cs => IsBareToken t ∧ PrintableList cs

/-- `Printable` on a list of children. -/
def PrintableList : List SExp → Prop
  | [] => True
  | c :: cs => Printable c ∧ PrintableList cs

end

/-- `Printable` on an atom. -/
@[simp] theorem printable_atom (s : String) : Printable (.atom s) = IsToken s := rfl

/-- `Printable` on a node. -/
@[simp] theorem printable_node (t : String) (cs : List SExp) :
    Printable (.node t cs) = (IsBareToken t ∧ PrintableList cs) := rfl

/-- `PrintableList` on the empty list. -/
@[simp] theorem printableList_nil : PrintableList [] = True := rfl

/-- `PrintableList` on a cons. -/
@[simp] theorem printableList_cons (c : SExp) (cs : List SExp) :
    PrintableList (c :: cs) = (Printable c ∧ PrintableList cs) := rfl

mutual

/-- `Printable` is decidable. -/
def decPrintable : (e : SExp) → Decidable (Printable e)
  | .atom s => inferInstanceAs (Decidable (IsToken s))
  | .node t cs =>
      match decPrintableList cs with
      | .isTrue h =>
          if ht : IsBareToken t then .isTrue ⟨ht, h⟩ else .isFalse fun hh => ht hh.1
      | .isFalse h => .isFalse fun hh => h hh.2

/-- `PrintableList` is decidable. -/
def decPrintableList : (cs : List SExp) → Decidable (PrintableList cs)
  | [] => .isTrue trivial
  | c :: cs =>
      match decPrintable c with
      | .isTrue h =>
          match decPrintableList cs with
          | .isTrue h' => .isTrue ⟨h, h'⟩
          | .isFalse h' => .isFalse fun hh => h' hh.2
      | .isFalse h => .isFalse fun hh => h hh.1

end

instance (e : SExp) : Decidable (Printable e) := decPrintable e
instance (cs : List SExp) : Decidable (PrintableList cs) := decPrintableList cs

/-- The children part of a node's layout: every child of `xs`, each preceded by
the separator `sep` (`spectec/src/util/sexpr.ml:23`). -/
def ppChildren (off width : Nat) (sep : String) (xs : List SExp) : List Char :=
  (Rope.flattens (xs.map fun x => Rope.concat [.leaf sep, (pp off width x).2])).toList

/-- A node with no children contributes no characters. -/
@[simp] theorem ppChildren_nil (off width : Nat) (sep : String) :
    ppChildren off width sep [] = [] := rfl

/-- Each child is preceded by the separator. -/
@[simp] theorem ppChildren_cons (off width : Nat) (sep : String) (x : SExp) (xs : List SExp) :
    ppChildren off width sep (x :: xs) =
      sep.toList ++ ((pp off width x).2.flatten.toList ++ ppChildren off width sep xs) := by
  simp [ppChildren, String.toList_append]

end SExp

/-! ## Soundness of the printer -/

/-- The indentation that `pp` inserts is layout (`spectec/src/util/sexpr.ml:22`). -/
theorem spaces_indent (off : Nat) : Spaces (SExp.indent off).toList := by
  intro c hc
  rw [SExp.indent, String.toList_ofList] at hc
  rw [List.eq_of_mem_replicate hc]
  exact Or.inl rfl

namespace SExp

/-- The layout of a node, split into tag, children and terminator.  The two
cases of the `if` at `spectec/src/util/sexpr.ml:21` differ only in the layout
strings, and both are nonempty layout runs. -/
theorem pp_node_toList (off width : Nat) (t : String) (xs : List SExp) :
    ∃ sep fin : String, Spaces sep.toList ∧ sep.toList ≠ [] ∧ Spaces fin.toList ∧
      (pp off width (.node t xs)).2.flatten.toList =
        '(' :: (t.toList ++ (ppChildren (off + 2) width sep xs ++ (fin.toList ++ [')']))) := by
  simp only [pp, Rope.flatten_concat, Rope.flattens_cons, Rope.flattens_append,
    Rope.flattens_nil, Rope.flatten_leaf, String.toList_append, ppList_eq_map,
    List.map_map, ppChildren]
  split
  · refine ⟨" ", "", by decide, by decide, by decide, ?_⟩
    simp [Function.comp_def]
  · refine ⟨"\n  " ++ indent off, "\n" ++ indent off, ?_, ?_, ?_, ?_⟩
    · rw [String.toList_append]
      exact (by decide : Spaces "\n  ".toList).append (spaces_indent off)
    · simp
    · rw [String.toList_append]
      exact (by decide : Spaces "\n".toList).append (spaces_indent off)
    · simp [Function.comp_def]

end SExp

mutual

/-- **Printer soundness.**  The layout that `pp` produces for a `Printable`
S-expression is read back as that S-expression, whatever the target `width`
and the current offset `off`. -/
theorem pp_lexesPre (off width : Nat) (e : SExp) (h : e.Printable)
    (rest : List Char) (hrest : HeadNot IsBare rest) :
    LexesPre ((SExp.pp off width e).2.flatten.toList ++ rest) e rest := by
  match e, h with
  | .atom s, h =>
      have ht : IsToken s := h
      simp only [SExp.pp, Rope.flatten_leaf]
      rcases ht with hb | hq
      · exact .bare hb hrest
      · exact .quoted hq
  | .node t xs, h =>
      have h2 : IsBareToken t ∧ SExp.PrintableList xs := h
      obtain ⟨sep, fin, hsep, hsne, hfin, hpp⟩ := SExp.pp_node_toList off width t xs
      have htl : HeadNot IsBare (fin.toList ++ ')' :: rest) :=
        hfin.headNot (fun _ hc => not_isBare_of_isSpace hc) (by exact not_isBare_rparen)
      obtain ⟨hseq, hhead⟩ :=
        ppChildren_lexesSeq (off + 2) width sep hsep hsne xs h2.2
          (fin.toList ++ ')' :: rest) rest htl (.nil hfin)
      rw [hpp]
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      exact .node h2.1 hhead hseq

/-- The children of a node are read back in order: this is the `LexesSeq` half
of `pp_lexesPre`.  The conjunct `HeadNot IsBare` is what makes the tag of the
enclosing node obey maximal munch. -/
theorem ppChildren_lexesSeq (off width : Nat) (sep : String)
    (hsep : Spaces sep.toList) (hsne : sep.toList ≠ [])
    (xs : List SExp) (h : SExp.PrintableList xs) (tl rest : List Char)
    (htl : HeadNot IsBare tl) (hnil : LexesSeq tl [] (')' :: rest)) :
    LexesSeq (SExp.ppChildren off width sep xs ++ tl) xs (')' :: rest) ∧
      HeadNot IsBare (SExp.ppChildren off width sep xs ++ tl) := by
  match xs, h with
  | [], _ => exact ⟨by simpa using hnil, by simpa using htl⟩
  | x :: xs', h =>
      have h2 : SExp.Printable x ∧ SExp.PrintableList xs' := h
      obtain ⟨hseq', hhead'⟩ :=
        ppChildren_lexesSeq off width sep hsep hsne xs' h2.2 tl rest htl hnil
      have hx := pp_lexesPre off width x h2.1 _ hhead'
      rw [SExp.ppChildren_cons]
      simp only [List.append_assoc]
      exact ⟨.cons hsep hx hseq',
        hsep.headNot_of_ne_nil (fun _ hc => not_isBare_of_isSpace hc) hsne _⟩

end

/-! ## Placement in the lattice -/

/-- `render` emits a spelling of every `Printable` S-expression, at every
width. -/
theorem lexicalRel_render (width : Nat) (e : SExp) (h : e.Printable) :
    lexicalRel (SExp.render width e) e := by
  have hpre := pp_lexesPre 0 width e h [] trivial
  rw [List.append_nil] at hpre
  exact .intro (w := []) spaces_nil spaces_nil hpre

/-- `render` is a correct encoder on `Printable`. -/
theorem lexicalRel_encoderCorrectOn (width : Nat) :
    lexicalRel.EncoderCorrectOn SExp.Printable (SExp.render width) :=
  fun e h => lexicalRel_render width e h

/-- The printer's graph, restricted to `Printable`, lies below the lexical
convention. -/
theorem render_le_lexicalRel (width : Nat) :
    (EncRel.ofFun (SExp.render width)).restrict SExp.Printable ≤ lexicalRel := by
  rintro s e ⟨rfl, hp⟩
  exact lexicalRel_render width e hp

/-- The restriction to `Printable` is necessary.  `Atom ""` prints as nothing
at all (`spectec/src/util/sexpr.ml:16`), and the empty string spells nothing:
this is the one place where `Util.Sexpr` printing is not injective. -/
theorem not_lexicalRel_empty (e : SExp) : ¬ lexicalRel "" e := by
  intro h
  obtain ⟨w, body, rest, -, -, hpre, heq⟩ := h.inv
  obtain ⟨c, t, hc, -, -⟩ := hpre.start
  rw [hc] at heq
  exact absurd heq (by simp)

/-- `Atom ""` is the atom that `render` erases. -/
theorem render_atom_empty (width : Nat) : SExp.render width (.atom "") = "" := rfl

/-- `Atom ""` is not `Printable`, which is why `render_le_lexicalRel` is
restricted. -/
theorem not_printable_atom_empty : ¬ SExp.Printable (.atom "") := by
  rw [SExp.printable_atom]
  rintro (⟨hne, -⟩ | ⟨body, hb, -⟩)
  · exact hne (by simp)
  · exact absurd hb (by simp)

/-- A worked example, built from the rules: `"(a b)"` spells
`Node ("a", [Atom "b"])`. -/
theorem lexicalRel_example : lexicalRel "(a b)" (.node "a" [.atom "b"]) := by
  have ha : IsBareToken "a" := by decide
  have hb : IsBareToken "b" := by decide
  have hpre : LexesPre ("b".toList ++ [')']) (.atom "b") [')'] := .bare hb (by decide)
  have hnil : LexesSeq ([] ++ ')' :: []) [] (')' :: []) := .nil spaces_nil
  have hseq : LexesSeq ([' '] ++ ("b".toList ++ [')'])) [.atom "b"] (')' :: []) :=
    .cons (by decide) hpre hnil
  have hnode : LexesPre ('(' :: ("a".toList ++ ([' '] ++ ("b".toList ++ [')']))))
      (.node "a" [.atom "b"]) [] := .node ha (by decide) hseq
  exact .intro (w := []) spaces_nil spaces_nil hnode

/-! ## Whole `--ast` files -/

/-- Layout may be prepended to a stream. -/
theorem LexesStream.prepend {w l : List Char} {es : List SExp} (hw : Spaces w)
    (h : LexesStream l es) : LexesStream (w ++ l) es := by
  cases h with
  | nil hw' => exact .nil (hw.append hw')
  | @cons w' body rest e es hw' hpre hs =>
      rw [← List.append_assoc]
      exact .cons (hw.append hw') hpre hs

/-- `output_script` emits a spelling of a whole list of definitions. -/
theorem lexesStream_outputScript (width : Nat) :
    ∀ (es : List SExp), SExp.PrintableList es →
      ∀ (tl : List Char), Spaces tl →
        LexesStream ((SExp.outputScript width es).toList ++ tl) es
  | [], _, tl, htl => by
      simpa [SExp.outputScript] using LexesStream.nil htl
  | e :: es, h, tl, htl => by
      have h2 : SExp.Printable e ∧ SExp.PrintableList es := h
      have hrec := (lexesStream_outputScript width es h2.2 tl htl).prepend
        (w := ['\n']) (by decide)
      have hT : HeadNot IsBare ('\n' :: ((SExp.outputScript width es).toList ++ tl)) := by
        exact not_isBare_of_isSpace (Or.inr rfl)
      have hpre := pp_lexesPre 0 width e h2.1 _ hT
      have : (SExp.outputScript width (e :: es)).toList ++ tl =
          [] ++ ((SExp.pp 0 width e).2.flatten.toList ++
            ('\n' :: ((SExp.outputScript width es).toList ++ tl))) := by
        simp [SExp.outputScript, SExp.output, SExp.render, String.toList_append]
      rw [this]
      exact .cons spaces_nil hpre hrec

/-- **Printer soundness for a whole file.**  The exact contents of
`spectec --ast -o FILE` are a spelling of the list of definitions. -/
theorem streamRel_astFile (width : Nat) (es : List SExp) (h : SExp.PrintableList es) :
    streamRel (SExp.astFile width es) es := by
  have := lexesStream_outputScript width es h ['\n'] (by decide)
  simpa [streamRel, SExp.astFile, String.toList_append] using this

/-- The file printer's graph, restricted to `PrintableList`, lies below the
stream convention. -/
theorem astFile_le_streamRel (width : Nat) :
    (EncRel.ofFun (SExp.astFile width)).restrict SExp.PrintableList ≤ streamRel := by
  rintro s es ⟨rfl, hp⟩
  exact streamRel_astFile width es hp

/-- A bare token spells the atom that carries it. -/
theorem lexicalRel_atom_bare (s : String) (h : IsBareToken s) : lexicalRel s (.atom s) := by
  have hpre : LexesPre (s.toList ++ []) (.atom s) [] := .bare h trivial
  rw [List.append_nil] at hpre
  exact .intro (w := []) spaces_nil spaces_nil hpre

/-- Leading layout is allowed, so the same atom has many spellings. -/
theorem lexicalRel_space_atom (s : String) (h : IsBareToken s) :
    lexicalRel (" " ++ s) (.atom s) := by
  have hpre : LexesPre (s.toList ++ []) (.atom s) [] := .bare h trivial
  rw [List.append_nil] at hpre
  show Lexes (" " ++ s).toList (.atom s)
  rw [String.toList_append]
  exact .intro (by decide) spaces_nil hpre

/-- The convention is not deterministic: layout is free, so `--ast-width` (and
indeed any leading whitespace) changes the spelling but not the value. -/
theorem lexicalRel_not_deterministic : ¬ lexicalRel.Deterministic := by
  intro hdet
  have hb : IsBareToken "a" := by decide
  have heq := hdet (lexicalRel_atom_bare "a" hb) (lexicalRel_space_atom "a" hb)
  have h2 := congrArg String.toList heq
  rw [String.toList_append] at h2
  exact absurd h2 (by decide)

/-! ## Comparison with the WAT and Scheme conventions

The three S-expression conventions in this library differ lexically, and only
this one is currently phrased as an `EncRel`:

* **SpecTec** (`spectec/src/util/sexpr.ml`): no comments, no dotted pairs, no
  `#` syntax; a node's head is a *string* rather than a nested expression
  (`SExp.node`), so `(1 2)` is not well-formed abstract syntax at all; texts
  are OCaml-escaped with decimal `\DDD` escapes
  (`Silmaril.SpecTec.Escape.escapeByte`) and the escaped form including its
  quotation marks is what the atom stores.
* **WAT** (`Silmaril/Wasm/Wat/Lexer.lean`): `;;` line comments and nested
  `(; … ;)` block comments, `$`-identifiers, hexadecimal `\hh` string escapes,
  and byte-string rather than text atoms.  That lexer runs at elaboration time
  and is not an `EncRel`.
* **Scheme/Lisp** (`Silmaril/Formats/SExp/Parser.lean`): `;` comments, `#`
  syntax, dotted pairs, and proper lists whose head is an expression.  That
  parser is a total function, again not an `EncRel`.

There is no `Silmaril/Formats/SExp/Wat.lean` or
`Silmaril/Formats/SExp/Scheme.lean` at the time of writing, so a lattice
comparison (`≤`, `⊓`, a common refinement) is future work; naming relations
that do not exist would be guesswork.  What can be stated now is that the
characters those conventions reserve are ordinary bare characters here. -/

/-- `;` is an ordinary bare character: SpecTec's convention has no comment
syntax, so a WAT or Scheme comment would be read as atoms. -/
theorem isBare_semicolon : IsBare ';' := by decide

/-- `#` is an ordinary bare character: there is no Scheme-style `#` syntax. -/
theorem isBare_hash : IsBare '#' := by decide

/-- `$` is an ordinary bare character: WAT identifiers are not special here. -/
theorem isBare_dollar : IsBare '$' := by decide

/-- `.` is an ordinary bare character: there are no dotted pairs, so `(a . b)`
is a node with tag `a` and the two children `.` and `b`. -/
theorem isBare_dot : IsBare '.' := by decide

/-- The apostrophe is an ordinary bare character: there is no `'`-quotation
syntax, and indeed `n'` is a common SpecTec identifier. -/
theorem isBare_apostrophe : IsBare '\'' := by decide

end Silmaril.SpecTec
