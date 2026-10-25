module

public import Silmaril.Formats.SExp.Encoding

/-!
# The WebAssembly text-format lexical conventions as an S-expression encoding

`sexpWat p : EncRel String SExp` transcribes the WAT lexical layer and its
bracket structure, for two profiles:

* `Profile.core3` — SpecTec `6.0-text.lexical.spectec` (Wasm Core 3.0);
* `Profile.v1` — the W3C 2019 Recommendation (Wasm 1.0), §6.3.

It is the composite `lexRel p ⨾ treesRel` of a lexer relation (characters to
tokens, `Lex`) and a bracketing relation (tokens to trees, `Trees`).

## Lexical conventions (Core 3.0, `Tsource`/`Ttoken`/`Tspace`)

* **Whitespace** `Tspace`: space, `Tformat` (tab, newlines `U+0A`, `U+0D`,
  `U+0D U+0A`), comments and annotations.
* **Line comments** `;; …` up to a newline or the end of input.  In Core 3.0
  a newline is `U+0A` or `U+0D` (`Tnewline`); in the 2019 REC a line comment
  ends at `U+0A` only (`linechar ::= c (if c ≠ U+0A)`), see `IsNewlineP`.
* **Block comments** `(; … ;)`, *nested*; `Tblockchar`'s restrictions on `;`
  and `(` follow the 2.0 look-ahead rules (`BlockTail`), as the reference
  interpreter's lexer does (the literal SpecTec reading consumes the next
  character; erratum T5, the documented text-format erratum).
* **Annotations** `(@id …)` (Core 3.0 only): `"(@" Tannotid (Tspace | Ttoken)* ")"`
  with well-bracketed tokens (reserved tokens allowed inside).  **Annotations
  are treated as whitespace**: they are erased from the S-expression, exactly
  as the Core 3.0 specification (which assigns no meaning to them) prescribes.
  In Wasm 1.0 `(@` is an ordinary `(` followed by a token starting with `@`.
* **Tokens** are split by longest match.  In Core 3.0 a token is a maximal run
  of `Tidchar`s and string literals, or one of the single-character reserved
  tokens `, ; [ ] { }` (as in the reference interpreter; SpecTec's `Treserved`
  puts these inside the run, erratum the documented text-format erratum); a run is classified as
  a string (exactly one string literal), an identifier (`$` followed by
  `Tidchar+`, or `$` followed by a non-empty UTF-8 string, the quoted form of
  Core 3.0), a bare token (`Tidchar+`: keywords, numbers, and idchar-only
  reserved tokens, kept as `Atom.sym` with their raw text — numbers such as
  `1_000`, `0x1p-3`, `nan:0x7f`, `inf` are interpreted by the syntax layer,
  `Silmaril.Wasm.Text.Values`), or otherwise a *reserved* token, which makes
  the text malformed (outside annotations).  A line comment `;;` wins against
  the reserved token `;` (longest match).  In Wasm 1.0 reserved tokens are
  `Tidchar+` only, strings are separate tokens, and quoted identifiers do not
  exist.
* **Strings** `Tstring` with escapes `\t \n \r \" \' \\ \hh \u{…}` denote byte
  sequences (`Tstringelem`), shorter than `2^32`.
* `(` immediately followed by `;` always starts a block comment, and (Core 3.0)
  `(` immediately followed by `@` always starts an annotation.

Deviations: (1) block comments use look-ahead (above; the documented text-format erratum);
(2) the SpecTec source bounds `\u{n}` by `n < 0xD800 ∨ 0xE800 ≤ n`; this is a
typo for `0xE000`, and (3) like the reference
interpreter, `\u{n}` also accepts surrogates, encoded as the interpreter does
(`escapeUtf8`).  See `Silmaril.Wasm.Text.Core.Modules`.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

/-- The lexical profile: Wasm 1.0 (2019 REC) or Core 3.0 (SpecTec). -/
inductive Profile where
  | v1
  | core3
  deriving DecidableEq, Repr

/-! ## Character classes -/

/-- `Tidchar`. -/
def IsIdChar (c : Char) : Prop :=
  ('0' ≤ c ∧ c ≤ '9') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨
    c ∈ "!#$%&'*+-./:<=>?@\\^_`|~".toList

instance (c : Char) : Decidable (IsIdChar c) := by unfold IsIdChar; infer_instance

/-- Characters that may occur in a Core 3.0 token run besides string literals:
`Tidchar` only.  The punctuation `, ; [ ] { }` forms single-character reserved
tokens (`IsPunct`, `Tok.punct`), as in the reference interpreter
(`lexer.mll`: `reserved = (idchar | string)+ | ',' | ';' | '[' | ']' | '{' | '}'`)
and the annotations proposal; SpecTec's `Treserved` puts it inside the run,
which makes `(func;;bla)` (`token.wast:55`) a single reserved token. -/
def IsRunChar (c : Char) : Prop := IsIdChar c

instance (c : Char) : Decidable (IsRunChar c) := by unfold IsRunChar; infer_instance

/-- The single-character reserved tokens `, ; [ ] { }` of Core 3.0. -/
def IsPunct (c : Char) : Prop := c ∈ [',', ';', '[', ']', '{', '}']

instance (c : Char) : Decidable (IsPunct c) := by unfold IsPunct; infer_instance

/-- `" "` and `Tformat` characters. -/
def IsSpaceChar (c : Char) : Prop := c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

/-- Characters ending a line comment, per profile: `Tnewline` (`U+0A` or `U+0D`;
`U+0D U+0A` is `U+0D` followed by the space character `U+0A`) in Core 3.0, and
`U+0A` only in the 2019 REC (`linechar ::= c (if c ≠ U+0A)`). -/
def IsNewlineP : Profile → Char → Prop
  | .v1, c => c = '\n'
  | .core3, c => c = '\n' ∨ c = '\r'

/-- `Tlinechar*` (resp. `linechar*`). -/
def NoNewline (p : Profile) (cs : Chars) : Prop := ∀ c ∈ cs, ¬ IsNewlineP p c

/-! ## Numerals (`Tnum`, `Thexnum`), shared with the syntax layer -/

/-- `Tnum`: decimal digits with single `_` separators between digits. -/
inductive Num : Chars → Nat → Prop where
  | one {d : Char} : '0' ≤ d ∧ d ≤ '9' → Num [d] (d.toNat - '0'.toNat)
  | snoc {ds : Chars} {n : Nat} {d : Char} : Num ds n → '0' ≤ d ∧ d ≤ '9' →
      Num (ds ++ [d]) (10 * n + (d.toNat - '0'.toNat))
  | snocSep {ds : Chars} {n : Nat} {d : Char} : Num ds n → '0' ≤ d ∧ d ≤ '9' →
      Num (ds ++ ['_', d]) (10 * n + (d.toNat - '0'.toNat))

/-- `Thexnum`: hexadecimal digits with single `_` separators between digits. -/
inductive HexNum : Chars → Nat → Prop where
  | one {d : Char} : IsHexDigit d → HexNum [d] (hexVal d)
  | snoc {ds : Chars} {n : Nat} {d : Char} : HexNum ds n → IsHexDigit d →
      HexNum (ds ++ [d]) (16 * n + hexVal d)
  | snocSep {ds : Chars} {n : Nat} {d : Char} : HexNum ds n → IsHexDigit d →
      HexNum (ds ++ ['_', d]) (16 * n + hexVal d)

/-! ## Strings (`Tstringchar`, `Tstringelem`, `Tstring`) -/

/-- The bytes of the escape `\u{n}` (`n < 0x110000`), as the reference
interpreter produces them (`Utf8.encode [n]`, `interpreter/binary/utf8.ml`):
the UTF-8 encoding of the character `n` when `n` is a Unicode scalar value, and
the generalized three-byte encoding `ED (80 + n/64 % 64) (80 + n % 64)` when `n`
is a surrogate `0xD800 ≤ n < 0xE000`. -/
def escapeUtf8 (n : Nat) : List UInt8 :=
  if 0xD800 ≤ n ∧ n < 0xE000 then
    [0xED, UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]
  else charUtf8 (Char.ofNat n)

theorem escapeUtf8_scalar {n : Nat} (h : n < 0xD800 ∨ 0xE000 ≤ n) :
    escapeUtf8 n = charUtf8 (Char.ofNat n) := by
  unfold escapeUtf8
  split
  · omega
  · rfl

/-- One string element and the bytes it denotes.

`\u{n}` accepts every `n < 0x110000`, including the surrogates
`0xD800 ≤ n < 0xE000`, which it encodes as the reference interpreter does
(`escapeUtf8`).  This departs from SpecTec (`n < 0xD800 ∨ 0xE800 ≤ n`, itself a
typo for `0xE000`, the documented text-format erratum), which excludes surrogates, to accept
exactly the strings the reference interpreter accepts; the encoded surrogate is
never valid UTF-8, so names (`NameLit`) still reject it, as the interpreter
does.  See `Silmaril.Wasm.Text.Core.Modules`. -/
inductive StringElem : Chars → List UInt8 → Prop where
  | char {c : Char} : 0x20 ≤ c.toNat → c.toNat ≠ 0x7F → c ≠ '"' → c ≠ '\\' →
      StringElem [c] (charUtf8 c)
  | tab : StringElem ['\\', 't'] [0x09]
  | newline : StringElem ['\\', 'n'] [0x0A]
  | ret : StringElem ['\\', 'r'] [0x0D]
  | dquote : StringElem ['\\', '"'] [0x22]
  | squote : StringElem ['\\', '\''] [0x27]
  | backslash : StringElem ['\\', '\\'] [0x5C]
  | unicode {ds : Chars} {n : Nat} : HexNum ds n → n < 0x110000 →
      StringElem ('\\' :: 'u' :: '{' :: ds ++ ['}']) (escapeUtf8 n)
  | byte {h₁ h₂ : Char} : IsHexDigit h₁ → IsHexDigit h₂ →
      StringElem ['\\', h₁, h₂] [UInt8.ofNat (16 * hexVal h₁ + hexVal h₂)]

/-- A sequence of string elements and the concatenation of their bytes. -/
inductive StringBody : Chars → List UInt8 → Prop where
  | nil : StringBody [] []
  | cons {e rest : Chars} {b bs : List UInt8} :
      StringElem e b → StringBody rest bs → StringBody (e ++ rest) (b ++ bs)

/-- `Tstring`: a quoted string literal and the bytes it denotes. -/
def StringLit (cs : Chars) (bs : List UInt8) : Prop :=
  ∃ body, cs = '"' :: (body ++ ['"']) ∧ StringBody body bs ∧ bs.length < 2 ^ 32

/-- `Tname`: a string literal whose bytes are the UTF-8 encoding of `n`. -/
def NameLit (cs : Chars) (n : String) : Prop :=
  ∃ bs, StringLit cs bs ∧ Unicode.utf8? bs = some n

/-! ## Block comments (`Tblockcomment`, `Tblockchar`) -/

mutual
  /-- The rest of a block comment after `(;`: `Tblockchar* ";)"`, following the
  2.0 **look-ahead** rules (2019 REC §6.3.4: `';'` if the next character is not
  `')'`, `'('` if the next character is not `';'`), which is exactly the
  reference interpreter's lexer (`lexer.mll`, rule `comment`).  Defining the body
  together with its terminator lets the look-ahead see the terminator; `;)` can
  only close the comment, so the grammar is deterministic.

  The Core 3.0 SpecTec snapshot writes these alternatives as `";"+ c` and
  `"("+ c`, which, read literally, *consume* `c`: that reading rejects
  `comments.wast:26` `(;;;;;;;;;;;;;;)` and `(;a;;)` and breaks
  `(; ;(; x ;) ;)`, which every implementation accepts (erratum T5,
  the documented text-format erratum); see
  `Silmaril.Wasm.Text.Core.Modules` (Departures from the sources). -/
  inductive BlockTail : Chars → Prop where
    | close : BlockTail [';', ')']
    | plain {c : Char} {r : Chars} : c ≠ ';' → c ≠ '(' → BlockTail r → BlockTail (c :: r)
    | semi {r : Chars} : r.head? ≠ some ')' → BlockTail r → BlockTail (';' :: r)
    | paren {r : Chars} : r.head? ≠ some ';' → BlockTail r → BlockTail ('(' :: r)
    | nested {a r : Chars} : BlockComment a → BlockTail r → BlockTail (a ++ r)

  /-- `Tblockcomment`: `(; Tblockchar* ;)`. -/
  inductive BlockComment : Chars → Prop where
    | mk {t : Chars} : BlockTail t → BlockComment ('(' :: ';' :: t)
end

/-- `(;a;;)` is a block comment: the second `;` is followed by `;`, not `)`. -/
theorem blockComment_semi_end : BlockComment "(;a;;)".toList := by
  refine BlockComment.mk (t := ['a', ';', ';', ')']) ?_
  exact .plain (by decide) (by decide) (.semi (by decide) .close)

/-- `(; ;(; x ;) ;)` is one block comment with a nested comment after `;`. -/
theorem blockComment_nested_after_semi : BlockComment "(; ;(; x ;) ;)".toList := by
  refine BlockComment.mk (t := [' ', ';', '(', ';', ' ', 'x', ' ', ';', ')', ' ', ';', ')']) ?_
  refine .plain (by decide) (by decide) (.semi (by decide) ?_)
  have hn : BlockComment ['(', ';', ' ', 'x', ' ', ';', ')'] :=
    .mk (.plain (by decide) (by decide) (.plain (by decide) (by decide)
      (.plain (by decide) (by decide) .close)))
  exact BlockTail.nested (a := ['(', ';', ' ', 'x', ' ', ';', ')']) (r := [' ', ';', ')']) hn
    (.plain (by decide) (by decide) .close)

/-! ## Tokens -/

/-- Lexical tokens.  `reserved` and `punct` tokens only occur inside
annotations. -/
inductive Tok where
  | lp
  | rp
  | atom (a : Atom)
  | reserved
  /-- A single-character reserved token `, ; [ ] { }` (Core 3.0). -/
  | punct (c : Char)
  deriving DecidableEq, Repr

/-- A Core 3.0 token run: `Tidchar`s and string literals. -/
inductive RunPieces : Chars → Prop where
  | nil : RunPieces []
  | char {c : Char} {rest : Chars} : IsRunChar c → RunPieces rest → RunPieces (c :: rest)
  | str {s rest : Chars} {bs : List UInt8} : StringLit s bs → RunPieces rest →
      RunPieces (s ++ rest)

/-- Identifier-or-bare-token classification of a `Tidchar+` run (`Tid`,
`Tkeyword`, numbers, idchar-only reserved tokens). -/
inductive IdRun : Chars → Atom → Prop where
  | sym {cs : Chars} : cs ≠ [] → (∀ c ∈ cs, IsIdChar c) →
      ¬ (cs.head? = some '$' ∧ 2 ≤ cs.length) → IdRun cs (.sym (String.ofList cs))
  | id {rest : Chars} : rest ≠ [] → (∀ c ∈ rest, IsIdChar c) →
      IdRun ('$' :: rest) (.id (String.ofList rest))

/-- Classification of a Core 3.0 token run as an atom (`Tstring`, `Tid` incl.
the quoted form `"$" Tname`, `Tidchar+`). -/
inductive RunAtom3 : Chars → Atom → Prop where
  | str {cs : Chars} {bs : List UInt8} : StringLit cs bs → RunAtom3 cs (.str bs)
  | idRun {cs : Chars} {a : Atom} : IdRun cs a → RunAtom3 cs a
  | quotedId {q : Chars} {n : String} : NameLit q n → n ≠ "" →
      RunAtom3 ('$' :: q) (.id n)

/-- One token's characters, for profile `p`; `top` forbids reserved tokens. -/
def Tok1 : Profile → Bool → Chars → Tok → Prop
  | _, _, cs, .lp => cs = ['(']
  | _, _, cs, .rp => cs = [')']
  | .core3, _, cs, .atom a => RunAtom3 cs a ∧ ¬ cs.take 2 = [';', ';']
  | .core3, top, cs, .reserved =>
      top = false ∧ RunPieces cs ∧ cs ≠ [] ∧ (¬ ∃ a, RunAtom3 cs a) ∧ ¬ cs.take 2 = [';', ';']
  | .core3, top, cs, .punct c => top = false ∧ IsPunct c ∧ cs = [c]
  | .v1, _, cs, .atom (.str bs) => StringLit cs bs
  | .v1, _, cs, .atom a => IdRun cs a
  | .v1, _, _, .reserved => False
  | .v1, _, _, .punct _ => False

/-- The longest-match condition on the character following a token. -/
def Follow : Profile → Tok → Chars → Prop
  | .core3, .lp, rest => rest.head? ≠ some ';' ∧ rest.head? ≠ some '@'
  | .v1, .lp, rest => rest.head? ≠ some ';'
  | _, .rp, _ => True
  | .core3, .punct c, rest => c = ';' → rest.head? ≠ some ';'
  | .core3, _, rest => ∀ c, rest.head? = some c → ¬ IsRunChar c ∧ c ≠ '"'
  | .v1, .punct _, _ => True
  | .v1, .atom (.str _), _ => True
  | .v1, _, rest => ∀ c, rest.head? = some c → ¬ IsIdChar c

/-- Well-bracketed token sequences (annotation bodies). -/
inductive Balanced : List Tok → Prop where
  | nil : Balanced []
  | tok {t : Tok} {ts : List Tok} : t ≠ .lp → t ≠ .rp → Balanced ts → Balanced (t :: ts)
  | group {a b : List Tok} : Balanced a → Balanced b → Balanced (.lp :: (a ++ .rp :: b))

/-- `Tannotid`: `Tidchar+ | Tname`. -/
def AnnotId (cs : Chars) : Prop :=
  (cs ≠ [] ∧ ∀ c ∈ cs, IsIdChar c) ∨ ∃ n, NameLit cs n

mutual
  /-- One whitespace item (`" "`, `Tformat`, `Tcomment`, `Tannot`). -/
  inductive SpaceItem : Profile → Chars → Prop where
    | char {p : Profile} {c : Char} : IsSpaceChar c → SpaceItem p [c]
    | line {p : Profile} {body : Chars} {nl : Char} : NoNewline p body → IsNewlineP p nl →
        SpaceItem p (';' :: ';' :: (body ++ [nl]))
    | block {p : Profile} {cs : Chars} : BlockComment cs → SpaceItem p cs
    | annot {idc body : Chars} {ts : List Tok} : AnnotId idc →
        (∀ c, body.head? = some c → ¬ IsRunChar c ∧ c ≠ '"') →
        Lex .core3 false body ts → Balanced ts →
        SpaceItem .core3 ('(' :: '@' :: (idc ++ body ++ [')']))

  /-- `Tspace`. -/
  inductive Space : Profile → Chars → Prop where
    | nil {p : Profile} : Space p []
    | cons {p : Profile} {a b : Chars} : SpaceItem p a → Space p b → Space p (a ++ b)

  /-- Token sequences separated by whitespace.  `top = true` at the top level
  (no reserved tokens; a final line comment may end at the end of input). -/
  inductive Lex : Profile → Bool → Chars → List Tok → Prop where
    | done {p : Profile} {top : Bool} {s : Chars} : Space p s → Lex p top s []
    | doneEof {p : Profile} {s body : Chars} : Space p s → NoNewline p body →
        Lex p true (s ++ ';' :: ';' :: body) []
    | step {p : Profile} {top : Bool} {s c rest : Chars} {t : Tok} {ts : List Tok} :
        Space p s → Tok1 p top c t → Follow p t rest → Lex p top rest ts →
        Lex p top (s ++ c ++ rest) (t :: ts)
end

/-! ## Bracket structure -/

mutual
  /-- One S-expression from its tokens. -/
  inductive Tree : List Tok → SExp → Prop where
    | atom (a : Atom) : Tree [.atom a] (.atom a)
    | list {ts : List Tok} {xs : List SExp} : Trees ts xs →
        Tree (.lp :: (ts ++ [.rp])) (listOf xs)

  /-- A sequence of S-expressions from their tokens. -/
  inductive Trees : List Tok → List SExp → Prop where
    | nil : Trees [] []
    | cons {a b : List Tok} {x : SExp} {xs : List SExp} :
        Tree a x → Trees b xs → Trees (a ++ b) (x :: xs)
end

/-! ## The encoding relations -/

/-- The lexer as an encoding of token lists in text. -/
def lexRel (p : Profile) : EncRel String (List Tok) := fun s ts => Lex p true s.toList ts

/-- Bracketing: a token list spells the document of its trees. -/
def treesRel : EncRel (List Tok) SExp := fun ts x => ∃ xs, Trees ts xs ∧ x = doc xs

/-- **WAT S-expression text** for profile `p`. -/
def sexpWat (p : Profile) : EncRel String SExp := lexRel p ⨾ treesRel

/-- Core 3.0 lexical conventions. -/
abbrev sexpWat3 : EncRel String SExp := sexpWat .core3

/-- Wasm 1.0 lexical conventions. -/
abbrev sexpWat1 : EncRel String SExp := sexpWat .v1

/-- UTF-8 byte spellings (the source-file encoding of `.wat` files). -/
def sexpWatBytes (p : Profile) : EncRel (List UInt8) SExp := (sexpWat p).push Unicode.utf8

end Silmaril.Formats.SExpEncoding.Wat
