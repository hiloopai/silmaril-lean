module

public import Silmaril.Formats.SExp.Encoding

/-!
# R7RS-style Scheme S-expression text: definitions

The grammar and the encoding relation `sexpScheme`; see `EncodingScheme.lean` for
the documentation, the functionality proofs and examples.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Scheme

open Silmaril

/-! ## Character classes -/

/-- `<whitespace>`: intraline whitespace (space, tab) and line endings. -/
def IsWs (c : Char) : Prop := c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

/-- `<intraline whitespace>`. -/
def IsIntraline (c : Char) : Prop := c = ' ' ∨ c = '\t'

/-- `<delimiter>`: whitespace, `|`, `(`, `)`, `"`, `;`. -/
def IsDelim (c : Char) : Prop := IsWs c ∨ c = '|' ∨ c = '(' ∨ c = ')' ∨ c = '"' ∨ c = ';'

instance (c : Char) : Decidable (IsWs c) := by unfold IsWs; infer_instance
instance (c : Char) : Decidable (IsDelim c) := by unfold IsDelim; infer_instance

/-- No line ending in a comment body. -/
def NoLineEnd (cs : Chars) : Prop := ∀ c ∈ cs, c ≠ '\n' ∧ c ≠ '\r'

/-- The next character, if any, is a delimiter. -/
def DelimNext (rest : Chars) : Prop := ∀ c, rest.head? = some c → IsDelim c

/-- The value of a sequence of hexadecimal digits. -/
def hexValue (ds : Chars) : Nat := ds.foldl (fun n d => 16 * n + hexVal d) 0

/-- `<hex scalar value>`: one or more hex digits denoting a Unicode scalar value. -/
def HexScalar (ds : Chars) (c : Char) : Prop :=
  ds ≠ [] ∧ (∀ d ∈ ds, IsHexDigit d) ∧
    (hexValue ds < 0xD800 ∨ (0xE000 ≤ hexValue ds ∧ hexValue ds < 0x110000)) ∧
    c = Char.ofNat (hexValue ds)

/-- `<line ending>`: `\n`, `\r\n` or `\r`. -/
def LineEnding (cs : Chars) : Prop := cs = ['\n'] ∨ cs = ['\r', '\n'] ∨ cs = ['\r']

/-! ## Comments -/

mutual
  /-- The rest of a `<nested comment>` after `#|`: `<comment text>
  <comment cont>* |#`.  The R7RS side condition "`<comment text>` does not
  contain `#|` or `|#`" is read with **look-ahead**, so that it also applies
  across the boundaries with the delimiters: a `#` is never followed by `|`
  (that would open a nested comment) and a `|` is never followed by `#` (that
  would close the comment).  Hence `#|a#|#` is unterminated, as in R7RS
  readers. -/
  inductive NestedTail : Chars → Prop where
    | close : NestedTail ['|', '#']
    | char {c : Char} {r : Chars} : c ≠ '#' → c ≠ '|' → NestedTail r → NestedTail (c :: r)
    | hash {r : Chars} : r.head? ≠ some '|' → NestedTail r → NestedTail ('#' :: r)
    | bar {r : Chars} : r.head? ≠ some '#' → NestedTail r → NestedTail ('|' :: r)
    | nested {a r : Chars} : Nested a → NestedTail r → NestedTail (a ++ r)

  /-- `<nested comment>`: `#| <comment text> <comment cont>* |#`. -/
  inductive Nested : Chars → Prop where
    | mk {t : Chars} : NestedTail t → Nested ('#' :: '|' :: t)
end

/-- One item of intertoken space (datum comments are handled by `Skip`). -/
inductive SpaceItem : Chars → Prop where
  | ws {c : Char} : IsWs c → SpaceItem [c]
  | line {body : Chars} {e : Char} : NoLineEnd body → (e = '\n' ∨ e = '\r') →
      SpaceItem (';' :: (body ++ [e]))
  | nested {cs : Chars} : Nested cs → SpaceItem cs

/-- Intertoken space. -/
inductive Space : Chars → Prop where
  | nil : Space []
  | cons {a b : Chars} : SpaceItem a → Space b → Space (a ++ b)

/-! ## Strings and `|symbols|` -/

/-- Mnemonic and character escapes shared by strings and `|symbols|`. -/
def escapes : List (Char × Char) :=
  [('a', Char.ofNat 7), ('b', Char.ofNat 8), ('t', '\t'), ('n', '\n'), ('r', '\r'),
    ('"', '"'), ('\\', '\\'), ('|', '|')]

/-- A string body and the characters it denotes.  A line continuation absorbs
all following intraline whitespace (maximal munch). -/
inductive StrBody : Chars → List Char → Prop where
  | nil : StrBody [] []
  | char {c : Char} {rest : Chars} {cs : List Char} : c ≠ '"' → c ≠ '\\' →
      StrBody rest cs → StrBody (c :: rest) (c :: cs)
  | esc {e c : Char} {rest : Chars} {cs : List Char} : (e, c) ∈ escapes →
      StrBody rest cs → StrBody ('\\' :: e :: rest) (c :: cs)
  | hex {ds rest : Chars} {c : Char} {cs : List Char} : HexScalar ds c →
      StrBody rest cs → StrBody ('\\' :: 'x' :: (ds ++ ';' :: rest)) (c :: cs)
  | cont {w₁ le w₂ rest : Chars} {cs : List Char} : (∀ c ∈ w₁, IsIntraline c) →
      LineEnding le → (∀ c ∈ w₂, IsIntraline c) →
      (le = ['\r'] → rest.head? ≠ some '\n') →
      (∀ c, rest.head? = some c → ¬ IsIntraline c) →
      StrBody rest cs → StrBody ('\\' :: (w₁ ++ le ++ w₂ ++ rest)) cs

/-- A string literal and the string it denotes. -/
def StrLit (cs : Chars) (s : String) : Prop :=
  ∃ body, cs = '"' :: (body ++ ['"']) ∧ StrBody body s.toList

/-- A `|symbol|` body (`<symbol element>*`). -/
inductive SymBody : Chars → List Char → Prop where
  | nil : SymBody [] []
  | char {c : Char} {rest : Chars} {cs : List Char} : c ≠ '|' → c ≠ '\\' →
      SymBody rest cs → SymBody (c :: rest) (c :: cs)
  | esc {e c : Char} {rest : Chars} {cs : List Char} : (e, c) ∈ escapes →
      SymBody rest cs → SymBody ('\\' :: e :: rest) (c :: cs)
  | hex {ds rest : Chars} {c : Char} {cs : List Char} : HexScalar ds c →
      SymBody rest cs → SymBody ('\\' :: 'x' :: (ds ++ ';' :: rest)) (c :: cs)

/-- `| <symbol element>* |`. -/
def SymLit (cs : Chars) (s : String) : Prop :=
  ∃ body, cs = '|' :: (body ++ ['|']) ∧ SymBody body s.toList

/-! ## Tokens -/

/-- Scheme tokens. -/
inductive Tok where
  | lp
  | rp
  | dot
  /-- A quote abbreviation, with the name of the symbol it abbreviates. -/
  | quote (name : String)
  | datumComment
  | atom (a : Atom)
  deriving DecidableEq, Repr

/-- A bare token: a maximal run of non-delimiters that is not `.`, does not
start with a quote character, (if it starts with `#`) has at least two
characters and does not start with `#\`; or a character literal `#\c…` (whose
`c` may be a delimiter).  Character literals come only from the second
disjunct, so `#\ ` is the literal for the space character and never the token
`#\` followed by whitespace (a lone `#\` has no spelling, as in R7RS). -/
def Bare (cs : Chars) : Prop :=
  (cs ≠ [] ∧ (∀ c ∈ cs, ¬ IsDelim c) ∧ cs ≠ ['.'] ∧
      (∀ c, cs.head? = some c → c ≠ '\'' ∧ c ≠ '`' ∧ c ≠ ',') ∧
      (cs.head? = some '#' → 2 ≤ cs.length) ∧ cs.take 2 ≠ ['#', '\\']) ∨
    ∃ c rest, cs = '#' :: '\\' :: c :: rest ∧ ∀ d ∈ rest, ¬ IsDelim d

/-- One token's characters together with the longest-match condition on the
following characters. -/
def Tok1 (cs : Chars) (t : Tok) (rest : Chars) : Prop :=
  match t with
  | .lp => cs = ['(']
  | .rp => cs = [')']
  | .dot => cs = ['.'] ∧ DelimNext rest
  | .quote name =>
      (cs = ['\''] ∧ name = "quote") ∨ (cs = ['`'] ∧ name = "quasiquote") ∨
        (cs = [','] ∧ name = "unquote" ∧ rest.head? ≠ some '@') ∨
        (cs = [',', '@'] ∧ name = "unquote-splicing")
  | .datumComment => cs = ['#', ';']
  | .atom (.str bs) => ∃ s, StrLit cs s ∧ bs = Unicode.utf8 s
  | .atom (.sym s) =>
      SymLit cs s ∨
        (Bare cs ∧ s = String.ofList cs ∧ DelimNext rest ∧
          (cs.head? = some '#' → rest.head? ≠ some '('))
  | .atom (.id _) => False

/-- Token sequences separated by intertoken space. -/
inductive Lex : Chars → List Tok → Prop where
  | done {s : Chars} : Space s → Lex s []
  | doneEof {s body : Chars} : Space s → NoLineEnd body → Lex (s ++ ';' :: body) []
  | step {s c rest : Chars} {t : Tok} {ts : List Tok} :
      Space s → Tok1 c t rest → Lex rest ts → Lex (s ++ c ++ rest) (t :: ts)

/-! ## Data (`<datum>`), with datum comments -/

mutual
  /-- One datum. -/
  inductive Datum : List Tok → SExp → Prop where
    | atom (a : Atom) : Datum [.atom a] (.atom a)
    | list {ts s : List Tok} {xs : List SExp} : Data ts xs → Skip s →
        Datum (.lp :: (ts ++ s ++ [.rp])) (listOf xs)
    | dotted {ts s₁ d s₂ : List Tok} {xs : List SExp} {tail : SExp} :
        Data ts xs → xs ≠ [] → Skip s₁ → Datum d tail → Skip s₂ →
        Datum (.lp :: (ts ++ .dot :: (s₁ ++ d ++ s₂ ++ [.rp]))) (xs.foldr .cons tail)
    | quote {name : String} {s d : List Tok} {x : SExp} : Skip s → Datum d x →
        Datum (.quote name :: (s ++ d)) (listOf [kw name, x])

  /-- A sequence of data, each possibly preceded by datum comments. -/
  inductive Data : List Tok → List SExp → Prop where
    | nil : Data [] []
    | cons {s d rest : List Tok} {x : SExp} {xs : List SExp} :
        Skip s → Datum d x → Data rest xs → Data (s ++ d ++ rest) (x :: xs)

  /-- Datum comments `#; <datum>` (atmosphere). -/
  inductive Skip : List Tok → Prop where
    | nil : Skip []
    | cons {s d rest : List Tok} {x : SExp} :
        Skip s → Datum d x → Skip rest → Skip (.datumComment :: (s ++ d ++ rest))
end

/-! ## The encoding relation -/

/-- The lexer as an encoding of token lists in text. -/
def lexRel : EncRel String (List Tok) := fun s ts => Lex s.toList ts

/-- A token list spells the document of its data (trailing datum comments allowed). -/
def docRel : EncRel (List Tok) SExp :=
  fun ts x => ∃ a b xs, ts = a ++ b ∧ Data a xs ∧ Skip b ∧ x = doc xs

/-- **Scheme S-expression text**. -/
def sexpScheme : EncRel String SExp := lexRel ⨾ docRel

/-- UTF-8 byte spellings. -/
def sexpSchemeBytes : EncRel (List UInt8) SExp := sexpScheme.push Unicode.utf8

end Silmaril.Formats.SExpEncoding.Scheme
