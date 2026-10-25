module

public import Silmaril.Encoding.TextExtras
public import Silmaril.Formats.SExp.Parser

/-!
# S-expression text encodings: the shared target AST

Two concrete-syntax conventions for S-expressions are given as encoding
relations `EncRel String SExp` with the *same* target, so that they can be
compared in the lattice `EncRel String SExp`:

* `EncodingWat.lean` — the WebAssembly text-format lexical conventions
  (SpecTec `6.0-text.lexical`, and the 2019 REC for Wasm 1.0);
* `EncodingScheme.lean` — R7RS-style Scheme conventions;
* `EncodingCompare.lean` — incomparability, a common sublanguage, and the
  relation of the existing `Formats.SExpParser.parseLexemes?` parser to both.

## Choice of AST

The target is `SExp := Formats.SExp2 Atom`: the existing dotted S-expression
type (`nil`/`atom`/`cons`), so improper lists of Scheme are representable while
WAT only ever produces proper lists.  It is *token preserving up to lexical
equivalence*: each atom records which lexical class it came from,

* `Atom.sym text` — a bare token (WAT keyword/number/reserved idchar run,
  Scheme symbol or other bare datum), with its raw text;
* `Atom.str bytes` — a string literal, *decoded* to its byte contents (WAT
  strings denote byte sequences, `\hh` escapes may produce non-UTF-8 bytes;
  Scheme strings denote character sequences and are stored UTF-8 encoded);
* `Atom.id name` — a WAT identifier, without the `$`; the plain (`$abc`) and
  quoted (`$"abc"`) spellings of the same name give the same atom.  Scheme
  never produces `id` atoms (`$abc` is the Scheme symbol `"$abc"`).

Spelling differences that the respective standards declare equivalent
(escapes, `$abc` vs `$"abc"`, whitespace, comments, annotations) are erased;
everything a later syntax layer can observe is kept.

A *document* (a whole text, possibly several top-level data) is represented
as the proper list of its top-level data (`doc`), so a document encoding is
still an `EncRel String SExp`.

The existing `Formats.SExpParser.Lexeme` (symbol vs string, string contents as
a `String`) maps into `Atom` by `Lexeme.toAtom`.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding

open Silmaril

/-- Character lists: the carrier of the grammars. -/
abbrev Chars := List Char

/-- Atoms, tagged with their lexical class. -/
inductive Atom where
  /-- A bare token, with its raw text. -/
  | sym (text : String)
  /-- A string literal, decoded to its bytes. -/
  | str (bytes : List UInt8)
  /-- A WAT identifier (name without the leading `$`). -/
  | id (name : String)
  deriving DecidableEq, Repr

/-- The target AST: dotted S-expressions over tagged atoms. -/
abbrev SExp := SExp2 Atom

/-- The proper list with the given elements. -/
def listOf (xs : List SExp) : SExp := xs.foldr .cons .nil

/-- A document is the proper list of its top-level data. -/
abbrev doc (xs : List SExp) : SExp := listOf xs

/-- A bare-token atom. -/
abbrev kw (s : String) : SExp := .atom (.sym s)

@[simp] theorem listOf_nil : listOf [] = .nil := rfl
@[simp] theorem listOf_cons (x : SExp) (xs : List SExp) :
    listOf (x :: xs) = .cons x (listOf xs) := rfl

theorem listOf_injective : Function.Injective listOf := by
  intro xs ys h
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [listOf]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listOf] at h
    | cons y ys =>
      simp only [listOf_cons, SExp2.cons.injEq] at h
      rw [h.1, ih h.2]

/-- Proper-list view (fails on atoms and dotted tails). -/
def toList? : SExp → Option (List SExp)
  | .nil => some []
  | .atom _ => none
  | .cons x rest => (x :: ·) <$> toList? rest

@[simp] theorem toList?_listOf (xs : List SExp) : toList? (listOf xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toList?, ih]

/-- The proper S-expressions are exactly the image of `listOf` on lists (plus atoms). -/
def Proper : SExp → Prop
  | .nil => True
  | .atom _ => True
  | .cons x rest => Proper x ∧ ProperTail rest
where
  /-- A nil-terminated spine of proper elements. -/
  ProperTail : SExp → Prop
    | .nil => True
    | .atom _ => False
    | .cons x rest => Proper x ∧ ProperTail rest

/-- The existing parser's lexemes as tagged atoms (string contents UTF-8). -/
def Lexeme.toAtom : SExpParser.Lexeme → Atom
  | .symbol s => .sym s
  | .string s => .str (Unicode.utf8 s)

/-- Character-class helpers shared by the grammars. -/
def IsHexDigit (c : Char) : Prop :=
  ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

instance (c : Char) : Decidable (IsHexDigit c) := by
  unfold IsHexDigit; infer_instance

/-- The value of a hexadecimal digit (`0` for non-digits). -/
def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- The UTF-8 bytes of one character. -/
def charUtf8 (c : Char) : List UInt8 := Unicode.utf8 (String.singleton c)

end Silmaril.Formats.SExpEncoding
