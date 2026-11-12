module

public import Silmaril.Encoding.Unicode

/-!
# OCaml string escaping

`spectec --ast` renders identifiers and texts with
`"\"" ^ String.escaped t ^ "\""` (`spectec/src/backend-ast/print.ml:12`).

The function being transcribed is OCaml 5.4.0's `String.escaped`
(`stdlib/string.ml:109`), a thin wrapper around `Bytes.unsafe_escape`
(`stdlib/bytes.ml:170`); `Bytes.escaped` (`stdlib/bytes.ml:224`) is the only
other caller, so this really is `Bytes.escaped` under another name.  The
escape table is `stdlib/bytes.ml:197-218` and the output-width table that
mirrors it is `stdlib/bytes.ml:186-190`.  (Under the pinned opam switch those
files are at `$OPAMROOT/spectec/lib/ocaml/`, with `OPAMROOT=$HOME/opam`.)

It is a *byte*-wise escape:

* `"` (`0x22`) and `\` (`0x5C`) become `\"` and `\\`, and newline, tab,
  carriage return and backspace become `\n`, `\t`, `\r`, `\b`;
* every *other* byte in `0x20`–`0x7E` stands for itself.  The six named
  cases above are matched first (`stdlib/bytes.ml:198-207`), so `0x22` and
  `0x5C` never reach the `' ' .. '~'` branch (`stdlib/bytes.ml:208`);
* every remaining byte becomes `\DDD` with exactly three decimal digits
  (`stdlib/bytes.ml:209-217`).

It is `Bytes.escaped` and not `Char.escaped` (`stdlib/char.ml:29`): the latter
also escapes `'` as `\'` (`stdlib/char.ml:30`), which `String.escaped` does
not, and a SpecTec identifier may well contain an apostrophe.

`unescapeBytes?` is the exact inverse: it accepts a `\DDD` escape only for
those bytes that `escapeByte` would render that way, so `escape` and
`unescape?` are mutually inverse rather than merely round-tripping.

Since OCaml strings are byte strings and Lean strings are sequences of Unicode
scalars, `escape` escapes the UTF-8 encoding of its argument
(`Silmaril.Unicode.utf8`) and `unescape?` fails on byte sequences that are not
well-formed UTF-8.  No pinned specification contains such a text: every
`--ast` file at the pin is pure ASCII.

## Where the proofs are

This file has the definitions only; the facts live in
`Silmaril/SpecTec/SExp/EscapeFacts.lean`.  `Escape.escapeBytes_utf8` relates
`escapeChar` to the UTF-8 encoding, and `Escape.unescape?_escape`,
`Escape.escape_of_unescape?`, `Escape.unquote?_quote` and
`Escape.quote_of_unquote?` are the round-trip theorems in both directions.
-/

@[expose] public section

namespace Silmaril.SpecTec.Escape

/-- The ASCII digit for `n < 10`. -/
def digitChar (n : Nat) : Char := Char.ofNat (n + 48)

/-- The value of an ASCII digit. -/
def digitVal? (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- The bytes that `String.escaped` renders as a two-character escape. -/
def IsNamed (n : Nat) : Prop := n = 34 ∨ n = 92 ∨ n = 10 ∨ n = 9 ∨ n = 13 ∨ n = 8

instance (n : Nat) : Decidable (IsNamed n) := by unfold IsNamed; infer_instance

/-- The bytes that `String.escaped` passes through unchanged. -/
def IsLiteral (n : Nat) : Prop := 32 ≤ n ∧ n ≤ 126 ∧ ¬ IsNamed n

instance (n : Nat) : Decidable (IsLiteral n) := by unfold IsLiteral; infer_instance

/-- The bytes that `String.escaped` renders as `\DDD`. -/
def IsDecimal (n : Nat) : Prop := n < 256 ∧ ¬ IsNamed n ∧ ¬ IsLiteral n

instance (n : Nat) : Decidable (IsDecimal n) := by unfold IsDecimal; infer_instance

/-- `String.escaped` on a single byte (`stdlib/bytes.ml:197-218`). -/
def escapeByte (b : UInt8) : List Char :=
  let n := b.toNat
  if n = 34 then ['\\', '"']
  else if n = 92 then ['\\', '\\']
  else if n = 10 then ['\\', 'n']
  else if n = 9 then ['\\', 't']
  else if n = 13 then ['\\', 'r']
  else if n = 8 then ['\\', 'b']
  else if 32 ≤ n ∧ n ≤ 126 then [Char.ofNat n]
  else ['\\', digitChar (n / 100), digitChar (n / 10 % 10), digitChar (n % 10)]

/-- `String.escaped` on a byte string. -/
def escapeBytes : List UInt8 → List Char
  | [] => []
  | b :: bs => escapeByte b ++ escapeBytes bs

/-- `String.escaped` on the UTF-8 encoding of one Unicode scalar.

This is `escapeByte` applied to each byte of `String.utf8EncodeChar c`,
written so that it reduces in the kernel without unfolding `String.toUTF8`,
which is opaque.  `Escape.escapeBytes_utf8`, in
`Silmaril/SpecTec/SExp/EscapeFacts.lean`, relates the two. -/
def escapeChar (c : Char) : List Char :=
  let n := c.toNat
  if n = 34 then ['\\', '"']
  else if n = 92 then ['\\', '\\']
  else if n = 10 then ['\\', 'n']
  else if n = 9 then ['\\', 't']
  else if n = 13 then ['\\', 'r']
  else if n = 8 then ['\\', 'b']
  else if 32 ≤ n ∧ n ≤ 126 then [c]
  else (String.utf8EncodeChar c).flatMap escapeByte

/-- `String.escaped t` (`spectec/src/backend-ast/print.ml:12`). -/
def escape (s : String) : String := String.ofList (s.toList.flatMap escapeChar)

/-- `"\"" ^ String.escaped t ^ "\""` (`spectec/src/backend-ast/print.ml:12`):
the atom that `--ast` emits for a text or an identifier. -/
def quote (s : String) : String := "\"" ++ escape s ++ "\""

/-- The inverse of `escapeBytes`. -/
def unescapeBytes? : List Char → Option (List UInt8)
  | [] => some []
  | c :: rest =>
      if c = '\\' then
        match rest with
        | [] => none
        | e :: rest' =>
            if e = '"' then (34 :: ·) <$> unescapeBytes? rest'
            else if e = '\\' then (92 :: ·) <$> unescapeBytes? rest'
            else if e = 'n' then (10 :: ·) <$> unescapeBytes? rest'
            else if e = 't' then (9 :: ·) <$> unescapeBytes? rest'
            else if e = 'r' then (13 :: ·) <$> unescapeBytes? rest'
            else if e = 'b' then (8 :: ·) <$> unescapeBytes? rest'
            else
              match rest' with
              | d₂ :: d₃ :: rest'' =>
                  match digitVal? e, digitVal? d₂, digitVal? d₃ with
                  | some a₁, some a₂, some a₃ =>
                      let n := a₁ * 100 + a₂ * 10 + a₃
                      if IsDecimal n then
                        (UInt8.ofNat n :: ·) <$> unescapeBytes? rest''
                      else none
                  | _, _, _ => none
              | _ => none
      else if IsLiteral c.toNat then
        (UInt8.ofNat c.toNat :: ·) <$> unescapeBytes? rest
      else none

/-- The inverse of `escape`; `none` when the escaped bytes are not
well-formed UTF-8. -/
def unescape? (s : String) : Option String :=
  (unescapeBytes? s.toList).bind Unicode.utf8?

/-- The inverse of `quote`: strip the delimiting quotes, then unescape. -/
def unquote? (s : String) : Option String :=
  match s.toList with
  | '"' :: rest =>
      match rest.reverse with
      | '"' :: body => unescape? (String.ofList body.reverse)
      | _ => none
  | _ => none

end Silmaril.SpecTec.Escape
