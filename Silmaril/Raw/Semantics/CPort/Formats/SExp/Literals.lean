module

public import Silmaril.Formats.SExp.Parser
public import Silmaril.Formats.Cbor.Bytes
public import Silmaril.Formats.Json.RfcParser

/-! Typed atom vocabularies layered over the shared S-expression lexer. -/

@[expose] public section

universe uα uβ uγ uι uκ uτ uυ uφ
variable {α : Type uα} {β : Type uβ} {γ : Type uγ}
variable {ι : Type uι} {κ : Type uκ} {n : Nat}
variable {τ : Type uτ} {υ : Type uυ} {φ : Type uφ}

namespace Silmaril.Formats

/-- The first richer atom vocabulary: unquoted symbols and decoded strings. -/
inductive StringSymbol where
  | symbol (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

/-- A Lisp-oriented vocabulary which additionally distinguishes keywords. -/
inductive KeywordSymbol where
  | symbol (value : String)
  | keyword (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

/-- A data-oriented atom vocabulary. Number spellings remain exact, just as in
`RfcJsonAtom`; byte strings use the compact `Bytes` representation. -/
inductive LiteralAtom where
  | symbol (value : String)
  | string (value : String)
  | number (literal : String)
  | bytes (value : Bytes)
  deriving DecidableEq

namespace SExpParser

/-!
`#hex#` is deliberately the sole byte syntax in this layer. It is unambiguous,
already used by the advanced S-expression format, and keeps vertical bars
available for a future Lisp-compatible quoted-symbol syntax. A `b"..."` syntax
would additionally have to specify whether ordinary characters are UTF-8 and
which of the text escapes denote individual octets.
-/

def Lexeme.toStringSymbol : Lexeme → StringSymbol
  | .symbol value => .symbol value
  | .string value => .string value

/-- Parse while distinguishing unquoted symbols from decoded string literals. -/
def parseStringSymbol? (text : String) : Option (SExp2 StringSymbol) :=
  SExp2.map Lexeme.toStringSymbol <$> parseLexemes? text

def keyword (value : String) : KeywordSymbol :=
  match value.toList with
  | ':' :: tail => if tail.isEmpty then .symbol value else .keyword (String.ofList tail)
  | _ => .symbol value

def Lexeme.toKeywordSymbol : Lexeme → KeywordSymbol
  | .symbol value => keyword value
  | .string value => .string value

/-- Parse Common-Lisp-style colon-prefixed keywords separately from symbols. -/
def parseKeywordSymbol? (text : String) : Option (SExp2 KeywordSymbol) :=
  SExp2.map Lexeme.toKeywordSymbol <$> parseLexemes? text

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let high ← hexDigit? high
      let low ← hexDigit? low
      let tail ← decodeHexChars rest
      some (UInt8.ofNat (high * 16 + low) :: tail)
  | [_] => none

/-- Decode the RFC advanced-S-expression hexadecimal spelling `#...#`.
The payload must contain an even number of hexadecimal digits. -/
def decodeHexBytes? (literal : String) : Option Bytes := do
  let chars := literal.toList
  let body ← match chars with
    | '#' :: rest => match rest.reverse with
      | '#' :: reversedBody => some reversedBody.reverse
      | _ => none
    | _ => none
  let bytes ← decodeHexChars body
  some ⟨bytes.toByteArray⟩

def numberLiteral? (value : String) : Option String :=
  match RfcJson.parse? value with
  | some (.scalar (some (.number literal))) => some literal
  | _ => none

def Lexeme.toLiteralAtom? : Lexeme → Option LiteralAtom
  | .string value => some (.string value)
  | .symbol value =>
      match decodeHexBytes? value with
      | some bytes => some (.bytes bytes)
      | none =>
          if value.startsWith "#" && value.endsWith "#" then none
          else match numberLiteral? value with
            | some literal => some (.number literal)
            | none => some (.symbol value)

def traverseAtoms (f : α → Option β) : SExp2 α → Option (SExp2 β)
  | .nil => some .nil
  | .atom value => .atom <$> f value
  | .cons car cdr => .cons <$> traverseAtoms f car <*> traverseAtoms f cdr

/-- Parse symbols, decoded strings, exact RFC-JSON number literals, and
`#hex#` byte literals. Malformed hash-delimited text remains a symbol unless it
has both delimiters, in which case malformed hex is rejected. -/
def parseLiterals? (text : String) : Option (SExp2 LiteralAtom) := do
  let value ← parseLexemes? text
  traverseAtoms Lexeme.toLiteralAtom? value

example : parseStringSymbol? "(name \"name\")" = some
    (.cons (.atom (.symbol "name")) (.cons (.atom (.string "name")) .nil)) := by
  cbv

example : (parseLiterals? "(42 -1.5e2 #00ff# \"42\")").isSome = true := by
  have h42 : "42".startsWith "#" = false := by simp
  have hneg : "-1.5e2".startsWith "#" = false := by simp
  cbv
  simp only [h42]
  cbv
  simp only [hneg]
  cbv

example : decodeHexBytes? "#00ff#" = some ⟨[0, 255].toByteArray⟩ := by
  cbv

example : (parseLiterals? "#0#").isNone = true := by
  have hs : "#0#".startsWith "#" = true := by simp
  have he : "#0#".endsWith "#" = true := by
    rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_iff]
    rw [String.copy_toSlice]
    decide +kernel
  cbv
  simp only [hs, he]
  rfl

example : parseStringSymbol? "\"line\\nnext\"" =
    some (.atom (.string "line\nnext")) := by cbv

example : (parseKeywordSymbol? "(put :key \"value\")").isSome = true := by
  cbv

end SExpParser
end Silmaril.Formats
