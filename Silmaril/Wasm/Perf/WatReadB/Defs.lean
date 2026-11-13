module

public import Silmaril.Wasm.Perf.WatRead.Defs

/-!
# A WAT lexer over the UTF-8 bytes

`WatRead.lexT` (the tail-recursive `Sexp.lex`) runs on `String.toList`: a `List Char` of the
whole text, 24 bytes per character (`wasm-wit parse` of the 21 MB WAT of a 10.8 MB component
held 500 MB of it). Here the lexer reads the text's UTF-8 bytes (`String.toByteArray`) by index,
each byte read as the character `chr x` (`Char.ofNat x.toNat`): `skipLineB`, `skipBlockB`,
`lexStrB`, `scanId`/`idChars`, `lexB` are `skipLine`, `skipBlock`, `lexStrT`, `takeWhile`/
`dropWhile isIdChar` and `lexT` on the characters `cs b i = (b.toList.drop i).map chr`
(`Thms.lean`). When every byte is ASCII, `cs s.toByteArray 0 = s.toList` (`toList_ascii`), so
`readB` (the byte lexer on ASCII texts, `WatRead.readF` otherwise) is `Sexp.read`
(`readB_eq`), and `parseWatB` is `Wit.Tool.parseWat` (`parseWatB_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.WatReadB

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (hexVal? charBytes isSpace isIdChar parseTop)

/-- A byte read as a character. -/
@[inline] def chr (x : UInt8) : Char := Char.ofNat x.toNat

/-- `skipLine` on the bytes from `i`: the index after the next newline (or the end). -/
def skipLineB (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    if chr b[i] = '\n' then i + 1 else skipLineB b (i + 1)
  else i
termination_by b.size - i

/-- `skipBlock` on the bytes from `i`. -/
def skipBlockB (b : ByteArray) (d i : Nat) : Option Nat :=
  if h : i < b.size then
    if h' : i + 1 < b.size then
      if chr b[i] = ';' ∧ chr b[i + 1] = ')' then
        match d with
        | 0 => some (i + 2)
        | d + 1 => skipBlockB b d (i + 2)
      else if chr b[i] = '(' ∧ chr b[i + 1] = ';' then skipBlockB b (d + 1) (i + 2)
      else skipBlockB b d (i + 1)
    else skipBlockB b d (i + 1)
  else none
termination_by b.size - i

/-- `lexStrT` on the bytes from `i`: the literal's bytes and the index after the closing
quote. -/
def lexStrB (b : ByteArray) (i : Nat) (acc : List UInt8) : Option (List UInt8 × Nat) :=
  if h : i < b.size then
    if chr b[i] = '"' then some (acc.reverse, i + 1)
    else if chr b[i] = '\\' then
      if h₁ : i + 1 < b.size then
        if chr b[i + 1] = 't' then lexStrB b (i + 2) (9 :: acc)
        else if chr b[i + 1] = 'n' then lexStrB b (i + 2) (10 :: acc)
        else if chr b[i + 1] = 'r' then lexStrB b (i + 2) (13 :: acc)
        else if chr b[i + 1] = '"' then lexStrB b (i + 2) (34 :: acc)
        else if chr b[i + 1] = '\'' then lexStrB b (i + 2) (39 :: acc)
        else if chr b[i + 1] = '\\' then lexStrB b (i + 2) (92 :: acc)
        else if h₂ : i + 2 < b.size then
          match hexVal? (chr b[i + 1]), hexVal? (chr b[i + 2]) with
          | some x, some y => lexStrB b (i + 3) ((16 * x + y).toUInt8 :: acc)
          | _, _ => none
        else none
      else none
    else if (chr b[i]).toNat < 0x20 ∨ (chr b[i]).toNat = 0x7f then none
    else lexStrB b (i + 1) ((charBytes (chr b[i])).reverse ++ acc)
  else none
termination_by b.size - i

/-- The first index from `i` whose byte is not an `idchar` (or the end). -/
def scanId (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    if isIdChar (chr b[i]) then scanId b (i + 1) else i
  else i
termination_by b.size - i

/-- The characters of the bytes from `i` to `j`. -/
def idChars (b : ByteArray) (i j : Nat) : List Char :=
  if h : i < j ∧ i < b.size then chr b[i] :: idChars b (i + 1) j else []
termination_by b.size - i

/-- The character of the byte at `i`, if any. -/
@[inline] def nx (b : ByteArray) (i : Nat) : Option Char :=
  if h : i < b.size then some (chr b[i]) else none

/-- `lexT` on the bytes from `i`. -/
def lexB (b : ByteArray) (i : Nat) (acc : List Tok) : Option (List Tok) :=
  if h : i < b.size then
    if chr b[i] = ';' ∧ nx b (i + 1) = some ';' then
      let j := skipLineB b (i + 2)
      if i < j then lexB b j acc else none
    else if chr b[i] = '(' ∧ nx b (i + 1) = some ';' then
      match skipBlockB b 0 (i + 2) with
      | none => none
      | some j => if i < j then lexB b j acc else none
    else if chr b[i] = '(' then lexB b (i + 1) (Tok.lp :: acc)
    else if chr b[i] = ')' then lexB b (i + 1) (Tok.rp :: acc)
    else if chr b[i] = '"' then
      match lexStrB b (i + 1) [] with
      | none => none
      | some (bs, j) => if i < j then lexB b j (Tok.str bs :: acc) else none
    else if isSpace (chr b[i]) then lexB b (i + 1) acc
    else if isIdChar (chr b[i]) then
      let j := scanId b (i + 1)
      if i < j then lexB b j (Tok.atom (String.ofList (chr b[i] :: idChars b (i + 1) j)) :: acc)
      else none
    else none
  else some acc.reverse
termination_by b.size - i
decreasing_by all_goals omega

/-- Every byte is ASCII. -/
def isAscii (b : ByteArray) : Bool := b.data.all (· < 128)

/-- `Sexp.read` with the byte lexer on ASCII texts (`readB_eq`); other texts go through
`WatRead.readF`. -/
def readB (s : String) : Option (List Sexp) :=
  if isAscii s.toByteArray then lexB s.toByteArray 0 [] >>= parseTop else WatRead.readF s

/-- `Wat.read` through `readB`. -/
def readWatB (s : String) : Option Silmaril.Wasm.Component.Binary.Ast :=
  match readB s with
  | some [x] => Silmaril.Wasm.Component.Wat.ofSexp x
  | _ => none

/-- **`wasm-wit parse`** (`Wit.Tool.parseWat`) through `readWatB` and the `ByteArray` encoder
`EncodeB.encodeF` (`parseWatB_eq`). -/
def parseWatB (t : String) : Except String ByteArray :=
  match readWatB t with
  | none => .error "not component WAT this reader accepts"
  | some c => match Silmaril.Wasm.Perf.EncodeB.encodeF c with
    | some b => .ok b
    | none => .error "a number or size exceeds 2^32"

end Silmaril.Wasm.Perf.WatReadB
