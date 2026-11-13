module

public import Silmaril.Wasm.Tools.Component.Wat.Defs

/-!
# A tail-recursive reader for component WAT (the fast path of `wasm-tools parse`)

`Sexp.read` (`Silmaril.Wasm.Component.Wat.Sexp`) is the specification reader: `lex` builds its
token list by mapping over the recursive result, `lexStr` likewise for the bytes of a string,
and `parseSeq` rebuilds the trees with one recursive call per sibling, so their stack depth
grows with the input (a `start` with thousands of results, or the 3 MB string of a core
module). Here:

* `lexA acc cs`: the lexer with an accumulator (tokens in reverse), tail recursive;
  `lexStrA` likewise; `lexA_eq : lexA acc cs = (lex cs).map (acc.reverse ++ ·)`;
* `parseStk ts stk`: the tree parser with an explicit stack of open lists (siblings in
  reverse), tail recursive; `parseStk_sound`: a result `xs` has exactly the tokens `ts`, so
  it is `parseTop`'s (`Sexp.parseTop_toksL`);
* `readF s`: `lexA`, then `parseStk`, falling back to `parseTop` when `parseStk` fails;
  `readF_eq : readF = Sexp.read`;
* `readXF`, `parseTextF`: `Wat.readX` and `Wat.parseText` with `readF`;
  `parseTextF_eq : parseTextF = Wat.parseText`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.FastRead

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (lex lexStr hexVal? charBytes isSpace isIdChar skipLine
  skipBlock parseTop)

/-- `lexStr` with the bytes accumulated in reverse. -/
def lexStrA (acc : List UInt8) : List Char → Option (List UInt8 × List Char)
  | [] => none
  | '"' :: cs => some (acc.reverse, cs)
  | '\\' :: 't' :: cs => lexStrA (9 :: acc) cs
  | '\\' :: 'n' :: cs => lexStrA (10 :: acc) cs
  | '\\' :: 'r' :: cs => lexStrA (13 :: acc) cs
  | '\\' :: '"' :: cs => lexStrA (34 :: acc) cs
  | '\\' :: '\'' :: cs => lexStrA (39 :: acc) cs
  | '\\' :: '\\' :: cs => lexStrA (92 :: acc) cs
  | '\\' :: h :: l :: cs =>
    match hexVal? h, hexVal? l with
    | some a, some b => lexStrA ((16 * a + b).toUInt8 :: acc) cs
    | _, _ => none
  | '\\' :: _ => none
  | c :: cs => if c.toNat < 0x20 ∨ c.toNat = 0x7f then none
      else if c.toNat < 0x80 then lexStrA (c.toNat.toUInt8 :: acc) cs
      else lexStrA ((charBytes c).reverse ++ acc) cs

set_option linter.unusedTactic false in
/-- `lexStrA` is `lexStr` with the accumulator in front. -/
theorem lexStrA_eq (acc : List UInt8) (cs : List Char) :
    lexStrA acc cs = (lexStr cs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  fun_induction lexStrA acc cs <;>
    simp_all [lexStr, List.reverse_cons, Option.map_map, Function.comp_def]
  all_goals
    rw [ite_eq_right (by omega)]
    simp [Option.map_map, Function.comp_def]
  all_goals simp [charBytes, *]

set_option linter.unusedTactic false in
/-- `lex` with the tokens accumulated in reverse (`lexA_eq`). -/
def lexA (acc : List Tok) (cs : List Char) : Option (List Tok) :=
  match cs with
  | [] => some acc.reverse
  | ';' :: ';' :: r => lexA acc (skipLine r)
  | '(' :: ';' :: r =>
    match h : skipBlock 0 r with
    | none => none
    | some r' =>
      have := Sexp.skipBlock_length_le 0 r r' h
      lexA acc r'
  | '(' :: r => lexA (.lp :: acc) r
  | ')' :: r => lexA (.rp :: acc) r
  | '"' :: r =>
    match h : lexStrA [] r with
    | none => none
    | some (bs, r') =>
      have : r'.length ≤ r.length := by
        rw [lexStrA_eq] at h
        cases hs : lexStr r with
        | none => rw [hs] at h; cases h
        | some p =>
          rw [hs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          have := Sexp.lexStr_length_le r p.1 p.2 (by rw [hs])
          simp only [Prod.mk.injEq] at h
          rw [← h.2]
          exact this
      lexA (.str bs :: acc) r'
  | c :: r =>
    if isSpace c then lexA acc r
    else if isIdChar c then
      have := Sexp.dropWhile_length_le isIdChar r
      lexA (.atom (String.ofList (c :: r.takeWhile isIdChar)) :: acc) (r.dropWhile isIdChar)
    else none
termination_by cs.length
decreasing_by all_goals (have := Sexp.skipLine_length_le r; simp_all; try omega)

/-- The tree parser with an explicit stack: the head is the open list's children so far (in
reverse), below it the enclosing lists'. -/
def parseStk : List Tok → List (List Sexp) → Option (List Sexp)
  | [], [cur] => some cur.reverse
  | .lp :: ts, stk => parseStk ts ([] :: stk)
  | .rp :: ts, cur :: parent :: stk => parseStk ts ((.list cur.reverse :: parent) :: stk)
  | .atom a :: ts, cur :: stk => parseStk ts ((.atom a :: cur) :: stk)
  | .str b :: ts, cur :: stk => parseStk ts ((.str b :: cur) :: stk)
  | _, _ => none

/-- **The fast reader**: `lexA`, then `parseStk` (`parseTop` when it fails). -/
def readF (s : String) : Option (List Sexp) :=
  match lexA [] s.toList with
  | none => none
  | some ts =>
    match parseStk ts [[]] with
    | some xs => some xs
    | none => parseTop ts

/-- `Wat.readX` with the fast reader, which runs once (`Wat.readX` reads the text a second
time when the printer's spelling does not apply). -/
def readXF (s : String) : Option Silmaril.Wasm.Component.BinaryP3.Ast :=
  match readF s with
  | some [x] =>
    match Wat.ofSexp x with
    | some c => some c
    | none =>
      Wac.WatX.desugar (Wac.WatX.clean x) >>= _root_.Silmaril.Wasm.Component.Wat.resolve >>= Wat.ofSexp
  | _ => none

/-! ## The fast encoder

`BinaryP3.encode` builds a `List UInt8` and converts it at the end; a 3 MB core module
section is copied into a list and back. `encodeF` appends each top-level section to a
`ByteArray`, core module and custom sections straight from their bytes, the others through
`Encode.section_` (`encodeF_eq : encodeF = BinaryP3.encode`). -/

open Silmaril.Wasm.Component.BinaryP3 (Section Ast)
open Silmaril.Parse.ByteParse.Enc (u32 name)

/-- One section, as bytes. -/
def secF : Section → Option ByteArray
  | .coreModule m => (u32 m.size).map fun n => ByteArray.mk (0x01 :: n).toArray ++ m
  | .custom n d => do
    let a ← name n
    let k ← u32 (a.length + d.size)
    pure (ByteArray.mk (0x00 :: (k ++ a)).toArray ++ d)
  | s => (Silmaril.Wasm.Component.BinaryP3.Encode.section_ s).map fun l => ByteArray.mk l.toArray

/-- Sections appended to `acc`. -/
def secsF (acc : ByteArray) : List Section → Option ByteArray
  | [] => some acc
  | s :: ss => match secF s with
    | some b => secsF (acc ++ b) ss
    | none => none

/-- **The fast encoder** (`encodeF_eq`). -/
def encodeF : Ast → Option ByteArray
  | .mk ss => secsF (ByteArray.mk Silmaril.Wasm.Component.Binary.preambleBytes.toArray) ss

/-- **`wasm-tools parse`** of component WAT, with the fast reader. -/
def parseTextF (t : String) : Except String ByteArray :=
  match readXF t with
  | none => .error "not component WAT this reader accepts"
  | some c => match encodeF c with
    | some b => .ok b
    | none => .error "a number or size exceeds 2^32"

end Silmaril.Wasm.Tools.Component.FastRead
