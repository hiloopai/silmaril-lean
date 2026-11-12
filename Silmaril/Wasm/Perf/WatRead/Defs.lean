module

public import Silmaril.Wasm.Component.Wat.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Perf.EncodeB.Defs

/-!
# A tail-recursive WAT lexer

`Wat.Sexp.lexStr` recurses once per character of a string literal and `Wat.Sexp.lex` once per
token, so `wasm-wit parse` overflows the stack on a WAT text whose core modules are a few MB
of `(core module binary "…")` (observed: 21 MB of WAT, "Stack overflow detected"). `lexStrT`
and `lexT` are the same functions with accumulators (in reverse), and `readF`, `readWatF`,
`parseWatF` are `Sexp.read`, `Wat.read` and `Wit.Tool.parseWat` over them (`parseWatF` encodes
with `EncodeB.encodeF`, called directly: this module imports no theorem header).

`Thms.lean`: `lexStrT_eq`, `lexT_eq`, `readF_eq : readF = Sexp.read` (also `@[csimp]`),
`parseWatF_eq : parseWatF = Wit.Tool.parseWat`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.WatRead

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (hexVal? charBytes isSpace isIdChar skipLine skipBlock
  skipBlock_length_le lexStr parseTop dropWhile_length_le skipLine_length_le)

/-- `lexStr` with the bytes accumulated in reverse in `acc`. -/
def lexStrT : List Char → List UInt8 → Option (List UInt8 × List Char)
  | [], _ => none
  | '"' :: cs, acc => some (acc.reverse, cs)
  | '\\' :: 't' :: cs, acc => lexStrT cs (9 :: acc)
  | '\\' :: 'n' :: cs, acc => lexStrT cs (10 :: acc)
  | '\\' :: 'r' :: cs, acc => lexStrT cs (13 :: acc)
  | '\\' :: '"' :: cs, acc => lexStrT cs (34 :: acc)
  | '\\' :: '\'' :: cs, acc => lexStrT cs (39 :: acc)
  | '\\' :: '\\' :: cs, acc => lexStrT cs (92 :: acc)
  | '\\' :: h :: l :: cs, acc =>
    match hexVal? h, hexVal? l with
    | some a, some b => lexStrT cs ((16 * a + b).toUInt8 :: acc)
    | _, _ => none
  | '\\' :: _, _ => none
  | c :: cs, acc => if c.toNat < 0x20 ∨ c.toNat = 0x7f then none
      else lexStrT cs ((charBytes c).reverse ++ acc)

/-- `lexStr` through `lexStrT`. -/
@[inline] def lexStrF (cs : List Char) : Option (List UInt8 × List Char) := lexStrT cs []

theorem lexStrT_eq (cs : List Char) : ∀ acc : List UInt8,
    lexStrT cs acc = (lexStr cs).map fun p => (acc.reverse ++ p.1, p.2) := by
  fun_induction lexStr cs <;> intro acc <;> simp_all [lexStrT, Function.comp_def]

theorem lexStrF_eq (cs : List Char) : lexStrF cs = lexStr cs := by
  simp only [lexStrF, lexStrT_eq, List.reverse_nil, List.nil_append, Option.map_id']

theorem lexStrF_length_le (cs : List Char) (bs : List UInt8) (r : List Char)
    (h : lexStrF cs = some (bs, r)) : r.length ≤ cs.length :=
  Silmaril.Wasm.Component.Wat.Sexp.lexStr_length_le cs bs r (by rw [← lexStrF_eq]; exact h)

/-- `lexStrF_eq` for the compiler: below, and in modules importing this one, `lexStr` runs as
`lexStrF`. -/
@[csimp] theorem lexStr_eq_lexStrF : @lexStr = @lexStrF := by
  funext cs
  exact (lexStrF_eq cs).symm

set_option linter.unusedTactic false in
/-- `Sexp.lex` with the tokens accumulated in reverse in `acc` (string literals through
`lexStr`, which the compiler runs as `lexStrF`). -/
def lexT (cs : List Char) (acc : List Tok) : Option (List Tok) :=
  match cs with
  | [] => some acc.reverse
  | ';' :: ';' :: r => lexT (skipLine r) acc
  | '(' :: ';' :: r =>
    match h : skipBlock 0 r with
    | none => none
    | some r' =>
      have := skipBlock_length_le 0 r r' h
      lexT r' acc
  | '(' :: r => lexT r (Tok.lp :: acc)
  | ')' :: r => lexT r (Tok.rp :: acc)
  | '"' :: r =>
    match h : lexStr r with
    | none => none
    | some (bs, r') =>
      have := Silmaril.Wasm.Component.Wat.Sexp.lexStr_length_le r bs r' h
      lexT r' (Tok.str bs :: acc)
  | c :: r =>
    if isSpace c then lexT r acc
    else if isIdChar c then
      have := dropWhile_length_le isIdChar r
      lexT (r.dropWhile isIdChar) (Tok.atom (String.ofList (c :: r.takeWhile isIdChar)) :: acc)
    else none
termination_by cs.length
decreasing_by all_goals (have := skipLine_length_le r; simp_all; try omega)

/-- `Sexp.read` through `lexT` (`readF_eq`). -/
def readF (s : String) : Option (List Sexp) := lexT s.toList [] >>= parseTop

/-- `Wat.read` through `readF`. -/
def readWatF (s : String) : Option Silmaril.Wasm.Component.Binary.Ast :=
  match readF s with
  | some [x] => Silmaril.Wasm.Component.Wat.ofSexp x
  | _ => none

/-- `wasm-wit parse` (`Wit.Tool.parseWat`) through `readWatF` and the `ByteArray` encoder
`EncodeB.encodeF` (`parseWatF_eq`). -/
def parseWatF (t : String) : Except String ByteArray :=
  match readWatF t with
  | none => .error "not component WAT this reader accepts"
  | some c => match Silmaril.Wasm.Perf.EncodeB.encodeF c with
    | some b => .ok b
    | none => .error "a number or size exceeds 2^32"

end Silmaril.Wasm.Perf.WatRead
