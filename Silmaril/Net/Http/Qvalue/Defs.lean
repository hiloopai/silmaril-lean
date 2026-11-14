module

public import Silmaril.Net.Http.Abnf.Defs

/-!
# Quality values (RFC 9110 §12.4.2)

`qvalue = ( "0" [ "." 0*3DIGIT ] ) / ( "1" [ "." 0*3("0") ] )`, as thousandths
(`parseQvalue`: `"0.5"` is `500`, `"1"` is `1000`). Shared by every field with a
`weight`: `Accept-Encoding` (`Silmaril.Net.Http.ContentCoding`) and HTTP/1.1's `TE`
(`Silmaril.Net.Http1.Codings`). The bound `parseQvalue_le` is in `Qvalue.Thms`.
-/

@[expose] public section

namespace Silmaril.Net.Http.Qvalue

open Silmaril.Net.Http.Abnf

/-- The value of an ASCII digit. -/
def digit? (b : UInt8) : Option Nat := if isDigit b then some (b.toNat - 0x30) else none

/-- Up to three decimals after the point, as thousandths. -/
def thousandths : List UInt8 → Option Nat
  | [] => some 0
  | [a] => (digit? a).map (· * 100)
  | [a, b] => (digit? a).bind fun x => (digit? b).map fun y => x * 100 + y * 10
  | [a, b, c] =>
    (digit? a).bind fun x => (digit? b).bind fun y => (digit? c).map fun z => x * 100 + y * 10 + z
  | _ => none

/-- `qvalue = ( "0" [ "." 0*3DIGIT ] ) / ( "1" [ "." 0*3("0") ] )`, in thousandths. -/
def parseQvalue : List UInt8 → Option Nat
  | [0x30] => some 0
  | [0x31] => some 1000
  | 0x30 :: 0x2E :: ds => thousandths ds
  | 0x31 :: 0x2E :: ds => if ds.length ≤ 3 ∧ ds.all (· == 0x30) then some 1000 else none
  | _ => none

end Silmaril.Net.Http.Qvalue
