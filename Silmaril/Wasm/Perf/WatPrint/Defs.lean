module

public import Silmaril.Wasm.Component.Wat.Defs

/-!
# A string-builder WAT printer

`Wat.Sexp.pp` builds `List Char` and decides the layout of every list by printing it flat
first (`one.length`), so printing a component of a few MB allocates hundreds of MB of list
cells. `ppS`/`ppLS` write the same characters into a `String` accumulator, and decide the
layout from `flatLen`, the length of the flat printing computed without building it.

`Thms.lean`: `printAllF_eq : printAllF = Sexp.printAll` and `printWatF_eq : printWatF =
Wit.Tool.printWat`, so the round-trip theorem of the printer (`Sexp.read_print`) and the
tool theorems hold for the fast printer.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.WatPrint

open Silmaril.Wasm.Component.Wat (Sexp)
open Silmaril.Wasm.Component.Wat.Sexp (escByte quote hexDigit width breakSep)

/-- `escByte b` appended to `acc`. -/
@[inline] def escPush (b : UInt8) (acc : String) : String :=
  if 0x20 ≤ b.toNat ∧ b.toNat < 0x7f ∧ b.toNat ≠ 0x22 ∧ b.toNat ≠ 0x5c then
    acc.push (Char.ofNat b.toNat)
  else ((acc.push '\\').push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))

/-- `bs.flatMap escByte` appended to `acc` (tail-recursive). -/
def escAll : List UInt8 → String → String
  | [], acc => acc
  | b :: bs, acc => escAll bs (escPush b acc)

/-- The length of `escByte b`. -/
@[inline] def escW (b : UInt8) : Nat :=
  if 0x20 ≤ b.toNat ∧ b.toNat < 0x7f ∧ b.toNat ≠ 0x22 ∧ b.toNat ≠ 0x5c then 1 else 3

/-- `n` plus the length of `bs.flatMap escByte` (tail-recursive). -/
def escLen : List UInt8 → Nat → Nat
  | [], n => n
  | b :: bs, n => escLen bs (n + escW b)

/-- `quote bs` appended to `acc`. -/
def quoteS (bs : List UInt8) (acc : String) : String := (escAll bs (acc.push '"')).push '"'

mutual
/-- The length of `pp true 0 s`, the flat printing of `s`. -/
def flatLen : Sexp → Nat
  | .atom a => a.length
  | .str b => escLen b 2
  | .list xs => flatLenL xs + 2

/-- The length of `ppL true (fun _ _ => [' ']) 0 xs`. -/
def flatLenL : List Sexp → Nat
  | [] => 0
  | [x] => flatLen x
  | x :: y :: xs => flatLen x + 1 + flatLenL (y :: xs)
end

mutual
/-- `Sexp.pp flat ind s` appended to `acc`. -/
def ppS (flat : Bool) (ind : Nat) : Sexp → String → String
  | .atom a, acc => acc ++ a
  | .str b, acc => quoteS b acc
  | .list xs, acc =>
    if flat || ind + (flatLenL xs + 2) ≤ width then
      (ppLS true (fun _ _ => [' ']) 0 xs (acc.push '(')).push ')'
    else (ppLS false (breakSep (ind + 2)) (ind + 2) xs (acc.push '(')).push ')'

/-- `Sexp.ppL flat sep ind xs` appended to `acc`. -/
def ppLS (flat : Bool) (sep : Sexp → Sexp → List Char) (ind : Nat) :
    List Sexp → String → String
  | [], acc => acc
  | [x], acc => ppS flat ind x acc
  | x :: y :: xs, acc => ppLS flat sep ind (y :: xs) (ppS flat ind x acc ++ String.ofList (sep x y))
end

/-- **`Sexp.printAll` with a string builder** (`printAllF_eq`). -/
def printAllF (ss : List Sexp) : String :=
  ss.foldl (fun acc s => (ppS false 0 s acc).push '\n') ""

/-- `Wat.print` with `printAllF`. -/
def printF (c : Silmaril.Wasm.Component.Binary.Ast) : String :=
  printAllF [Silmaril.Wasm.Component.Wat.toSexp c]

/-- `wasm-wit print` (`Wit.Tool.printWat`) with `printF` (`printWatF_eq`). -/
def printWatF (b : ByteArray) : Except String String :=
  match Silmaril.Wasm.Component.Binary.parse b with
  | .ok c => .ok (printF c)
  | .error _ => .error "malformed component"

end Silmaril.Wasm.Perf.WatPrint
