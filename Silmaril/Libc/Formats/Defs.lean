module

public import Silmaril.Libc.Stdio.Defs

/-!
# A restricted `printf`/`scanf` format language

The restricted `printf`/`scanf` formats of a small C library: the conversions `%d %ld %lld %u %x %s %c` (and `%%`), white
space and literal bytes (`parseFmt`), and what `scanf` reads from its input (`scanPieces`). The
definitions are pure functions of bytes, kept apart from the process model so that the abstract
`stdio` contracts (`Silmaril.Libc.Contract.Stdio`) reuse them without the dynamic loader.
-/

@[expose] public section

namespace Silmaril.Libc.Formats

open Silmaril.X86 (Byte)
open Silmaril.Libc.Stdio (isSpace isDigit scanInt)

/-! ## Formats -/

/-- The conversions. -/
inductive Conv where
  | d | ld | lld | u | x | s | c
  deriving DecidableEq, Repr

/-- A piece of a format: a literal byte, a white-space byte, a conversion. -/
inductive Piece where
  | lit (b : Byte)
  | ws (b : Byte)
  | conv (k : Conv)

/-- The byte of an ASCII character. -/
abbrev ch (c : Char) : Byte := BitVec.ofNat 8 c.toNat

/-- The conversion after a `%` (and the rest of the format). -/
def convOf : List Byte → Option (Conv × List Byte)
  | c :: r =>
    if c = ch 'd' then some (.d, r)
    else if c = ch 'u' then some (.u, r)
    else if c = ch 'x' then some (.x, r)
    else if c = ch 's' then some (.s, r)
    else if c = ch 'c' then some (.c, r)
    else if c = ch 'l' then
      match r with
      | c2 :: r2 =>
        if c2 = ch 'd' then some (.ld, r2)
        else if c2 = ch 'l' then
          match r2 with
          | c3 :: r3 => if c3 = ch 'd' then some (.lld, r3) else none
          | [] => none
        else none
      | [] => none
    else none
  | [] => none

/-- Parse a format with `fuel` steps. -/
def parseAux : Nat → List Byte → Option (List Piece)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, b :: rest =>
    if b = ch '%' then
      match rest with
      | c :: r =>
        if c = ch '%' then (parseAux k r).map (.lit b :: ·)
        else match convOf rest with
          | some (cv, r') => (parseAux k r').map (.conv cv :: ·)
          | none => none
      | [] => none
    else if isSpace b then (parseAux k rest).map (.ws b :: ·)
    else (parseAux k rest).map (.lit b :: ·)

/-- **The restricted format language** (module doc). -/
def parseFmt (f : List Byte) : Option (List Piece) := parseAux (f.length + 1) f

/-- The number of conversions. -/
def convCount : List Piece → Nat
  | [] => 0
  | .conv _ :: ps => convCount ps + 1
  | _ :: ps => convCount ps

/-! ## `printf` -/

/-- Lower-case hexadecimal digits. -/
def hexStr (n : Nat) : List Byte := (Nat.toDigits 16 n).map fun c => BitVec.ofNat 8 c.toNat

/-! ## `scanf` -/

/-- A value `scanf` assigns: an integer stored in `w` bytes, or bytes. -/
inductive SVal where
  | int (x : Int) (w : Nat)
  | bytes (bs : List Byte)

/-- The bytes an assigned value stores. -/
def SVal.store : SVal → List Byte
  | .int x w => (List.range w).map fun i => BitVec.ofInt 8 (x / 2 ^ (8 * i))
  | .bytes bs => bs

/-- The outcome of one conversion. -/
inductive CRes where
  | none
  | ub
  | some (v : SVal) (rest : List Byte)

/-- The outcome of a format. -/
inductive ScanOut where
  | ok (vs : List SVal) (rest : List Byte)
  | fail (vs : List SVal) (rest : List Byte)
  | ub

/-- A hexadecimal digit's value. -/
def hexVal (c : Byte) : Option Nat :=
  if isDigit c then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

/-- The `%x` conversion: white space, an optional `0x`/`0X`, hexadecimal digits. -/
def scanHex (inp : List Byte) : Option (Nat × List Byte) :=
  let r := inp.dropWhile isSpace
  let r := match r with
    | z :: x :: r' => if z = ch '0' ∧ (x = ch 'x' ∨ x = ch 'X') then r' else r
    | _ => r
  let ds := r.takeWhile fun c => (hexVal c).isSome
  if ds = [] then none
  else some (ds.foldl (fun v c => 16 * v + (hexVal c).getD 0) 0, r.dropWhile fun c => (hexVal c).isSome)

/-- An integer conversion's value, if in `[lo, hi)`, stored in `w` bytes. -/
def intIn (lo hi : Int) (w : Nat) : Option (Int × List Byte) → CRes
  | none => .none
  | some (x, r) => if lo ≤ x ∧ x < hi then .some (.int x w) r else .ub

/-- **One conversion.** -/
def convScan : Conv → List Byte → CRes
  | .d, inp => intIn (-2 ^ 31) (2 ^ 31) 4 (scanInt inp)
  | .ld, inp => intIn (-2 ^ 63) (2 ^ 63) 8 (scanInt inp)
  | .lld, inp => intIn (-2 ^ 63) (2 ^ 63) 8 (scanInt inp)
  | .u, inp => intIn 0 (2 ^ 32) 4 (scanInt inp)
  | .x, inp => intIn 0 (2 ^ 32) 4 ((scanHex inp).map fun p => ((p.1 : Int), p.2))
  | .s, inp =>
    let r := inp.dropWhile isSpace
    let w := r.takeWhile fun c => !isSpace c
    if w = [] then .none else .some (.bytes (w ++ [0#8])) (r.dropWhile fun c => !isSpace c)
  | .c, inp =>
    match inp with
    | b :: r => .some (.bytes [b]) r
    | [] => .none

/-- A value assigned before the rest. -/
def ScanOut.cons (v : SVal) : ScanOut → ScanOut
  | .ok vs r => .ok (v :: vs) r
  | .fail vs r => .fail (v :: vs) r
  | .ub => .ub

/-- **Reading a format** from the input. -/
def scanPieces : List Piece → List Byte → ScanOut
  | [], inp => .ok [] inp
  | .ws _ :: ps, inp => scanPieces ps (inp.dropWhile isSpace)
  | .lit b :: ps, inp =>
    match inp with
    | c :: r => if c = b then scanPieces ps r else .fail [] inp
    | [] => .fail [] []
  | .conv k :: ps, inp =>
    match convScan k inp with
    | .none => .fail [] inp
    | .ub => .ub
    | .some v r => (scanPieces ps r).cons v

/-- What `scanPieces` would assign from the input `inp`. -/
def assigned : ScanOut → List SVal
  | .ok vs _ => vs
  | .fail vs _ => vs
  | .ub => []

end Silmaril.Libc.Formats
