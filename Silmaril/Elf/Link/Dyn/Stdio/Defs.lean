module

public import Silmaril.X86.RelIsa.Defs

/-! # What `scanf("%d %d", …)` reads and `printf("%d\n", …)` writes

The byte-level specifications behind the stdio contracts of `Proc` (ISO C 7.21.6.2 and
7.21.6.1, as glibc 2.39 implements them for these two formats):

* `scanInt`: the `%d` conversion: skip white space (`isspace` in the C locale: space and
  `\t\n\v\f\r`), an optional sign, then the longest nonempty run of decimal digits; `none` is
  a matching failure (including end of input);
* `scanDD`: `"%d %d"`: two conversions (the ` ` directive skips white space, as `%d` itself
  does); `ok a b rest` when both convert, with the input after them; `fail` when a
  conversion fails (`scanf` then returns `0`, `1` or `EOF`, never `2`); `ub` when a converted
  value is outside `int` (undefined behaviour in ISO C, 7.21.6.2p10);
* `decStr x`: the decimal digits of `x` with a leading `-` for negatives (`%d`).
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Stdio

open Silmaril.X86 (Byte)

/-- C-locale white space. -/
def isSpace (c : Byte) : Bool := c.toNat == 32 || (9 ≤ c.toNat && c.toNat ≤ 13)

/-- A decimal digit. -/
def isDigit (c : Byte) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The value of a run of decimal digits. -/
def digitsVal (ds : List Byte) : Nat := ds.foldl (fun v c => 10 * v + (c.toNat - 48)) 0

/-- The `%d` conversion. -/
def scanInt (inp : List Byte) : Option (Int × List Byte) :=
  let r := inp.dropWhile isSpace
  let (neg, r) := match r with
    | c :: r' => if c.toNat = 45 then (true, r') else if c.toNat = 43 then (false, r') else (false, r)
    | [] => (false, [])
  let ds := r.takeWhile isDigit
  if ds = [] then none
  else some (if neg then -(digitsVal ds : Int) else (digitsVal ds : Int), r.dropWhile isDigit)

/-- A value of C's `int`. -/
def inInt32 (x : Int) : Bool := decide (-2 ^ 31 ≤ x) && decide (x < 2 ^ 31)

/-- The outcome of `scanf("%d %d", …)`. -/
inductive ScanRes : Type where
  | ok (a b : Int) (rest : List Byte)
  | fail
  | ub

/-- **`"%d %d"`.** -/
def scanDD (inp : List Byte) : ScanRes :=
  match scanInt inp with
  | none => .fail
  | some (a, r1) =>
    if inInt32 a then
      match scanInt r1 with
      | none => .fail
      | some (b, r2) => if inInt32 b then .ok a b r2 else .ub
    else .ub

/-- **`%d`**: the decimal representation. -/
def decStr (x : Int) : List Byte := (toString x).toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The four little-endian bytes of an `int`. -/
def le32 (x : Int) : List Byte :=
  let w := BitVec.ofInt 32 x
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- `"%d %d"` -/
def fmtDD : List Byte := [0x25, 0x64, 0x20, 0x25, 0x64]

/-- `"%d\n"` -/
def fmtDN : List Byte := [0x25, 0x64, 0x0a]

end Silmaril.Elf.Link.Dyn.Stdio
