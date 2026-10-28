module

public import Silmaril.Numeric.Ieee754.Std.Isa

/-!
# Checking Berkeley TestFloat vectors against the `Std` implementation

`testfloat_gen` (TestFloat 3e) writes one test case per line: operands, the
expected result and the expected exception flags, all in hexadecimal. The
flag byte is SoftFloat's: inexact 1, underflow 2, overflow 4, infinite
(division by zero) 8, invalid 16. Results of comparisons are `0` or `1`, and
integer results are two's complement.

`checkLine` evaluates one line with an `Isa` profile and reports whether the
encoding and the flags agree exactly. The vectors themselves are generated
outside the repository (`scripts/ieee754/testfloat-check.sh`); a sample is
checked at build time in `Std.Vectors`.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std.TestFloat

open Silmaril.Numeric.Ieee754

def hexDigit? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex? (s : String) : Option ℕ :=
  if s.isEmpty then none else
  s.foldl (fun acc c => do let a ← acc; let d ← hexDigit? c; pure (16 * a + d)) (some 0)

def flagsByte (fl : Flags) : ℕ :=
  (if fl.inexact then 1 else 0) + (if fl.underflow then 2 else 0) + (if fl.overflow then 4 else 0) +
    (if fl.divisionByZero then 8 else 0) + (if fl.invalidOperation then 16 else 0)

/-- TestFloat's format names. -/
def encoding? (reading : X87Reading) : String → Option Encoding
  | "f16" => some Interchange.binary16.encoding
  | "f32" => some Interchange.binary32.encoding
  | "f64" => some Interchange.binary64.encoding
  | "f128" => some Interchange.binary128.encoding
  | "extF80" => some (X87.encoding reading)
  | _ => none

def intFormat? : String → Option (IntFormat × ℕ)
  | "i32" => some (IntFormat.signed 32, 32)
  | "ui32" => some (IntFormat.unsigned 32, 32)
  | "i64" => some (IntFormat.signed 64, 64)
  | "ui64" => some (IntFormat.unsigned 64, 64)
  | _ => none

def mode? : String → Option RoundingMode
  | "-rnear_even" => some .nearestTiesToEven
  | "-rminMag" => some .towardZero
  | "-rmin" => some .towardNegative
  | "-rmax" => some .towardPositive
  | "-rnear_maxMag" => some .nearestTiesToAway
  | _ => none

def isa? : String → Option Isa
  | "x86SSE" => some .x86SSE
  | "sf8086SSE" => some .softfloat8086SSE
  | "riscv" => some .riscv
  | "x87" => some .x87
  | "x87hw" => some .x87
  | _ => none

/-- Two's complement of an integer of width `w`. -/
def twos (w : ℕ) (n : ℤ) : ℕ := (n % (2 ^ w : ℤ)).toNat

def ofTwos (w : ℕ) (n : ℕ) : ℤ := if n < 2 ^ (w - 1) then n else (n : ℤ) - 2 ^ w

/-- A test configuration: profile, function name, rounding, exactness and the
extF80 rounding precision (64, 53 or 24). -/
structure Config where
  isa : Isa
  fn : String
  mode : RoundingMode := .nearestTiesToEven
  exact : Bool := false
  precision : ℕ := 64
  reading : X87Reading := .softfloat

def withPrecision (c : Config) (E : Encoding) : Encoding :=
  if E.expBits = 15 then
    match c.precision with
    | 24 => { E with fmt := .x87PrecisionSingle }
    | 53 => { E with fmt := .x87PrecisionDouble }
    | _ => E
  else E

/-- Evaluate one vector line; `some true` when result and flags agree, `none`
when the line or function is not understood. -/
def checkLine (c : Config) (line : String) : Option Bool := do
  let words := (line.splitOn " ").filter (· ≠ "")
  let nums ← words.mapM parseHex?
  let parts := c.fn.splitOn "_"
  let I := c.isa
  let mode := c.mode
  let res (E : Encoding) (p : Fields × Flags) (z f : ℕ) : Bool :=
    p.1.toNat E == z && flagsByte p.2 == f
  match parts with
  | [src, "to", dst] =>
    match intFormat? src, encoding? c.reading dst with
    | some (t, w), some E => do
      let E := withPrecision c E
      let [a, z, f] := nums | none
      let n : ℤ := if t.lo < 0 then ofTwos w a else a
      pure (res E (I.ofInt E mode n) z f)
    | _, _ =>
      let E₁ ← encoding? c.reading src
      match intFormat? dst with
      | some (t, w) => do
        let [a, z, f] := nums | none
        let p := I.toInt E₁ t mode c.exact (Fields.ofNat E₁ a)
        pure (twos w p.1 == z && flagsByte p.2 == f)
      | none => do
        let E₂ ← encoding? c.reading dst
        let E₂ := withPrecision c E₂
        let [a, z, f] := nums | none
        pure (res E₂ (I.convert E₁ E₂ mode (Fields.ofNat E₁ a)) z f)
  | src :: rest => do
    let E ← encoding? c.reading src
    let E := withPrecision c E
    let x := Fields.ofNat E
    let op := "_".intercalate rest
    match op, nums with
    | "add", [a, b, z, f] => pure (res E (I.add E mode (x a) (x b)) z f)
    | "sub", [a, b, z, f] => pure (res E (I.sub E mode (x a) (x b)) z f)
    | "mul", [a, b, z, f] => pure (res E (I.mul E mode (x a) (x b)) z f)
    | "div", [a, b, z, f] => pure (res E (I.div E mode (x a) (x b)) z f)
    | "rem", [a, b, z, f] => pure (res E (I.rem E (x a) (x b)) z f)
    | "mulAdd", [a, b, d, z, f] => pure (res E (I.fma E mode (x a) (x b) (x d)) z f)
    | "x86min", [a, b, z, f] => pure (res E (minMax E (I.nan E) .x86 false (x a) (x b)) z f)
    | "x86max", [a, b, z, f] => pure (res E (minMax E (I.nan E) .x86 true (x a) (x b)) z f)
    | "sqrt", [a, z, f] => pure (res E (I.sqrt E mode (x a)) z f)
    | "roundToInt", [a, z, f] => pure (res E (I.roundToIntegral E mode c.exact (x a)) z f)
    | "eq", [a, b, z, f] => cmp E false (fun o => o == some .eq) (x a) (x b) z f
    | "le", [a, b, z, f] => cmp E true (fun o => o == some .lt || o == some .eq) (x a) (x b) z f
    | "lt", [a, b, z, f] => cmp E true (fun o => o == some .lt) (x a) (x b) z f
    | "eq_signaling", [a, b, z, f] => cmp E true (fun o => o == some .eq) (x a) (x b) z f
    | "le_quiet", [a, b, z, f] =>
        cmp E false (fun o => o == some .lt || o == some .eq) (x a) (x b) z f
    | "lt_quiet", [a, b, z, f] => cmp E false (fun o => o == some .lt) (x a) (x b) z f
    | _, _ => none
  | _ => none
where
  cmp (E : Encoding) (signaling : Bool) (pred : Option Ordering → Bool) (a b : Fields)
      (z f : ℕ) : Option Bool :=
    let p := Isa.compare E signaling a b
    some ((if pred p.1 then 1 else 0) == z && flagsByte p.2 == f)

/-- Check every line; returns (checked, failed lines). -/
def checkAll (c : Config) (text : String) : ℕ × List String :=
  (text.splitOn "\n").foldl (fun (acc : ℕ × List String) line =>
    if line.all Char.isWhitespace then acc else
    match checkLine c line with
    | some true => (acc.1 + 1, acc.2)
    | _ => (acc.1 + 1, line :: acc.2)) (0, [])

end Silmaril.Numeric.Ieee754.Std.TestFloat
