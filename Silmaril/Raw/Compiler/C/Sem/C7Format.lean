module

public import Silmaril.Compiler.C.Sem.C7State.Defs
/-!
# Exact decimal printf conversions

Binary64 is decoded as a ratio of natural numbers. Decimal scaling and round-to-nearest,
ties-to-even use integer division and its remainder, with no host floating arithmetic.
`%g` chooses its notation using the exponent after rounding to significant digits.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C7

open Silmaril.Compile.C
open C0 (Stop ub)
open C1 (Spec bytesOf wrap)
open C4 (Arg)

/-- Round a nonnegative ratio to an integer, ties to even. -/
def roundEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q

/-- Multiply a ratio by a decimal power, then round once. -/
def roundScaled (num den : Nat) (scale : Int) : Nat :=
  if scale ≥ 0 then roundEven (num * 10 ^ scale.toNat) den
  else roundEven num (den * 10 ^ scale.natAbs)

/-- Exact magnitude of a finite binary64 encoding. -/
def binaryRatio (bits : Nat) : Nat × Nat :=
  let ef : Nat := bits / 2^52 % 2048
  let frac := bits % 2^52
  let m := if ef == 0 then frac else 2^52 + frac
  let e : Int := if ef == 0 then -1074 else (ef : Int) - 1075
  if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ e.natAbs)

/-- The base-10 exponent before decimal rounding (zero uses exponent zero). -/
def decimalExponent (num den : Nat) : Int :=
  if num == 0 then 0 else
    let guess : Int := ((toString num).length : Int) - (toString den).length
    let below := if guess ≥ 0 then num < den * 10 ^ guess.toNat
      else num * 10 ^ guess.natAbs < den
    if below then guess - 1 else guess

/-- Fixed digits with a decimal point `p` places from the right. -/
def fixedDigits (q p : Nat) (alt : Bool) : String :=
  let ds := toString q
  let ds := String.ofList (List.replicate (p + 1 - ds.length) '0') ++ ds
  if p == 0 then ds ++ (if alt then "." else "")
  else String.ofList (ds.toList.take (ds.length - p)) ++ "." ++
    String.ofList (ds.toList.drop (ds.length - p))

/-- Strip only fraction zeros, never integer or exponent digits. -/
def trimFraction (s : String) : String :=
  if !s.contains '.' then s else
    let cs := s.toList.reverse.dropWhile (· == '0')
    String.ofList ((if cs.head? == some '.' then cs.tail else cs).reverse)

def exponentDigits (e : Int) (upper : Bool) : String :=
  let ds := toString e.natAbs
  (if upper then "E" else "e") ++ (if e < 0 then "-" else "+") ++
    String.ofList (List.replicate (2 - ds.length) '0') ++ ds

/-- Rounded scientific significand with `p` fraction digits, and its adjusted exponent. -/
def scientific (num den p : Nat) : Nat × Int :=
  let e := decimalExponent num den
  let q := roundScaled num den ((p : Int) - e)
  if q ≥ 10 ^ (p + 1) then (q / 10, e + 1) else (q, e)

/-- A floating conversion, including sign, special values, flags and padding. -/
def formatFloat (sp : Spec) (c : Char) (bits : Nat) : Except Stop (List UInt8) := do
  let p := sp.prec.getD 6
  if p > 100000 || sp.width > 100000 then throw (.unsupported "a printf resource bound")
  let sign := if bits / 2^63 % 2 == 1 then "-" else if sp.plus then "+"
    else if sp.space then " " else ""
  let upper := c == 'F' || c == 'E' || c == 'G'
  if bits / 2^52 % 2048 == 2047 then
    let body := if bits % 2^52 == 0 then (if upper then "INF" else "inf")
      else if upper then "NAN" else "nan"
    return sp.pad (bytesOf sign) (bytesOf body) false
  let (num, den) := binaryRatio bits
  let body := if c == 'f' || c == 'F' then fixedDigits (roundScaled num den p) p sp.alt
    else if c == 'e' || c == 'E' then
      let (q, e) := scientific num den p
      fixedDigits q p sp.alt ++ exponentDigits e upper
    else
      let p := max 1 p
      let (q, e) := scientific num den (p - 1)
      if e ≥ -4 && e < (p : Int) then
        let places := ((p : Int) - 1 - e).toNat
        let s := fixedDigits (roundScaled num den places) places sp.alt
        if sp.alt then s else trimFraction s
      else
        let s := fixedDigits q (p - 1) sp.alt
        (if sp.alt then s else trimFraction s) ++ exponentDigits e upper
  return sp.pad (bytesOf sign) (bytesOf body) true

/-- Consume an argument with a scalar value. -/
def nextScalar : List Arg → Except Stop (Arg × Int × List Arg)
  | a :: rest => match a.val with
    | .scalar v => .ok (a, v, rest)
    | .agg _ => ub "an aggregate printf argument"
  | [] => ub "printf with too few arguments"

/-- Consume an integer argument (also used for star width and precision). -/
def nextInteger (args : List Arg) : Except Stop (Int × List Arg) := do
  let (a, v, rest) ← nextScalar args
  if a.ty.isFloat then ub "a floating argument for an integer printf conversion"
  return (v, rest)

/-- Check each byte of a string against heap lifetimes and bounds, stopping at precision. -/
def formatString (env : Env) (ptr : Int) (prec : Option Nat) : Except Stop (Array UInt8) := do
  if ptr < 0 then ub "a negative string address"
  let mut out := #[]
  let a := ptr.toNat
  for i in [0:prec.getD (env.mem.sp + 1)] do
    env.access (a + i) 1
    let b := (← env.mem.readBytes (a + i) 1)[0]!
    if b == 0 then return out
    out := out.push b
  if prec.isNone then throw (.unsupported "an unterminated string")
  return out

/-- Typed printf formatting. The integer conversions reuse C1's specification and padding. -/
def formatTyped (env : Env) (fmt : List UInt8) (args : List Arg) : Except Stop (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  let mut fmt := fmt
  let mut args := args
  for _ in [0:fmt.length + 1] do
    match fmt with
    | [] => return out
    | c :: rest =>
      if c != 37 then out := out.push c; fmt := rest; continue
      let mut sp : Spec := {}
      let mut r := rest
      for _ in [0:r.length] do
        match r with
        | 45 :: r' => sp := { sp with minus := true }; r := r'
        | 43 :: r' => sp := { sp with plus := true }; r := r'
        | 32 :: r' => sp := { sp with space := true }; r := r'
        | 35 :: r' => sp := { sp with alt := true }; r := r'
        | 48 :: r' => sp := { sp with zero := true }; r := r'
        | _ => break
      if r.head? == some 42 then
        let (w, restArgs) ← nextInteger args
        args := restArgs; r := r.tail
        let w := wrap 4 true w
        sp := { sp with minus := sp.minus || w < 0, width := w.natAbs }
      else
        let ds := r.takeWhile fun b => 48 ≤ b && b ≤ 57
        sp := { sp with width := ds.foldl (fun a d => a * 10 + (d.toNat - 48)) 0 }
        r := r.drop ds.length
      if r.head? == some 46 then
        r := r.tail
        if r.head? == some 42 then
          let (p, restArgs) ← nextInteger args
          args := restArgs; r := r.tail
          let p := wrap 4 true p
          sp := { sp with prec := if p < 0 then none else some p.toNat }
        else
          let ds := r.takeWhile fun b => 48 ≤ b && b ≤ 57
          sp := { sp with prec := some (ds.foldl (fun a d => a * 10 + (d.toNat - 48)) 0) }
          r := r.drop ds.length
      let beforeLength := r
      match r with
      | 104 :: 104 :: r' => sp := { sp with len := 1 }; r := r'
      | 104 :: r' => sp := { sp with len := 2 }; r := r'
      | 108 :: 108 :: r' | 108 :: r' | 122 :: r' | 106 :: r' | 116 :: r' | 113 :: r' =>
        sp := { sp with len := 8 }; r := r'
      | _ => pure ()
      let modifier := beforeLength.take (beforeLength.length - r.length)
      if sp.width > 100000 || sp.prec.getD 0 > 100000 then
        throw (.unsupported "a printf resource bound")
      match r with
      | [] => throw (.unsupported "an incomplete printf conversion")
      | k :: r' =>
        fmt := r'
        let k := Char.ofNat k.toNat
        match k with
        | '%' => out := out.push 37
        | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' =>
          if modifier != [] && modifier != [108] then
            throw (.unsupported "a floating printf length modifier")
          let (a, v, restArgs) ← nextScalar args
          args := restArgs
          if !(match a.ty with | .float 8 => true | _ => false) then
            ub "a non-double floating printf argument"
          out := out ++ (← formatFloat sp k v.toNat).toArray
        | 'd' | 'i' | 'u' | 'o' | 'x' | 'X' =>
          let (v, restArgs) ← nextInteger args
          args := restArgs
          out := out ++ (sp.int k v).toArray
        | 'c' =>
          if modifier != [] then throw (.unsupported "a wide printf character")
          let (v, restArgs) ← nextInteger args
          args := restArgs
          out := out ++ (sp.pad [] [(wrap 1 false v).toNat.toUInt8] false).toArray
        | 's' =>
          if modifier != [] then throw (.unsupported "printf of a wide string")
          let (v, restArgs) ← nextInteger args
          args := restArgs
          out := out ++ (sp.pad [] (← formatString env v sp.prec).toList false).toArray
        | k => throw (.unsupported s!"the printf conversion %{k}")
  return out

end Silmaril.Compile.C.Sem.C7
