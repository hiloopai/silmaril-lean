module

/-!
# Printing floating-point literals as `wasmprinter` does

`wasmprinter` (wasm-tools 1.262.0, `crates/wasmprinter/src/lib.rs`, `print_float!`) prints an
`f32`/`f64` constant as a hexadecimal float (`0x1.8p+0`), `inf`, `nan` or `nan:0x…`, followed
by a comment `(;=…;)` holding Rust's `Display` of the value: the shortest decimal that rounds
back to the same float, written without an exponent (`1.5`, `1000000`, `0.0001`).

`hexBody` is a transcription of `print_float!` on natural numbers. `shortest` finds, for
`p = 1, 2, …`, the decimal with `p` significant digits nearest to the value and returns the
first one inside the value's rounding interval (round-to-nearest-even: closed when the
significand is even); that is the shortest round-tripping decimal and, among those, the
nearest. All arithmetic is exact (`Nat`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Print.Float

/-- Hexadecimal digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- `n` in lower-case hexadecimal, without prefix. -/
def hex (n : Nat) : String :=
  if n < 16 then String.singleton (hexDigit n)
  else hex (n / 16) ++ String.singleton (hexDigit (n % 16))
termination_by n
decreasing_by omega

/-- Number of decimal digits of `n` (1 for 0). -/
def digits (n : Nat) : Nat := (toString n).length

/-- Leading zeros of `x` as a `w`-bit number. -/
def leadingZeros (w x : Nat) : Nat := w - Nat.log2 x - (if x = 0 then 0 else 1)

/-- The value `m · 2^e` of a finite float of format (`mw` significand bits, `ew` exponent
bits) with unsigned bits `bits` (sign removed): `(m, e)`. -/
def decompose (mw ew bits : Nat) : Nat × Int :=
  let frac := bits % 2 ^ mw
  let ex := bits / 2 ^ mw
  let bias : Int := 2 ^ (ew - 1) - 1
  if ex = 0 then (frac, 1 - bias - mw) else (frac + 2 ^ mw, (ex : Int) - bias - mw)

/-- Compare `d · 10^k` with `x · 2^s`. -/
def cmpScaled (d : Nat) (k : Int) (x : Nat) (s : Int) : Ordering :=
  let lhs := d * (if k ≥ 0 then 10 ^ k.toNat else 1) * (if s < 0 then 2 ^ (-s).toNat else 1)
  let rhs := x * (if s ≥ 0 then 2 ^ s.toNat else 1) * (if k < 0 then 10 ^ (-k).toNat else 1)
  compare lhs rhs

/-- `⌊log10 (num / den)⌋` for `num, den > 0`. -/
def floorLog10 (num den : Nat) : Int :=
  if num ≥ den then (digits (num / den) : Int) - 1
  else
    -- smallest j ≥ 1 with num · 10^j ≥ den
    let bound := digits den + 1
    let j := (((List.range bound).map (· + 1)).find? (fun j => num * 10 ^ j ≥ den)).getD bound
    Int.neg (j : Int)

/-- The nearest `p`-significant-digit decimal to `num / den` (`> 0`): `(d, k)` with value
`d · 10^k`, rounding half up. -/
def roundTo (num den p : Nat) : Nat × Int :=
  let l := floorLog10 num den
  let k : Int := l - (p : Int) + 1
  -- d = round(num / (den · 10^k))
  let (n, dd) := if k ≥ 0 then (num, den * 10 ^ k.toNat) else (num * 10 ^ (-k).toNat, den)
  let d := (2 * n + dd) / (2 * dd)
  if d ≥ 10 ^ p then (d / 10, k + 1) else (d, k)

/-- The shortest decimal `(d, k)` (`d · 10^k`) that lies in the rounding interval of the
positive finite float `m · 2^e` of a format with `mw` significand bits; `boundary` says the
significand field is zero above the minimal exponent (the lower neighbour is closer). -/
def shortest (m : Nat) (e : Int) (mw : Nat) (boundary : Bool) : Nat × Int :=
  -- in units of 2^(e-2): v = 4m, the interval is [4m - lo, 4m + 2]
  let lo := if boundary then 1 else 2
  let even := m % 2 == 0
  let (num, den) := if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  let inside (d : Nat) (k : Int) : Bool :=
    let a := cmpScaled d k (4 * m - lo) (e - 2)
    let b := cmpScaled d k (4 * m + 2) (e - 2)
    (a == .gt || (even && a == .eq)) && (b == .lt || (even && b == .eq))
  let cands := (List.range (mw / 3 + 3)).map (· + 1)
  match cands.findSome? (fun p => let (d, k) := roundTo num den p
      if inside d k then some (d, k) else none) with
  | some r => r
  | none => roundTo num den (mw / 3 + 3)

/-- Strip trailing zeros of `d · 10^k`. -/
def normalize (d : Nat) (k : Int) : Nat × Int :=
  if d ≠ 0 ∧ d % 10 = 0 then normalize (d / 10) (k + 1) else (d, k)
termination_by d
decreasing_by omega

/-- `d · 10^k` written without an exponent, as Rust's `Display` does. -/
def decimalString (d : Nat) (k : Int) : String :=
  let (d, k) := normalize d k
  let s := toString d
  if k ≥ 0 then s ++ String.ofList (List.replicate k.toNat '0')
  else
    let pos : Int := (s.length : Int) + k
    if pos > 0 then
      String.ofList (s.toList.take pos.toNat) ++ "." ++ String.ofList (s.toList.drop pos.toNat)
    else "0." ++ String.ofList (List.replicate (-pos).toNat '0') ++ s

/-- Rust's `Display` of the float with bits `bits` (`mw` significand, `ew` exponent bits). -/
def display (mw ew bits : Nat) : String :=
  let w := mw + ew + 1
  let neg := bits / 2 ^ (w - 1) % 2 == 1
  let u := bits % 2 ^ (w - 1)
  let ex := u / 2 ^ mw
  let frac := u % 2 ^ mw
  let sign := if neg then "-" else ""
  if ex = 2 ^ ew - 1 then
    if frac = 0 then sign ++ "inf" else "NaN"
  else if u = 0 then sign ++ "0"
  else
    let (m, e) := decompose mw ew u
    let boundary := frac = 0 && ex > 1
    let (d, k) := shortest m e mw boundary
    sign ++ decimalString d k

/-- `print_float!` of wasmprinter: the literal and its comment, for bits `bits` of a float
with `mw` significand and `ew` exponent bits. -/
def literal (mw ew bits : Nat) : String :=
  let w := mw + ew + 1
  let neg := bits / 2 ^ (w - 1) % 2 == 1
  let u := bits % 2 ^ (w - 1)
  let sign := if neg then "-" else ""
  let ex := u / 2 ^ mw
  let frac := u % 2 ^ mw
  let shown := display mw ew bits
  if ex = 2 ^ ew - 1 then
    if frac = 0 then sign ++ "inf (;=" ++ shown ++ ";)"
    else if frac = 2 ^ (mw - 1) then sign ++ "nan (;=" ++ shown ++ ";)"
    else sign ++ "nan:0x" ++ hex frac ++ " (;=" ++ shown ++ ";)"
  else
    let bias : Int := 2 ^ (ew - 1) - 1
    let minExp : Int := -(2 ^ (ew - 1) : Int) + 1
    let exponent : Int := (ex : Int) - bias
    let body :=
      if u = 0 then "0x0p+0"
      else
        -- fraction as a w-bit number, left-aligned
        let fr0 := frac * 2 ^ (w - mw)
        let (fr, exponent) :=
          if frac > 0 ∧ exponent = minExp then
            let lead := leadingZeros w fr0
            let fr := if lead < w - 1 then (fr0 * 2 ^ (lead + 1)) % 2 ^ w else 0
            (fr, exponent - lead)
          else (fr0, exponent)
        let digitsStr := hexFrac w fr (w / 4 + 1)
        let expStr := if exponent ≥ 0 then "+" ++ toString exponent else toString exponent
        "0x1" ++ (if frac > 0 then "." ++ digitsStr else "") ++ "p" ++ expStr
    sign ++ body ++ " (;=" ++ shown ++ ";)"
where
  /-- The hexadecimal digits of the left-aligned `w`-bit fraction, until it is zero. -/
  hexFrac (w fr : Nat) : Nat → String
    | 0 => ""
    | fuel + 1 =>
      if fr = 0 then ""
      else String.singleton (hexDigit (fr / 2 ^ (w - 4))) ++ hexFrac w ((fr * 16) % 2 ^ w) fuel

def f32 (bits : Nat) : String := literal 23 8 bits
def f64 (bits : Nat) : String := literal 52 11 bits

end Silmaril.Wasm.Tools.Print.Float
