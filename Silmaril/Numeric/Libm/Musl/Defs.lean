module

public import Silmaril.Numeric.Libm.Binary64.Defs

/-!
# A fixed implementation: musl's `sin` and `cos`

A transcription of musl's `sin` and `cos` (`src/math/sin.c`, `cos.c`, `__sin.c`,
`__cos.c`, `__rem_pio2.c`, at musl commit
`7813e9119eb5fe681b6750b8a033a0490bca0941`; the algorithms are fdlibm's). Every
floating-point operation is the IEEE round-to-nearest-even operation of the
`F64` model, in C's evaluation order, with `FLT_EVAL_METHOD == 0` and no FMA
contraction (musl compiles with `-std=c99`, which turns contraction off in GCC).
wasi-libc's `sin` and `cos` are musl's.

The argument reduction is transcribed for `|x| < 2^20 · π/2` (the small and
"medium" Cody–Waite paths). Larger finite arguments use `__rem_pio2_large`
(Payne–Hanek), which is not transcribed: there the references return `none`.
Non-finite arguments also give `none`: musl returns `x - x`, a NaN whose
encoding is the hardware's (x86's default NaN is negative; Wasm's is
nondeterministic), and the special-case nodes already fix these results.
`BitExactWhere` (`Lattice.Defs`) states agreement on the inputs where a
reference is defined.

musl is MIT-licensed; the constants below are fdlibm's (Sun Microsystems,
"Permission to use, copy, modify, and distribute this software is freely
granted, provided that this notice is preserved").
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Musl

open Silmaril.Numeric.Ieee754

/-- A binary64 constant from its encoding. -/
abbrev k (bits : UInt64) : F64 := F64.ofBits bits

/-- The high word of `x` without the sign bit (`GET_HIGH_WORD(ix, x); ix &= 0x7fffffff`). -/
def highWord (x : F64) : UInt64 := (x.bits >>> 32) &&& 0x7fffffff

/-- The biased exponent field (`u.i >> 52 & 0x7ff`). -/
def expField (x : F64) : Int := (((x.bits >>> 52) &&& 0x7ff).toNat : Int)

/-! ## `__sin` and `__cos` -/

def S1 := k 0xBFC5555555555549
def S2 := k 0x3F8111111110F8A6
def S3 := k 0xBF2A01A019C161D5
def S4 := k 0x3EC71DE357B1FE7D
def S5 := k 0xBE5AE5E68A2B9CEB
def S6 := k 0x3DE5D93A5ACFD57C

def C1 := k 0x3FA555555555554C
def C2 := k 0xBF56C16C16C15177
def C3 := k 0x3EFA01A019CB1590
def C4 := k 0xBE927E4F809C52AD
def C5 := k 0x3E21EE9EBDB4B1C4
def C6 := k 0xBDA8FAE9BE8838D4

def half := k 0x3FE0000000000000
def oneD := k 0x3FF0000000000000

/-- `__sin(x, y, iy)`: the sine kernel on `[-π/4, π/4]`, `y` the tail of `x`. -/
def kernelSin (x y : F64) (iy : Bool) : F64 :=
  let z := x * x
  let w := z * z
  let r := S2 + z * (S3 + z * S4) + z * w * (S5 + z * S6)
  let v := z * x
  if !iy then x + v * (S1 + z * r)
  else x - ((z * (half * y - v * r) - y) - v * S1)

/-- `__cos(x, y)`: the cosine kernel on `[-π/4, π/4]`. -/
def kernelCos (x y : F64) : F64 :=
  let z := x * x
  let w := z * z
  let r := z * (C1 + z * (C2 + z * C3)) + w * w * (C4 + z * (C5 + z * C6))
  let hz := half * z
  let w := oneD - hz
  w + (((oneD - w) - hz) + (z * r - x * y))

/-! ## `__rem_pio2` for `|x| < 2^20 · π/2` -/

def toint := k 0x4338000000000000
def pio4 := k 0x3FE921FB54442D18
def invpio2 := k 0x3FE45F306DC9C883
def pio2_1 := k 0x3FF921FB54400000
def pio2_1t := k 0x3DD0B4611A626331
def pio2_2 := k 0x3DD0B4611A600000
def pio2_2t := k 0x3BA3198A2E037073
def pio2_3 := k 0x3BA3198A2E000000
def pio2_3t := k 0x397B839A252049C1

/-- The fixed reductions by `j · π/2`, `j ∈ {1, 2, 3, 4}`, for `|x| ≲ 9π/4`.
`j * pio2_1` is C's constant product, rounded once like any product. -/
def small (x : F64) (j : Nat) : Int × F64 × F64 :=
  let c := if j = 1 then pio2_1 else F64.ofInt j * pio2_1
  let ct := if j = 1 then pio2_1t else F64.ofInt j * pio2_1t
  if !x.signBit then
    let z := x - c
    let y0 := z - ct
    (j, y0, (z - y0) - ct)
  else
    let z := x + c
    let y0 := z + ct
    (-(j : Int), y0, (z - y0) + ct)

/-- The "medium" Cody–Waite reduction with up to three rounds. -/
def medium (x : F64) : Option (Int × F64 × F64) := do
  let ix := highWord x
  let fn := x * invpio2 + toint - toint
  let n ← fn.toInt?
  let r := x - fn * pio2_1
  let w := fn * pio2_1t
  let (n, fn, r, w) :=
    if F64.lessThan (r - w) (-pio4) then
      let fn := fn - oneD
      (n - 1, fn, x - fn * pio2_1, fn * pio2_1t)
    else if F64.lessThan pio4 (r - w) then
      let fn := fn + oneD
      (n + 1, fn, x - fn * pio2_1, fn * pio2_1t)
    else (n, fn, r, w)
  let ex : Int := ((ix >>> 20).toNat : Int)
  let y0 := r - w
  let (r, w, y0) :=
    if ex - expField y0 > 16 then
      let t := r
      let w := fn * pio2_2
      let r := t - w
      let w := fn * pio2_2t - ((t - r) - w)
      let y0 := r - w
      if ex - expField y0 > 49 then
        let t := r
        let w := fn * pio2_3
        let r := t - w
        let w := fn * pio2_3t - ((t - r) - w)
        (r, w, r - w)
      else (r, w, y0)
    else (r, w, y0)
  return (n, y0, (r - y0) - w)

/-- `__rem_pio2(x)` for finite `|x| < 2^20 · π/2`: `(n, y₀, y₁)` with
`x ≈ n · π/2 + y₀ + y₁`. `none` on larger or non-finite arguments. -/
def remPio2 (x : F64) : Option (Int × F64 × F64) :=
  let ix := highWord x
  if ix ≤ 0x400f6a7a then
    if ix &&& 0xfffff = 0x921fb then medium x
    else if ix ≤ 0x4002d97c then some (small x 1) else some (small x 2)
  else if ix ≤ 0x401c463b then
    if ix ≤ 0x4015fdbc then
      if ix = 0x4012d97c then medium x else some (small x 3)
    else if ix = 0x401921fb then medium x else some (small x 4)
  else if ix < 0x413921fb then medium x
  else none

/-! ## `sin` and `cos` -/

/-- musl's `sin`, where transcribed (`none` for finite `|x| ≥ 2^20 · π/2`). -/
def sin (x : F64) : Option F64 :=
  let ix := highWord x
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e500000 then some x else some (kernelSin x F64.zero false)
  else if ix ≥ 0x7ff00000 then none
  else (remPio2 x).map fun (n, y0, y1) =>
    match n % 4 with
    | 0 => kernelSin y0 y1 true
    | 1 => kernelCos y0 y1
    | 2 => F64.neg (kernelSin y0 y1 true)
    | _ => F64.neg (kernelCos y0 y1)

/-- musl's `cos`, where transcribed. -/
def cos (x : F64) : Option F64 :=
  let ix := highWord x
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e46a09e then some oneD else some (kernelCos x F64.zero)
  else if ix ≥ 0x7ff00000 then none
  else (remPio2 x).map fun (n, y0, y1) =>
    match n % 4 with
    | 0 => kernelCos y0 y1
    | 1 => F64.neg (kernelSin y0 y1 true)
    | 2 => F64.neg (kernelCos y0 y1)
    | _ => kernelSin y0 y1 true

end Silmaril.Numeric.Libm.Musl
