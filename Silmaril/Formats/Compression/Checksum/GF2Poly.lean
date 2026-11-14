module

import Silmaril.Proofs.Formats.Compression.Checksum.GF2PolyBits

/-!
# Polynomials over GF(2)

A polynomial over GF(2) is represented by the natural number whose bit `i` is
its coefficient of `xⁱ`; `0` is the zero polynomial. In this representation

* addition (= subtraction) is `^^^` (`add`),
* multiplication by `xᵏ` is `<<< k` (`mulXPow`),
* `deg a` is `Nat.log2 a` for `a ≠ 0`, so `deg a < n ↔ a < 2 ^ n`,
* `mul` is carry-less multiplication and `mod` is schoolbook long division:
  while `deg a ≥ deg g`, subtract `x^(deg a - deg g) · g` from `a`.

`ofBits` reads a bit string as a polynomial whose *first* bit is the
highest-order coefficient, the convention of transmitted CRC messages, and
`reflect n r` is the `n`-bit reversal of `r`.

The algebra (`mod` is the unique remainder of degree below `deg g`, and it is
additive and compatible with multiplication by `x`) is in
`Silmaril.Formats.Compression.Checksum.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.GF2Poly

/-- Addition (and subtraction) of polynomials over GF(2). -/
abbrev add (a b : Nat) : Nat := a ^^^ b

/-- Multiplication by `xᵏ`. -/
abbrev mulXPow (k a : Nat) : Nat := a <<< k

/-- The degree of a nonzero polynomial. -/
abbrev deg (a : Nat) : Nat := a.log2

/-- `x^(n-1) + … + x + 1`, the polynomial with `n` unit coefficients. -/
abbrev ones (n : Nat) : Nat := 2 ^ n - 1

/-- Product of polynomials: `a · b = (a · ⌊b / x⌋) · x + b₀ · a`. -/
def mul (a b : Nat) : Nat :=
  if _h : b = 0 then 0
  else (mul a (b / 2) <<< 1) ^^^ (if b.testBit 0 then a else 0)
termination_by b
decreasing_by omega

/-- Remainder of `a` divided by `g` (long division). Dividing by the zero
polynomial leaves `a` unchanged. -/
def mod (a g : Nat) : Nat :=
  if _h : a ≠ 0 ∧ g ≠ 0 ∧ deg g ≤ deg a then mod (add a (mulXPow (deg a - deg g) g)) g
  else a
termination_by a
decreasing_by exact Proofs.Formats.Compression.GF2Poly.xor_shiftLeft_log2_lt _h.1 _h.2.1 _h.2.2

/-- A bit string as a polynomial, first bit the highest-order coefficient:
`ofBits [b₀, …, bₙ₋₁] = b₀ xⁿ⁻¹ + … + bₙ₋₁`. -/
def ofBits (bs : List Bool) : Nat := bs.foldl (fun acc b => add (mulXPow 1 acc) b.toNat) 0

/-- The `n`-bit reversal of `r`: coefficient `i` of `r` becomes coefficient
`n - 1 - i`; coefficients at `n` and above are dropped. -/
def reflect (n r : Nat) : Nat := ofBits ((List.range n).map r.testBit)

end Silmaril.Formats.Compression.GF2Poly
