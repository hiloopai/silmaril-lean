module

public import Silmaril.Formats.Compression.Checksum.Adler32

@[expose] public section

namespace Silmaril.Formats.Compression

/-!
# Symbolic Adler-32 specification

For bytes `x₀, …, xₙ₋₁`, let `S = ∑ xᵢ` and `W = ∑ (n - i) * xᵢ`.
Starting from canonical accumulators `(a, b)`, the final accumulators are
`((a + S) mod 65521, (b + n * a + W) mod 65521)`.
The usual checksum starts from `(1, 0)` and packs the second component above
the first. This specification contains no machine widths, unrolled loops,
block sizes or delayed modular reductions.

`adlerWeightedSum` writes the weighted sum as a structural polynomial, so its
head has coefficient equal to the input length. The seed bounds in the
refinement theorem matter: the existing fold leaves an empty input's seed
unchanged, whereas this symbolic specification normalizes it modulo 65521.

These theorems relate two Lean definitions. They do not establish correctness
of an upstream C implementation or of its pointer and buffer interface.
-/

/-- The polynomial `∑ (n - i) * xᵢ`, with zero-based indices `i < n`. -/
def adlerWeightedSum : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.length + 1) * x + adlerWeightedSum xs

/-- Symbolic final state, with an arbitrary initial accumulator pair. -/
def adler32StateSpec (a b : Nat) (data : List Nat) : Nat × Nat :=
  ((a + data.sum) % adlerMod,
   (b + data.length * a + adlerWeightedSum data) % adlerMod)

/-- Adler-32's closed form, with the standard initial state `(1, 0)`. -/
def adler32Symbolic (data : List Nat) : Nat :=
  ((data.length + adlerWeightedSum data) % adlerMod) * 65536 +
    (1 + data.sum) % adlerMod

/-! ### Combining independently computed checksums -/

/-- Combine the accumulator pairs of two standard-seed checksums. Adding
`65520 = adlerMod - 1` represents subtraction of one modulo the modulus,
including when the left first accumulator is zero. -/
def adler32CombineState (left right : Nat × Nat) (rightLen : Nat) : Nat × Nat :=
  ((left.1 + right.1 + 65520) % adlerMod,
   (left.2 + right.2 + rightLen * (left.1 + 65520)) % adlerMod)

end Silmaril.Formats.Compression
