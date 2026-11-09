module

public import Silmaril.X86.Machine

/-!
# Accumulator-fold stencil with deferred reduction

The two running sums of a Fletcher/Adler checksum: `s1 ← s1 + b`, `s2 ← s2 + s1`, both
modulo `M`. Optimised code (zlib `adler32_z`, its `NMAX` blocking and `DO16` unrolling) adds
**without** reducing for up to `N` bytes and reduces once per chunk; the stencil states the
three forms and the bound that makes the deferral sound in a `w`-bit register.

* `modStep M`, `modFold M`: the reference, reducing after every byte;
* `rawStep`, `rawFold`: no reduction (unbounded naturals);
* `chunked M N`: `rawFold` over chunks of `N` bytes, reducing after each chunk;
* `RawBound M N w`: `255 · N(N+1)/2 + (N+1)(M-1) < 2^w`, zlib's `NMAX` condition: a chunk of at
  most `N` bytes started from reduced sums never exceeds `w` bits.

Theorems (`Stencils/AccumFold/Thms.lean`): `rawFold_mod` (deferring is sound modulo `M`),
`chunked_eq_modFold` (any chunk size), `rawFold_lt` (the bound), `rawFold_append` (an unrolled
block of `k` raw steps is `k` steps).
-/

@[expose] public section

namespace Silmaril.X86.Stencils.AccumFold

open Silmaril.X86 (Byte)

/-- One reference step: both sums reduced. -/
def modStep (M : Nat) (s : Nat × Nat) (b : Byte) : Nat × Nat :=
  ((s.1 + b.toNat) % M, (s.2 + (s.1 + b.toNat) % M) % M)

def modFold (M : Nat) (s : Nat × Nat) (bs : List Byte) : Nat × Nat := bs.foldl (modStep M) s

/-- One raw step: no reduction. -/
def rawStep (s : Nat × Nat) (b : Byte) : Nat × Nat := (s.1 + b.toNat, s.2 + s.1 + b.toNat)

def rawFold (s : Nat × Nat) (bs : List Byte) : Nat × Nat := bs.foldl rawStep s

/-- Reduce both sums. -/
def red (M : Nat) (s : Nat × Nat) : Nat × Nat := (s.1 % M, s.2 % M)

/-- Raw folds over chunks of `N` bytes, reducing after each chunk. -/
def chunked (M N : Nat) (hN : 0 < N) (s : Nat × Nat) (bs : List Byte) : Nat × Nat :=
  if _h : bs.length ≤ N then red M (rawFold s bs)
  else chunked M N hN (red M (rawFold s (bs.take N))) (bs.drop N)
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

/-- zlib's `NMAX` condition for chunk size `N`, modulus `M` and register width `w`. -/
def RawBound (M N w : Nat) : Prop := 255 * (N * (N + 1) / 2) + (N + 1) * (M - 1) < 2 ^ w

end Silmaril.X86.Stencils.AccumFold
