module

public import Init.Data.List.Basic
import Init.Omega

/-! # Base-256 digits: the leaves of kernel bytes

`unpack k v` is the `k` low base-256 digits of `v`, least significant first, and `leVal` is its
inverse on byte lists. `unpackFast` computes `unpack` by divide and conquer and replaces it in
compiled code (`@[csimp]`, `Silmaril.Prelude.Bytes.Digits.Thms`).
-/

@[expose] public section

namespace Silmaril.KBytes

/-- The `k` low base-256 digits of `v`, least significant first. -/
def unpack : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, v => UInt8.ofNat v :: unpack k (v / 256)

/-- The little-endian value of a byte list. -/
def leVal : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leVal bs

/-- Divide-and-conquer `unpack`: `O(M(n) log n)` instead of `k` big-number divisions. It
replaces `unpack` in compiled code (`unpack_eq_unpackFast`). -/
def unpackFast (k v : Nat) : List UInt8 :=
  if k ≤ 64 then unpack k v
  else unpackFast (k / 2) (v % 256 ^ (k / 2)) ++ unpackFast (k - k / 2) (v / 256 ^ (k / 2))
termination_by k
decreasing_by all_goals omega

end Silmaril.KBytes
