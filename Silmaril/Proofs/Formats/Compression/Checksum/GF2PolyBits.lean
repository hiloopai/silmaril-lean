module

/-! Bit-level `Nat` facts behind the termination of `GF2Poly.mod`
(`Silmaril.Formats.Compression.Checksum.GF2Poly`). -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.GF2Poly

/-- A number in `[2 ^ n, 2 ^ (n + 1))` has bit `n` set. -/
theorem testBit_of_bounds {x n : Nat} (hlo : 2 ^ n ≤ x) (hhi : x < 2 ^ (n + 1)) :
    x.testBit n = true := by
  have hx : x ≠ 0 := by have := Nat.one_le_two_pow (n := n); omega
  have hlog : x.log2 = n := by
    rw [Nat.log2_eq_iff hx]; exact ⟨hlo, hhi⟩
  rw [← hlog]; exact Nat.testBit_log2 hx

/-- Two numbers whose top bit is bit `n` cancel above bit `n`. -/
theorem xor_lt_of_bounds {x y n : Nat} (hx1 : 2 ^ n ≤ x) (hx2 : x < 2 ^ (n + 1))
    (hy1 : 2 ^ n ≤ y) (hy2 : y < 2 ^ (n + 1)) : x ^^^ y < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor]
  rcases Nat.lt_or_eq_of_le hi with h | h
  · have hp : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]; rfl
  · subst h; rw [testBit_of_bounds hx1 hx2, testBit_of_bounds hy1 hy2]; rfl

/-- Subtracting the divisor, shifted under the leading term of the dividend,
lowers the dividend: the step of polynomial long division over GF(2). -/
theorem xor_shiftLeft_log2_lt {a g : Nat} (ha : a ≠ 0) (hg : g ≠ 0) (h : g.log2 ≤ a.log2) :
    a ^^^ (g <<< (a.log2 - g.log2)) < a := by
  have ha1 := Nat.log2_self_le ha
  have ha2 := Nat.lt_log2_self (n := a)
  have hg1 := Nat.log2_self_le hg
  have hg2 := Nat.lt_log2_self (n := g)
  have hk : 2 ^ a.log2 = 2 ^ g.log2 * 2 ^ (a.log2 - g.log2) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hk1 : 2 ^ (a.log2 + 1) = 2 ^ (g.log2 + 1) * 2 ^ (a.log2 - g.log2) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hp := Nat.two_pow_pos (a.log2 - g.log2)
  refine Nat.lt_of_lt_of_le (xor_lt_of_bounds ha1 ha2 ?_ ?_) ha1
  · rw [Nat.shiftLeft_eq, hk]; exact Nat.mul_le_mul_right _ hg1
  · rw [Nat.shiftLeft_eq, hk1]; exact Nat.mul_lt_mul_of_pos_right hg2 hp

end Silmaril.Proofs.Formats.Compression.GF2Poly
