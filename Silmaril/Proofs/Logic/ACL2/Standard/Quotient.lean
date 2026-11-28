module

public import Silmaril.Logic.ACL2.Standard.Quotient.Defs
import Mathlib.Data.Rat.Floor

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.Quotient

open Silmaril.Logic.ACL2.Standard.Quotient

theorem quotient_eq_div (n d : Nat) : nonnegativeQuotient n d = n / d := by
  rw [nonnegativeQuotient, Nat.div_eq_ite n d]
  by_cases h : d = 0 ∨ n < d
  · have h' : ¬ (0 < d ∧ d ≤ n) := by omega
    rw [ite_eq_left h, ite_eq_right h']
  · have h' : 0 < d ∧ d ≤ n := by omega
    rw [ite_eq_right h, ite_eq_left h', quotient_eq_div (n - d) d, Nat.add_comm]
termination_by n
decreasing_by omega

theorem floorRatio_eq_floor (q : Rat) : floorRatio q = q.floor := by
  by_cases hd : q.den = 1
  · simp [floorRatio, Rat.floor_def, hd]
  by_cases hn : 0 ≤ q.num
  · rw [floorRatio, ite_eq_right hd, ite_eq_left hn, quotient_eq_div, Rat.floor_def,
      ← Int.ofNat_ediv_ofNat, Int.toNat_of_nonneg hn]
  · have separated : ¬ (q.den : Int) ∣ (q.num.natAbs : Int) := by
      intro h
      exact hd ((Nat.gcd_eq_right (Int.ofNat_dvd.mp h)).symm.trans q.reduced)
    have positive : 0 < (q.den : Int) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero q.den_nz)
    have numerator := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt (Int.lt_of_not_ge hn))
    calc
      floorRatio q = -(↑(q.num.natAbs / q.den : Nat) : Int) - 1 := by
        rw [floorRatio, ite_eq_right hd, ite_eq_right hn, quotient_eq_div]
      _ = (-(q.num.natAbs : Int)) / (q.den : Int) := by
        rw [Int.neg_ediv, ite_eq_right separated, Int.sign_eq_one_of_pos positive, Int.ofNat_ediv_ofNat]
      _ = q.floor := by rw [Rat.floor_def]; exact congrArg (· / (q.den : Int)) numerator.symm

theorem floorInteger_eq_div (n : Int) (d : Nat) : floorInteger n d = n / (d : Int) := by
  rw [floorInteger, floorRatio_eq_floor, ← Rat.intCast_div_eq_divInt]
  exact Rat.floor_intCast_div_natCast n d

theorem modInteger_eq_mod (n : Int) (d : Nat) : modInteger n d = n % (d : Int) := by
  simp only [modInteger, floorInteger_eq_div]
  have h := Int.mul_ediv_add_emod n (d : Int)
  rw [Int.mul_comm] at h
  omega

end Silmaril.Proofs.Logic.ACL2.Standard.Quotient
