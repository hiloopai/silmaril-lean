module

public import Silmaril.Logic.ACL2.Standard.FixedWidth.Defs
public import Silmaril.Logic.ACL2.Standard.BitSelection.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.FixedWidth

open Silmaril.Logic.ACL2.Standard
open Object

private theorem select_after_mod (n p q k : Int) (hp : p ≠ 0) :
    (n % (p * (q * k)) / p) % q = n / p % q := by
  rw [Int.emod_def n (p * (q * k)), Int.mul_assoc p (q * k), Int.sub_mul_ediv_left _ _ hp,
    Int.mul_assoc q k, Int.sub_eq_add_neg, ← Int.mul_neg, Int.add_mul_emod_self_left]

theorem fixedWidthProjection_eq_select (x : Object) {container width offset : Nat}
    (h : offset + width ≤ container) :
    fixedWidthProjection container width offset x =
      partSelectWidthLow x (integer width) (integer offset) := by
  have factor : (2 : Int) ^ container =
      (2 : Int) ^ offset * ((2 : Int) ^ width * (2 : Int) ^ (container - (offset + width))) := by
    rw [← Int.pow_add, ← Int.pow_add]
    congr 1
    omega
  simp only [fixedWidthProjection, partSelectWidthLow, loghead, logtail,
    integerFix_integer, Int.natCast_pow]
  change integer (x.integerFix % (2 : Int) ^ container / (2 : Int) ^ offset % (2 : Int) ^ width) =
    integer (x.integerFix / (2 : Int) ^ offset % (2 : Int) ^ width)
  have divisor : (2 : Int) ^ offset ≠ 0 := Int.pow_ne_zero (by decide : (2 : Int) ≠ 0)
  rw [factor, select_after_mod _ _ _ _ divisor]

end Silmaril.Proofs.Logic.ACL2.Standard.FixedWidth
