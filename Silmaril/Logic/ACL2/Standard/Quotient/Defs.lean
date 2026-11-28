module

public import Init.Data.Rat.Basic
import Init.Omega

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Quotient

/-- The translated ACL2 NONNEGATIVE-INTEGER-QUOTIENT on natural inputs. -/
def nonnegativeQuotient (n d : Nat) : Nat :=
  if d = 0 ∨ n < d then 0 else 1 + nonnegativeQuotient (n - d) d
termination_by n
decreasing_by omega

/-- The branches of stock ACL2 FLOOR after its rational product is formed.
The quotient argument is stored in lowest terms with a positive denominator. -/
def floorRatio (q : Rat) : Int :=
  if q.den = 1 then q.num
  else if 0 ≤ q.num then nonnegativeQuotient q.num.toNat q.den
  else -(nonnegativeQuotient q.num.natAbs q.den : Int) - 1

/-- ACL2 FLOOR on an integer dividend and a natural divisor. -/
def floorInteger (n : Int) (d : Nat) : Int := floorRatio (Rat.divInt n d)

/-- ACL2 MOD on an integer dividend and a natural divisor. -/
def modInteger (n : Int) (d : Nat) : Int := n - floorInteger n d * d

end Silmaril.Logic.ACL2.Standard.Quotient
