module

public import Silmaril.Logic.ACL2.Standard.Quotient.Defs
import Silmaril.Proofs.Logic.ACL2.Standard.Quotient

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Quotient

theorem quotient_eq_div (n d : Nat) : nonnegativeQuotient n d = n / d :=
  Proofs.Logic.ACL2.Standard.Quotient.quotient_eq_div n d

theorem floorRatio_eq_floor (q : Rat) : floorRatio q = q.floor :=
  Proofs.Logic.ACL2.Standard.Quotient.floorRatio_eq_floor q

theorem floorInteger_eq_div (n : Int) (d : Nat) : floorInteger n d = n / (d : Int) :=
  Proofs.Logic.ACL2.Standard.Quotient.floorInteger_eq_div n d

theorem modInteger_eq_mod (n : Int) (d : Nat) : modInteger n d = n % (d : Int) :=
  Proofs.Logic.ACL2.Standard.Quotient.modInteger_eq_mod n d

end Silmaril.Logic.ACL2.Standard.Quotient
