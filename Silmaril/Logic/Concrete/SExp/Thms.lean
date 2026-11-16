module

public import Silmaril.Logic.Concrete.SExp.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms
import Silmaril.Proofs.Logic.Concrete.SExp.Basic

/-!
# Concrete syntax over S-expressions: numerals, laws

`num?_num`: a numeral reads back. `legal_num`: numerals are legal atoms for the reader.
-/

@[expose] public section

namespace Silmaril.Logic.Concrete.SExp

open Silmaril.Logic.Smt.SExpr.Writer (LegalExpr)

@[simp] theorem num?_num (n : Nat) : num? (num n) = some n := Proofs.Logic.Concrete.SExp.num?_num n

theorem legal_num (n : Nat) : LegalExpr (num n) := Proofs.Logic.Concrete.SExp.legal_num n

end Silmaril.Logic.Concrete.SExp
