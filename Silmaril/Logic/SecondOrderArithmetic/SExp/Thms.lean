module

public import Silmaril.Logic.SecondOrderArithmetic.SExp.Defs
public import Silmaril.Logic.Concrete.Codec.Thms
import Silmaril.Proofs.Logic.SecondOrderArithmetic.SExp.Basic

/-!
# Second-order arithmetic as S-expressions: the presentation

`decodeFormula_eq_some_iff`: the decoder accepts exactly the canonical forms. `codec` is the
presentation `silmaril.soa.formula` (version 1). Bytes round-trip for formulas whose printed atoms
are legal (`SExpCodec.parse_print`); names that are not legal atoms (with spaces, parentheses, …)
print but do not parse back.
-/

@[expose] public section

namespace Silmaril.Logic.SecondOrderArithmetic.SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)

theorem decodeFormula_eq_some_iff {e : SE} {φ : Formula String} :
    decodeFormula e = some φ ↔ encodeFormula φ = e :=
  Proofs.Logic.SecondOrderArithmetic.SExp.decodeFormula_eq_some_iff

/-- **The default presentation of second-order arithmetic formulas.** -/
def codec : SExpCodec (Formula String) where
  name := "silmaril.soa.formula"
  version := "1"
  encode := encodeFormula
  decode := decodeFormula
  decode_eq_some_iff _ _ := decodeFormula_eq_some_iff

end Silmaril.Logic.SecondOrderArithmetic.SExp
