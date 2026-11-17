module

public import Silmaril.Logic.HOLLight.SExp.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms
public import Silmaril.Logic.Concrete.Codec.Defs
import Silmaril.Proofs.Logic.HOLLight.SExp.Basic

/-!
# HOL Light types and terms as S-expressions: round trips

* `decodeTm_encodeTm`, `decodeTy_encodeTy`: decoding inverts encoding.
* `decodeTm_eq_some_iff`: `decodeTm e = some t` iff `e` denotes `t` (`encodeTm t = e`). So the
  decoder accepts exactly the canonical forms, and `encodeTm_injective`.
* `legal_encodeTm`: every atom of a concrete term is legal ASCII for the reader.
* `parseTm_printTm`: printing a term and parsing the bytes gives back the term.
-/

@[expose] public section

namespace Silmaril.Logic.HOLLight.SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Smt.SExpr.Writer (LegalExpr)

theorem decodeTy_encodeTy (t : Ty) : decodeTy (encodeTy t) = some t :=
  Proofs.Logic.HOLLight.SExp.decodeTy_encodeTy t

theorem decodeTm_encodeTm (t : Tm) : decodeTm (encodeTm t) = some t :=
  Proofs.Logic.HOLLight.SExp.decodeTm_encodeTm t

/-- **The decoder accepts exactly the canonical forms.** -/
theorem decodeTm_eq_some_iff {e : SE} {t : Tm} : decodeTm e = some t ↔ Denotes e t :=
  Proofs.Logic.HOLLight.SExp.decodeTm_eq_some_iff

theorem encodeTm_injective : Function.Injective encodeTm := fun a b h => by
  have := decodeTm_encodeTm a; rw [h, decodeTm_encodeTm] at this; exact (Option.some.inj this).symm

theorem legal_encodeTm (t : Tm) : LegalExpr (encodeTm t) :=
  Proofs.Logic.HOLLight.SExp.legal_encodeTm t

/-- **Bytes round trip.** -/
theorem parseTm_printTm (t : Tm) : parseTm (printTm t) = some t :=
  Proofs.Logic.HOLLight.SExp.parseTm_printTm t

/-- **The default presentation of HOL Light terms**, `silmaril.hol-light.term` (version 1). -/
def codec : Silmaril.Logic.Concrete.SExpCodec Tm where
  name := "silmaril.hol-light.term"
  version := "1"
  encode := encodeTm
  decode := decodeTm
  decode_eq_some_iff _ _ := decodeTm_eq_some_iff

end Silmaril.Logic.HOLLight.SExp
