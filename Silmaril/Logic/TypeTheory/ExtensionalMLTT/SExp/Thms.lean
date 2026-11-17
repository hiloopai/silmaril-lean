module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms
public import Silmaril.Logic.Concrete.Codec.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp.Basic

/-!
# Extensional MLTT as S-expressions: round trips

* `decodeJdg_encodeJdg`: decoding inverts encoding (at the level of S-expressions, for every
  judgment, whatever its names).
* `decodeJdg_eq_some_iff`: `decodeJdg e = some J` iff `e` denotes `J`; the decoder accepts exactly
  the canonical forms, and `encodeJdg_injective`.
* `legal_encodeJdg_iff`: a judgment's concrete form is legal for the ASCII reader iff its names
  are legal atoms (`LegalNames`).
* `parseJdg_printJdg`: for a judgment with legal names, printing then parsing gives it back.
  `legalNames_of_parseJdg`: every parsed judgment has legal names, so the byte syntax covers
  exactly these judgments.
-/

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Smt.SExpr.Writer (LegalExpr)

theorem decodeJdg_encodeJdg (J : EJdg) : decodeJdg (encodeJdg J) = some J :=
  Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp.decodeJdg_encodeJdg J

/-- **The decoder accepts exactly the canonical forms.** -/
theorem decodeJdg_eq_some_iff {e : SE} {J : EJdg} : decodeJdg e = some J ↔ Denotes e J :=
  Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp.decodeJdg_eq_some_iff

theorem encodeJdg_injective : Function.Injective encodeJdg := fun a b h => by
  have := decodeJdg_encodeJdg a; rw [h, decodeJdg_encodeJdg] at this; exact (Option.some.inj this).symm

/-- A concrete judgment is legal for the reader exactly when its names are legal atoms. -/
theorem legal_encodeJdg_iff (J : EJdg) : LegalExpr (encodeJdg J) ↔ LegalNames J :=
  Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp.legal_encodeJdg_iff J

/-- **Bytes round trip**, for judgments with legal names. -/
theorem parseJdg_printJdg (J : EJdg) (h : LegalNames J) : parseJdg (printJdg J) = some J :=
  Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp.parseJdg_printJdg J h

/-- Every parsed judgment has legal names. -/
theorem legalNames_of_parseJdg {bytes : List UInt8} {J : EJdg} (h : parseJdg bytes = some J) :
    LegalNames J :=
  Proofs.Logic.TypeTheory.ExtensionalMLTT.SExp.legalNames_of_parseJdg h

/-- **The default presentation of extensional MLTT judgments**, `silmaril.mltt.judgment`
(version 1). -/
def codec : Silmaril.Logic.Concrete.SExpCodec EJdg where
  name := "silmaril.mltt.judgment"
  version := "1"
  encode := encodeJdg
  decode := decodeJdg
  decode_eq_some_iff _ _ := decodeJdg_eq_some_iff

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp
