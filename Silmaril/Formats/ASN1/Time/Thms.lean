module

public import Silmaril.Formats.ASN1.Time.Defs
import Silmaril.Formats.ASN1.Codec.Thms
import Silmaril.Proofs.Formats.ASN1.Time

/-!
# ASN.1: UTCTime and GeneralizedTime, laws

The time codecs are lawful: each valid date and time in range has exactly one
contents encoding, and the readers accept nothing else.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

theorem Content.lawful_utcTime : Content.utcTime.Lawful := Proofs.Formats.ASN1.lawful_utcTime

theorem Content.lawful_generalizedTime : Content.generalizedTime.Lawful :=
  Proofs.Formats.ASN1.lawful_generalizedTime

theorem lawful_utcTime : utcTime.Lawful := Codec.lawful_prim _ Content.lawful_utcTime

theorem lawful_generalizedTime : generalizedTime.Lawful :=
  Codec.lawful_prim _ Content.lawful_generalizedTime

theorem lawful_time : time.Lawful := Proofs.Formats.ASN1.lawful_time

theorem lawful_rfc5280Time : rfc5280Time.Lawful := Codec.lawful_refine lawful_time _

end Silmaril.Formats.ASN1
