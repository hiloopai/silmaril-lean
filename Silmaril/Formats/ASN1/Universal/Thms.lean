module

public import Silmaril.Formats.ASN1.Universal.Defs
import Silmaril.Formats.ASN1.Codec.Thms
import Silmaril.Proofs.Formats.ASN1.Universal

/-!
# ASN.1: universal types under DER, laws

Every contents codec and value codec of `Universal.Defs` is lawful: its decoder
inverts its encoder on well-formed values, and everything it decodes is well
formed and re-encodes to the input. In particular each value has exactly one
contents encoding (minimal INTEGERs, canonical BOOLEANs, zero BIT STRING
padding, minimal OID subidentifiers).
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

namespace Content

/-- Minimal two's complement round-trips every integer. -/
theorem intOfContent?_intContent (z : Int) : intOfContent? (intContent z) = some z :=
  Proofs.Formats.ASN1.intOfContent?_intContent z

/-- The INTEGER reader accepts only minimal two's complement. -/
theorem intContent_of_intOfContent? {bs : List UInt8} {z : Int} (h : intOfContent? bs = some z) :
    intContent z = bs :=
  Proofs.Formats.ASN1.intContent_of_intOfContent? h

theorem oidOfContent?_oidContent {arcs : List Nat} (h : oidWF arcs) :
    oidOfContent? (oidContent arcs) = some arcs :=
  Proofs.Formats.ASN1.oidOfContent?_oidContent h

theorem lawful_boolean : boolean.Lawful := Proofs.Formats.ASN1.lawful_boolean
theorem lawful_null : null.Lawful := Proofs.Formats.ASN1.lawful_null
theorem lawful_octets : octets.Lawful := Proofs.Formats.ASN1.lawful_octets
theorem lawful_integer : integer.Lawful := Proofs.Formats.ASN1.lawful_integer
theorem lawful_bitString : bitString.Lawful := Proofs.Formats.ASN1.lawful_bitString
theorem lawful_oid : oid.Lawful := Proofs.Formats.ASN1.lawful_oid
theorem lawful_utf8 : utf8.Lawful := Proofs.Formats.ASN1.lawful_utf8
theorem lawful_ia5 : ia5.Lawful := Codec.lawful_refine lawful_octets _
theorem lawful_printable : printable.Lawful := Codec.lawful_refine lawful_octets _

end Content

theorem lawful_boolean : boolean.Lawful := Codec.lawful_prim _ Content.lawful_boolean
theorem lawful_integer : integer.Lawful := Codec.lawful_prim _ Content.lawful_integer
theorem lawful_bitString : bitString.Lawful := Codec.lawful_prim _ Content.lawful_bitString
theorem lawful_octetString : octetString.Lawful := Codec.lawful_prim _ Content.lawful_octets
theorem lawful_null : null.Lawful := Codec.lawful_prim _ Content.lawful_null
theorem lawful_oid : oid.Lawful := Codec.lawful_prim _ Content.lawful_oid
theorem lawful_utf8String : utf8String.Lawful := Codec.lawful_prim _ Content.lawful_utf8
theorem lawful_printableString : printableString.Lawful :=
  Codec.lawful_prim _ Content.lawful_printable
theorem lawful_ia5String : ia5String.Lawful := Codec.lawful_prim _ Content.lawful_ia5
theorem lawful_natural : natural.Lawful := Proofs.Formats.ASN1.lawful_natural

theorem lawful_sequence {α : Type} {c : Codec (List Value) α} (hc : c.Lawful) :
    (sequence c).Lawful :=
  Codec.lawful_cons _ hc

theorem lawful_sequenceOf {α : Type} {c : Codec Value α} (hc : c.Lawful) :
    (sequenceOf c).Lawful :=
  Codec.lawful_cons _ (Codec.lawful_seqOf hc)

theorem lawful_setOf {α : Type} {c : Codec Value α} (hc : c.Lawful) : (setOf c).Lawful :=
  Codec.lawful_cons _ (Codec.lawful_setOf hc)

end Silmaril.Formats.ASN1
