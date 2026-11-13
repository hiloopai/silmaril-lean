module

public import Silmaril.Cerberus.Codec.WellFormed.Defs

/-!
# Cerberus documents as layered encodings

`Encodes = sexpCerberus ⨾ cerberusSyntax` follows the shared text-format pattern.
The syntax layer is the codec's encoder graph, restricted to ordered maps,
valid digests and enum registrations, pulled back through the structural tagged-tree reader.
The checked executable parser decides this relation. Header provenance and
Core typing are separate from this encoding.
-/

@[expose] public section

namespace Silmaril.Cerberus.Encoding

open Silmaril Formats.SExpEncoding TaggedCodec Codec.WellFormed

/-- Digest lengths, strict map ordering and registered enum integer types. -/
def Valid (d : Codec.Document) : Prop :=
  digestProblems [] (Codec.document.enc d) ++ mapProblems d.bindings ++ enumProblems d.enumBindings = []

/-- Cerberus syntax over the shared lexical target. -/
def cerberusSyntax : EncRel SExp Codec.Document :=
  (Codec.document.toEncRel.restrict Valid).pullPartial taggedDoc?

theorem syntax_functional : cerberusSyntax.Functional :=
  ((Codec.document.functional rfl).anti (EncRel.restrict_le _ _)).pullPartial _

/-- The shared-target encoder is correct for the checked syntax layer. -/
theorem syntax_encoderCorrectOn :
    cerberusSyntax.EncoderCorrectOn Valid (fun d => taggedDoc (Codec.document.enc d)) := by
  intro d hd
  exact ⟨Codec.document.enc d, taggedDoc?_taggedDoc _, rfl, hd⟩

/-- Canonical lexical spelling followed by checked Cerberus syntax. -/
def Encodes : EncRel String Codec.Document := sexpCerberus ⨾ cerberusSyntax

theorem encodes_functional : Encodes.Functional :=
  sexpCerberus_functional.comp syntax_functional

/-- The diagnostic parser's accepted language is the layered specification. -/
theorem parseDocument_iff {text : String} {d : Codec.Document} :
    parseDocument text = .ok d ↔ Encodes text d := by
  rw [parseDocument_eq_ok_iff]
  constructor
  · rintro ⟨s, t, hs, ht, hl, hd, hv⟩
    have he := Codec.document.canonical t d hd
    refine ⟨s, ⟨⟨s, t, hs, ht, hl⟩, hs⟩, t, ht, he, ?_⟩
    simpa [Valid, he] using hv
  · rintro ⟨s, ⟨⟨s', t', hs', ht', hl⟩, hs⟩, t, ht, he, hv⟩
    change Codec.document.enc d = t at he
    have hss : s' = s := Option.some.inj (hs'.symm.trans hs)
    subst s'
    have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst t'
    refine ⟨s, t, hs, ht, hl, ?_, ?_⟩
    · rw [← he]
      exact document_complete d
    · simpa [Valid, he] using hv

/-- The Option interface uses the same diagnostic parser. -/
def parse? (text : String) : Option Codec.Document := (parseDocument text).toOption

theorem parse?_eq_some_iff {text : String} {d : Codec.Document} :
    parse? text = some d ↔ parseDocument text = .ok d := by
  unfold parse?
  cases parseDocument text <;> simp [Except.toOption]

theorem parse?_sound : Encodes.DecoderSound parse? :=
  fun _ _ h => parseDocument_iff.1 (parse?_eq_some_iff.1 h)

theorem parse?_complete : Encodes.DecoderComplete parse? :=
  fun _ _ h => parse?_eq_some_iff.2 (parseDocument_iff.2 h)

theorem encodes_eq_ofDecoder : Encodes = EncRel.ofDecoder parse? :=
  EncRel.eq_ofDecoder parse? parse?_sound parse?_complete

/-- Exact UTF-8 bytes of the text relation, using the shared carrier transport. -/
def EncodesBytes : EncRel (List UInt8) Codec.Document := Encodes.push Unicode.utf8

theorem encodesBytes_functional : EncodesBytes.Functional :=
  Unicode.functional_push_utf8 encodes_functional

/-- Byte parsing decodes UTF-8 before using the checked document parser. -/
def parseBytes? (bytes : List UInt8) : Option Codec.Document :=
  (Unicode.utf8? bytes).bind parse?

theorem parseBytes?_sound : EncodesBytes.DecoderSound parseBytes? := by
  intro bytes d h
  obtain ⟨text, ht, hd⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨text, Unicode.utf8?_eq_some_iff.1 ht, parse?_sound text d hd⟩

theorem parseBytes?_complete : EncodesBytes.DecoderComplete parseBytes? := by
  rintro bytes d ⟨text, rfl, hd⟩
  change (Unicode.utf8? (Unicode.utf8 text)).bind parse? = some d
  rw [Unicode.utf8?_utf8]
  exact parse?_complete text d hd

instance : TextSyntax Codec.Document := ⟨⟨Encodes, encodes_functional⟩⟩

instance : BinarySyntax Codec.Document := TextSyntax.utf8Binary Codec.Document

/-- Retain the accepted source and its document through the shared pair type. -/
def withText? (text : String) : Option (WithText Codec.Document) :=
  WithText.ofDecoder? parse? parse?_sound text

/-- Retain the accepted UTF-8 bytes and their document. -/
def withBinary? (bytes : List UInt8) : Option (WithBinary Codec.Document) :=
  WithBinary.ofDecoder? parseBytes? parseBytes?_sound bytes

end Silmaril.Cerberus.Encoding
