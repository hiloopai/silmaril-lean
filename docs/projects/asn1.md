# ASN.1 and DER

A transcription of the Distinguished Encoding Rules of
[ITU-T X.690](https://www.itu.int/rec/T-REC-X.690) (08/2015 or later) for the
ASN.1 types of [ITU-T X.680](https://www.itu.int/rec/T-REC-X.680) used by the
X.509 profile, with the time rules of
[RFC 5280](https://www.rfc-editor.org/rfc/rfc5280) §4.1.2.5. Everything is
proved from the standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
and builds on core Lean plus `Silmaril.Encoding.Relation`.

## Topics

| Topic | Definitions | Main results |
| --- | --- | --- |
| [Digits](../../Silmaril/Formats/ASN1/Digits/Thms.lean) | `digitsBE`/`ofDigitsBE`, base-256 `beBytes`/`beNat`, base-128 `base128`/`readBase128`, `Base128Octets` (X.690 §8.1.2.4.2, §8.19.2) | the minimal spellings are unique and the readers are sound and complete (`base128Octets_iff`, `readBase128_eq_some`, `beBytes_beNat`) |
| [Value](../../Silmaril/Formats/ASN1/Value/Defs.lean) | `TagClass`, `Tag`, the length-erased TLV tree `Value` | |
| [Der](../../Silmaril/Formats/ASN1/Der/Thms.lean) | `IdentifierOctets`, `LengthOctets`, `DerList`, `derRel` (X.690 §8.1, §10.1); `encode`, `decode`, `Value.wf` | `derRel_iff` (the relation is the graph of `encode` on well-formed values), `decode_sound`, `decode_complete`, `derRel_functional`, `derRel_deterministic`, `encode_injective` |
| [Codec](../../Silmaril/Formats/ASN1/Codec/Thms.lean) | `Codec σ α` (data: `WF`, `enc`, `dec`), `Codec.Lawful`, `Codec.rel`; combinators `prim`, `cons`, `explicit`, `nil`, `field`, `optField`, `optLast`, `defaulted`, `seqOf`, `setOf`, `orElse`, `any`, `iso`, `refine`, `derCodec` | lawful codecs have functional, deterministic relations with sound and complete decoders; every combinator preserves lawfulness (`lawful_*`); `derCodec_rel_eq`: the DER relation of a schema is `derRel` composed with the schema relation |
| [Universal](../../Silmaril/Formats/ASN1/Universal/Thms.lean) | BOOLEAN, INTEGER (`Int`, and `natural` for 0..MAX), BIT STRING, OCTET STRING, NULL, OBJECT IDENTIFIER, UTF8String, PrintableString, IA5String; `sequence`, `sequenceOf`, `setOf` | all lawful; `intOfContent?_intContent`, `intContent_of_intOfContent?` (minimal two's complement) |
| [Time](../../Silmaril/Formats/ASN1/Time/Thms.lean) | `DateTime`, UTCTime and GeneralizedTime contents, the `Time` CHOICE, `rfc5280Time` | all lawful |
| [Vectors](../../Silmaril/Formats/ASN1/Vectors.lean) | known-answer checks by `decide +kernel` | |

Proofs longer than a few lines are in `Silmaril/Proofs/Formats/ASN1/`.

## What DER means here

The byte layer `derRel` checks the type-independent rules:

- identifier octets: single-octet form for tag numbers 0..30, minimal
  high-tag-number form (no leading `0x80` octet) from 31;
- length octets: definite form only, short form below 128, long form minimal
  (no leading zero octet) with 1..126 subsequent octets;
- no end-of-contents tag, so no indefinite lengths;
- the whole input is one TLV: `decode` rejects truncation and trailing octets.

The type-dependent rules are in the codecs:

- BOOLEAN contents are `0xFF` or `0x00` (§11.1);
- INTEGER contents are minimal two's complement (§8.3.2), never empty;
- BIT STRING: unused-bits octet in 0..7, zero when there are no bits, and the
  unused bits are zero (§11.2.1);
- OBJECT IDENTIFIER: at least two arcs, first arc 0..2, second arc below 40
  unless the first is 2, minimal base-128 subidentifiers (§8.19);
- string types are read in the primitive form only (§10.2); PrintableString and
  IA5String check their character sets, UTF8String checks UTF-8 validity;
- `DEFAULT` components equal to the default are rejected (§11.5);
- `SET OF` components must be in ascending order of their encodings, padded
  with trailing zero octets for the comparison (§11.6);
- UTCTime is `YYMMDDHHMMSSZ` for 1950–2049 and GeneralizedTime is
  `YYYYMMDDHHMMSSZ`, both with valid dates and times (§11.7, §11.8 and the
  RFC 5280 profile, which forbids fractional seconds). `rfc5280Time` also
  requires UTCTime exactly for the years 1950–2049.

## Not covered

- BER and CER: indefinite lengths, constructed string encodings, non-minimal
  lengths and alternative BOOLEAN encodings are rejected, not decoded.
- Universal types outside the list above (REAL, ENUMERATED, BMPString,
  TeletexString, UniversalString, …) and `SET` with components (only `SET OF`).
- GeneralizedTime with fractional seconds or a local time offset, and UTCTime
  with offsets: DER and RFC 5280 exclude them.
- The trailing-zero rule for BIT STRINGs with named bits (§11.2.2) and
  `SEQUENCE` extensibility markers are schema properties that a client states
  with `Codec.refine`.
- `optField` requires distinct tags for adjacent optional components, as
  X.680 §25.6 does; its lawfulness theorem takes that as a hypothesis.
- No `ByteArray` interface: octet strings are `List UInt8` throughout.
- X.509 certificates are not part of this topic.
