# Format languages

This page describes the byte languages of data formats in `Silmaril/Formats`: which inputs are
*valid*, given as Mathlib `Language UInt8`s. Each language has a proved decision procedure, and
depth, line or profile variants as named definitions. These are specifications. They are what
readers, validators and Wasm components are checked against, and they say nothing about the
correctness of any particular parser.

Each module states its standard, dialect and every choice in its documentation. Sources are
pinned in [`references.bib`](../../references.bib) with SHA-256.

## Stable semantic APIs

| Topic | Language and main definitions | Decision and key theorems | Source |
|---|---|---|---|
| `Formats.Utf8` | `Utf8.language`, `Utf8.IsWellFormed`, `Utf8.scalar`, `Utf8.multibyte`, `Bytes.IsUtf8` | `Utf8.isWellFormed_iff`, `isWellFormed_iff_exists_chars`, `isValidUTF8_iff` (Lean core), `decides_isWellFormed` | Unicode 15 Table 3-7, RFC 3629 |
| `Formats.JsonBytes` | `JsonBytes.language p` with `Profile.rfc8259` and `Profile.scalarEscapes`; `Text`, `Value`, `Elements`, `Members`; lexical `RegularExpression`s (`ws`, `number`, `string p`, `scalar p`); `Bytes.IsJson` | `Decide.textB_iff`, `decides_textB`, `language_isWellFormed` (UTF-8), `language_scalarEscapes_le` | RFC 8259 |
| `Formats.JsonBytes.Depth` | `JsonBytes.languageAt p d` (scalars depth 0, containers 1 + deepest child); `ValueAt` | `Decide.textAtB_iff`, `iUnion_languageAt`, `languageAt_mono`, `byteBracket_not_jsonDepth` | RFC 8259 §9 |
| `Formats.JsonLines` | `JsonLines.Policy` (`final`, `blankLines`, `crInText`) with `Policy.jsonLines` and `Policy.ndjson`; `lineOf pol L`, `frameLang pol L`, `language pol p`, `languageAt pol p d` | `frameB_iff`, `terminated_eq_frameItems`, `terminated_mem_itemBound_iff`, `language_isWellFormed`, `iUnion_languageAt` | jsonlines.org, NDJSON spec |
| `Formats.JsonEvents` | `Tree K S` (ordered, duplicates kept), `Event K S`, `Event.kind`, `Tree.toEvents`, `ofEvents?`, `language K S`, `Tree.depth` | `equivLanguage : Tree K S ≃ language K S`, `ofEvents?_eq_some_iff`, `toEvents_mem_depthBound_iff` | — |
| `Formats.JsonEvents.Scalar` | `Key = List UInt16`, `Scalar` (`null`, `bool`, `number lexeme`, `string units`), `Utf16.wellFormed`, `stringValid p`, `Scalar.valid p`, `eventValid p`, `ValidStream p` | `number_valid_iff`, `ValidStream.decidable` | RFC 8259 §6, §7, §8.2 |
| `Formats.Cbor.WellFormed` | `Cbor.wellFormed` (one well-formed item), `Item`, `Items`, `Head` | `isWellFormed_iff`, `skip_sound`, `item_skip`; all RFC 8949 Appendix F.1 vectors | RFC 8949 §3, App. C |
| `Formats.Cbor.Value` | `Cbor.Value` (representation-level: ordered maps, floats as width and bits), `encodeHead`, `Value.encode`, `decode`, `Value.Encodable` | `decode_encode`, `encode_injective`, `encode_mem_wellFormed` | RFC 8949 §4.2.1 heads |
| `Formats.Cbor.ModelValid` | `ModelValid.ok` (UTF-8 text, pairwise distinct key encodings, **relative to `Cbor.Value`**), `ModelValid.language` (shortest-head definite encodings only), `encodableB` | `check_iff`, `encodableB_iff`, `language_le_wellFormed` | RFC 8949 §5.3.1 (model-relative) |
| `Formats.Cbor.Drisl` | `Drisl.language P`; `Profile` = floats, int64 range, `CidBoundary` (`exact`/`prefix`), `LinkRule` (codecs, `(multihash code, digest length)` pairs); `LinkRule.dasl`, `.bdasl`, `.none`; profiles `drislExactCid`, `drislCidPrefix`, `drislBdaslExactCid`, `drislBdaslCidPrefix`, `drislNoLinks`, `drislNoFloatsExactCid`, `atprotoCoreExactCid`; `CidPayload` | `check_iff`, `cidOk_iff`, `cidOk_mono`, `cidOk_dasl_exact_iff`, `ok_tag_of_hashes_nil`, `language_mono`, `language_le_wellFormed`, `value_unique` | DRISL 2026-10-22, DASL CID, BDASL 2026-10-19, CBOR/c-42, atproto data model |
| `Formats.Cbor.Deterministic` | `Deterministic.language P` for `DetProfile` (`floatOk : FloatRule`, `utf8Text`); `FloatRule.none`, `.only64`, `.any`; `detOk` | `check_iff`, `language_le_wellFormed`, `value_unique`, `language_mono`, `drisl_le` | RFC 8949 §4.2.1 (relative to the float rule) |
| `Formats.Streaming` | `derivAcceptor r`, `utf8Acceptor`, `jsonAcceptor`, `jsonLinesAcceptor`, `cborAcceptor`, `jsonDepthAcceptor` | `…_correctInterleaved` (`Semantics.Acceptors`), `jsonDepthAcceptor_soundFold`, `jsonDepthAcceptor_completeFoldOn` | — |
| `Formats.JsonBytes.Accept` | `scalarHead`, `profileLang` | `decides_textB`, `decidesOn_scalarHead`, `profile_lt` (`Semantics.Accept`) | — |

Each decision theorem gives a `Decidable` instance, so `decide +kernel` checks closed examples.
`Silmaril.Formats.Accept.Lang.exact_ofBool_iff` turns a `Decides` fact into
`Lang.Exact (ofBool check) L`. `Silmaril.Formats.Format.ofLanguage L` makes any of these
languages a `Format`.

## Integration points

The WIT representations of JSON event streams and JSON Lines items are in
`Silmaril.Wasm.Component.Reference.WIT.Repr.Json` (#553), and the WIT string and item
languages in `Silmaril.Wasm.Component.Reference.WIT.Json`. The language registry and catalogue
use the definitions above; they do not restate them.

## Named assumptions and limits

- **JSON strings:** lone surrogate escapes are in `Profile.rfc8259`, not in
  `Profile.scalarEscapes`. `scalarEscapes` is I-JSON's surrogate rule only, not full I-JSON.
- **JSON Lines:** the empty file is zero lines under every policy, which neither source addresses.
  With an optional final newline and blank lines allowed, the bytes do not determine the
  item list.
- **CBOR values:** `Cbor.Value` is finer than RFC 8949's generic data model. Floats of different
  widths, and definite versus indefinite strings, are different values.
- **CBOR determinism:** `Cbor.Deterministic` checks definite lengths, shortest arguments and
  strictly sorted keys exactly. The float part of preferred serialization is the parameter
  `FloatRule`, so the language is RFC 8949 §4.2.1 core-deterministic only under the assumption
  that the rule is "shortest value-preserving width". That rule is not implemented. The
  provided rules are `none` (no floats), `only64` (CBOR/c-42 and DRISL, not RFC preferred) and
  `any`.
- **CBOR validity:** `ModelValid.ok` checks UTF-8 text and pairwise distinct key encodings in
  `Cbor.Value`, which is finer than RFC 8949's generic data model. It accepts a map whose half and
  double `1.5` keys RFC calls duplicates. `ModelValid.language` (shortest-head definite encodings
  only) both excludes RFC-valid encodings (non-shortest heads, indefinite lengths) and includes
  RFC-invalid ones. No inclusion with RFC-valid bytes is claimed in either direction; only
  decidability and well-formedness are proved. Tag-content validity is not checked.
- **DRISL tag 42:** whether bytes may follow a CID's digest is not settled by the normative DASL
  CID text. It is the profile parameter `CidBoundary`, and the named profiles carry it.
- **CID hashes:** allowed as `(multihash code, digest length)` pairs. DASL is `(0x12, 32)` and BDASL
  adds `(0x1e, 32)`. The empty pair set (`drislNoLinks`) rejects every tag-42 value. Fields are
  parsed as single-byte varints.
- **Repository CIDs:** the artifact registry's BLAKE3 CIDs use hash type `0x1e`. They are BDASL
  CIDs, not DASL CIDs. `drislExactCid` rejects them inside tag 42 and `drislBdaslExactCid` accepts
  them.
- **ATProto:** `atprotoCoreExactCid` covers only no floats and signed 64-bit integers.
  `blob` structure, reserved `$` fields and Lexicon constraints are not checked.
- **Readers:** `Silmaril.Formats.JsonWire.parse?_isSome_iff` proves that the RFC 8259 reader
  `JsonWire.parse?` accepts exactly `JsonBytes.language .rfc8259`. Its stages are proved against
  declarative grammars in `Silmaril.Formats.JsonWire.Grammar.Thms`, see "Proving a reader against
  a byte grammar" below. No other reader is related to these languages, and no lexer from bytes to
  events is proved.
- **Fast JSON loading:** [the scalar-Unicode loader](json-loading.md) provides indexed values,
  file elaborators and kernel proof tools without changing the wire reader or its guarantees.
- **Acceptors:** the JSON, JSON Lines and CBOR acceptors buffer their input; only
  `utf8Acceptor` is incremental.

## Proving a reader against a byte grammar

The proof that `JsonWire.parse?` accepts exactly the JSON texts is split by the reader's stages,
and each layer is a reusable API:

1. **UTF-8** (`Silmaril.Formats.Utf8.Thms`). `encode cs` is the UTF-8 encoding of characters.
   `String.fromUTF8?` inverts it (`fromUTF8?_eq_some`, `fromUTF8?_encode`), and it is injective
   (`encode_injective`), so splitting an encoding into well-formed parts splits the characters
   (`encode_eq_append`). The transport lemmas turn a byte regular expression on an encoding into
   a condition on the characters: `encode_mem_mul`, `encode_mem_star`, `encode_mem_add`,
   `encode_mem_char`, `encode_mem_byteRange`, `encode_mem_anyOf` and `encode_mem_multibyte`.
   Their side conditions are `Good` expressions, whose words are all well-formed UTF-8
   (`good_mul`, `good_star`, …).
2. **Lexemes** (`Silmaril.Formats.JsonWire.Grammar.Thms`). Each lexing function is proved sound
   and complete against a character condition: `quoted?` against `StrBody` and `decimal?` against
   `NumberChars`, and the conditions are the byte expressions read through UTF-8 (`mem_string`,
   `mem_number`).
3. **Lexer.** `lex` runs a per-character `step` (`Internal.step`). `tokensOf_cons` is one step,
   and the fuel only needs to cover the characters (`lex_tokens_eq`). Soundness says the tokens
   read are whitespace and lexemes (`Lexes`, `lexes_of_tokensOf`). Completeness goes one lexeme at
   a time: a lexeme followed by a delimiter is read as its token (`tokensOf_number`,
   `tokensOf_string`, …).
4. **Parser.** `TValue` is the RFC 8259 value grammar over tokens, written to mirror the
   recursive-descent procedures. `value?` reads all of a token list exactly when it is a `TValue`,
   with one fuel per token (`value?_eq_some_nil_iff`).
5. **Grammar.** One induction over the byte grammar's derivations shows the reader reads every
   text (completeness). One induction over `TValue` shows that whatever it reads is a text
   (soundness).

A new reader can reuse layers 1 and 4 unchanged, and needs a `step`, lexeme lemmas and the two
inductions of layer 5. Behaviour-preserving refactors make the reader easier to prove: the
lexer's step, escapes (`escape?`), signs (`splitSign`) and fractions (`splitFraction`) became
named functions, so each case of a proof is a small lemma instead of a `match` over character
literals.

## Checking

```sh
lake build --wfail Silmaril.Formats.JsonLines.Thms Silmaril.Formats.JsonEvents.Thms \
  Silmaril.Formats.Cbor.Drisl.Thms Silmaril.Formats.Streaming.Thms \
  Silmaril.Formats.JsonBytes.Accept.Thms
```
