# Encoding building blocks

Small, reusable byte and text encodings with proofs, in `Silmaril/Encoding` and
`Silmaril/Formats/Compression/Bwt`. Each item lists what is proved and what is only
checked on examples.

| Piece | Standard | Proved | Checked |
| --- | --- | --- | --- |
| `RadixFacts` | the generic radix-2^k group codec behind RFC 4648 | the strict group decoder accepts exactly the encoder's output, for any byte count; non-zero pad bits are rejected | |
| `Base32` (`std`, `hex`) | RFC 4648 §6, §7 | `decode?_eq_some_iff` (exact), `encode_injective`, `length_encode` | all §10 vectors; rejection of bad padding, pad bits and characters |
| `Base16` (`upper`, `lower`) | RFC 4648 §8 | exact strict decoder, injectivity, length; `decodeAnyCase?` (case-insensitive, a separate function) | §10 vectors |
| `Base64` (existing) | RFC 4648 §4, §5 | exact strict decoder | |
| `Ascii` | RFC 20 | character classes; case mapping laws (idempotence, `toLower ∘ toUpper = toLower`); case-insensitive equality is an equivalence; byte codec is exact; ASCII strings are their own UTF-8 encoding (`utf8_of_isAsciiStr`) | |
| `Punycode` | RFC 3492 (Bootstring with the Punycode parameters) | `decode (encode cs) = some cs` for every code-point list, via the variable-length integer layer and the insertion layer; `encode` is injective with ASCII output; `adapt` bounds | all 19 §7.1 samples, both directions |
| `Bwt` | Burrows–Wheeler (SRC report 124), move-to-front, bzip2's RUNA/RUNB zero runs | `ibwt (bwt s) = s` for every string, periodic ones included (LF-mapping lemma); the last column is a permutation of the input; MTF and zero-run round trips | `banana`, `abracadabra` |

Not included, and planned:

- **IDNA** (ToASCII/ToUnicode, UTS #46 mapping, the `xn--` label rules beyond the prefix).
  `Punycode.aceLabel` only prepends `xn--`.
- **Punycode mixed-case annotation** (RFC 3492 Appendix A).
- **bzip2 itself**: the RLE1 stage, the Huffman coding of MTF/zero-run symbols with up to 6
  tables and selectors, block CRCs, and the stream container. `Bwt/Defs.lean` lists the
  steps.
- Efficient BWT construction (suffix sorting). The specification sorts all rotations.

Crypto primitives, Diffie–Hellman and X.509 belong to the crypto track.
