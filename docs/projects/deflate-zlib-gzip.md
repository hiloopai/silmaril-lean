# DEFLATE, zlib and gzip: what is formalized, requirement by requirement

This page records, for each requirement, the evidence in this library for RFC 1951 (DEFLATE),
RFC 1950 (the zlib container) and RFC 1952 (gzip). It is written for consumers that use
these decoders as reference specifications, in particular erebor-lean. Statuses:

- **Proved**: a theorem in a `Thms` header, using only `propext`, `Classical.choice` and `Quot.sound`.
- **Checked**: an example evaluated by `decide` or `rfl`, kernel-checked, never with `native_decide`.
- **Policy**: a documented choice where the RFC leaves latitude.
- **Not formalized**: stated as such.

## Four different things

These are not the same object, and nothing here identifies them:

| Name | What it is | Here |
| --- | --- | --- |
| RFC 1951 DEFLATE | a bit-level compressed-data format | `Deflate.decoder` (`deflateTake`), `DeflateSpec.Stream` |
| RFC 1950 zlib | a container: 2-byte header, DEFLATE, Adler-32 of the output | `Zlib.decoder` (= `Zlib.take`), `ContainerSpec.ZlibMember`, `ZlibDictMember` |
| RFC 1952 gzip | a container: header with optional fields and FHCRC, DEFLATE, CRC-32 and ISIZE; files are one or more members | `Gzip.decoder` (= `gzipMember`), `Gzip.decompress` (= `gzipDecompress`), `GzipHeader`, `ContainerSpec.GzipMember`, `GzipFile` |
| the zlib **library** (`inflate`, `deflate`, `uncompress`, `gz*`, `windowBits`, return codes, compression levels) | a C API implementing all three formats | **not** modelled here. The `Inflate` topic models zlib 1.3.1's resumable inflater as an abstract machine, not its C code. The library's API contracts are erebor-lean's subject |

## The consumer contract (erebor-lean)

erebor-lean (`Erebor/Zlib/Spec/**`) uses, as its RFC-level "L0" references:

| Definition | Meaning in erebor | Evidence here |
| --- | --- | --- |
| `Deflate.deflateTake` | raw streams, `windowBits < 0` | `DeflateSpec.deflateTake_iff`, `Deflate.deflateTake_append` |
| `Zlib.take` | `uncompress`, inflate chain, `windowBits` 8–15 | `ContainerSpec.zlib_take_iff` (iff `ZlibMember`), `Zlib.take_eq_decoder`, `Zlib.local` |
| `gzipMember` | one member, `windowBits = 31` | `ContainerSpec.gzipMember_iff` (iff `GzipMember`), `Gzip.member_eq_decoder`, `Gzip.local` |
| `gzipDecompress` | the gz file API reference | `ContainerSpec.gzipDecompress_iff` (iff `GzipFile`), `Gzip.decompress_eq` (= `decoder.members`) |
| `gzipCompress` | test fixtures | `Gzip.decompress_compress`, `Gzip.compress_eq` |

erebor-lean states refinements as `∀ future, deflateTake (input ++ future) = .ok (out,
rest ++ future)`, and the same for `Zlib.take`. These follow from the append laws below.
erebor's open problem `zlib/refines/rfc1950--l1-stream` (`l1Complete`) is silmaril's
`Inflate.member_complete`, now proved.

## RFC 1951 DEFLATE

| Requirement | Status | Evidence |
| --- | --- | --- |
| An independent statement of RFC 1951, separate from the decoder: bit order (§3.1.1), canonical Huffman codes by the RFC's algorithm (§3.2.2), LZ77 copies with overlap (§3.2.3), stored blocks with `NLEN = ~LEN` (§3.2.4), length/distance tables (§3.2.5), fixed codes (§3.2.6), dynamic headers with repeat codes 16/17/18 across the lit/len–dist boundary (§3.2.7), blocks to `BFINAL` | Defined | `DeflateSpec.Defs`: `Stream p input out rest` |
| The spec matches the RFC's own examples | Checked | `fixedLitLenCode_table` (§3.2.6 table), `ofLengths_example` (§3.2.2 `ABCDEFGH`), `copyMatch_example` (§3.2.3 overlap) |
| The decoder is **sound and complete** for the spec: it returns `(out, rest)` iff the input starts with a valid stream decoding to `out`, followed by `rest` | Proved | `deflateTake_sound`, `deflateTake_complete`, `deflateTake_iff` |
| Decoding is a function (no ambiguity) | Proved | `Stream.functional` |
| Stored, fixed-Huffman and dynamic-Huffman blocks are all accepted | Proved via `deflateTake_iff`. Checked on zlib's vectors: `kat_stored`, `kat_fixed`, `kat_dynamic`, also as instances of `Stream` |
| Malformed input is rejected: `BTYPE = 11`, distance codes 30/31, lit/len 286/287, distances before the start of the output, bad `NLEN`, incomplete codes, truncation | Proved via completeness (anything the decoder accepts satisfies the spec, which excludes these). Checked: `kat_rejects_reserved_btype`, `kat_rejects_dist_code_30` |
| Policy differences from the letter of the RFC | Policy | `Policy.strict` (zlib's behaviour = the decoder) refines `Policy.rfc` (`Stream.strict_rfc`). Stricter than the RFC: `HDIST` 30/31 rejected; incomplete code-length codes rejected; incomplete lit/len or distance codes rejected, except one used symbol with a 1-bit code. Both policies: code 284 with extra bits `11111` is length 258 (as zlib); up to 7 padding bits after the final block are ignored. Listed in `DeflateSpec/Thms.lean` |
| Preset history (zlib `FDICT`): the decoder with an installed history is sound and complete for `StreamWithHistory`; only the last 32 KiB of a history can be referenced | Proved | `DeflateSpec.deflateTakeWithHistory_iff`, `StreamWithHistory.window` |
| **Append law**: bytes after a stream never change its decoding (former `Task.local`) | Proved | `Deflate.deflateTake_append`, `deflateTakeWithHistory_append`, `Deflate.local` (`task_local`) |
| Encoder validity | Proved | stored blocks: `Deflate.roundTrip`. Greedy LZ77 + one fixed-Huffman block: `Deflate.encoderFixed`, `roundTripFixed` (it stops exactly at its end: `compress_take`) |
| Resource bound | Proved | `Deflate.output_le`: at most 2064 output bytes per consumed input byte (258 per bit); see "Resources" |

## RFC 1950 zlib container

| Requirement | Status | Evidence |
| --- | --- | --- |
| An independent statement of RFC 1950 §2.2, separate from the decoder: CMF/FLG (`CM = 8`, `CINFO ≤ 7`, `FCHECK`), `FDICT = 0`, a `DeflateSpec.Stream` body, the big-endian Adler-32 trailer by its closed form `adler32Symbolic` | Defined | `ContainerSpec.Defs`: `ZlibHeader`, `ZlibMember input out rest` |
| The member decoder is **sound and complete** for it | Proved | `ContainerSpec.zlib_take_iff` (`Zlib.take`), `zlib_decompress_iff` (whole buffer) |
| Preset dictionary, independently: `FDICT = 1`, `DICTID` = Adler-32 (closed form) of the dictionary, body decoded with the whole dictionary as history (`StreamWithHistory`) | Defined; proved | `ContainerSpec.ZlibDictMember`; `zlib_takeWithDictionary_iff`: `Zlib.takeWithDictionary` accepts exactly `ZlibMember ∨ ZlibDictMember`. Profile: only `CINFO = 7` is specified with a dictionary, as the decoder implements (RFC 1950 allows smaller windows there) |
| Header: `CM = 8`, `CINFO ≤ 7`, `(CMF·256 + FLG) mod 31 = 0`; `FDICT = 1` is rejected by `Zlib.take` (dictionary-free) | Defined; checked | `zlibCheckHeader`, `decompress_fdict` |
| Preset dictionary: checked against `DICTID` and installed as DEFLATE history | Proved | `takeWithDictionary_eq_take`, `takeWithDictionary_stored`, `takeWithDictionary_wrong` |
| Body is RFC 1951 | Proved | `Zlib.decoder = framing.wrap Deflate.decoder` (`take_eq_decoder`) |
| Trailer: big-endian Adler-32 of the output | Proved | `decoder_trailer` |
| Adler-32 is mathematically correct (RFC 1950 §8.2 closed form) | Proved | `Checksum.adler32OfList_eq_symbolic`, `adler32_toNat_eq_symbolic`; check values RFC 1950 §9 |
| Append law | Proved | `Zlib.local` |
| Encoder round trip | Proved | `Zlib.roundTrip` (header `78 01`, stored blocks); compressing: `Zlib.roundTripFixed` |
| `FLEVEL` | Policy | ignored on decode, as RFC 1950 §2.2 allows ("not needed for decompression") |
| Window size: back-references are not limited to `2^(CINFO+8)` | Policy | the decoder accepts any distance within the output produced so far; zlib checks this only with `INFLATE_STRICT`. Documented, not enforced |

## RFC 1952 gzip

| Requirement | Status | Evidence |
| --- | --- | --- |
| An independent statement of RFC 1952 §2.2–2.3, separate from the decoder: header grammar (magic, `CM`, `FLG` bits with reserved bits zero, `MTIME`, `XFL`, `OS`, FEXTRA with `XLEN`, zero-terminated FNAME/FCOMMENT, FHCRC as the low 16 bits of `crc32Spec` of the preceding header bytes), a `DeflateSpec.Stream` body, the `crc32Spec` trailer and `ISIZE` = length mod 2³²; a file is one or more members with no other bytes | Defined | `ContainerSpec.Defs`: `GzipFlags`, `GzipMemberHeader`, `GzipMember input hdr out rest`, `GzipFile input out` |
| The decoders are **sound and complete** for it | Proved | `ContainerSpec.parseHeader_iff` (header), `gzipMember_iff` (member), `gzipDecompress_iff` (file) |
| Magic `1f 8b`, `CM = 8`, reserved `FLG` bits must be 0 (§2.4: "must give an error indication") | Proved/checked | `checkHeader`; `GzipHeader.parseHeader_agrees` |
| Optional fields: FEXTRA (`XLEN`), FNAME, FCOMMENT skipped; FHCRC checked as the low 16 bits of the CRC-32 of the preceding header | Proved | `parseHeader_agrees`; checked: `checkHeader_bad_hcrc` |
| The parsed header (FTEXT, MTIME, XFL, OS, extra, name, comment, FHCRC) is available | Proved | `GzipHeader.parseHeader`, which accepts exactly what the decoder accepts |
| FEXTRA subfield structure, ISO 8859-1 for FNAME/FCOMMENT, `XFL ∈ {2, 4}` | Policy | documented predicates (`parseSubfields`, `latin1Strict`, `xflDefined`), not acceptance conditions. RFC 1952 §2.4 allows a compliant decompressor to skip these fields |
| Trailer: CRC-32 and ISIZE (length mod 2³²), little-endian, checked | Proved | `decoder_trailer`, `gzipCheckTrailer`; checked: `decompress_bad_crc` |
| CRC-32 is mathematically correct (ISO 3309 / V.42 polynomial, RFC 1952 §8) | Proved | `crc32_eq_spec`, `crc32List_eq_spec`, `Checksum.crc32_digest_eq_spec`; also `crc32Spec_flip_ne` (every single-bit error is detected) |
| Body is RFC 1951 | Proved | `Gzip.decoder = framing.wrap Deflate.decoder` (`member_eq_decoder`) |
| Multiple members are concatenated (§2.2) | Proved | `decompress_eq` (= `decoder.members`), `members_encoder`, `decompress_append` |
| Trailing bytes after the last member | Policy | **rejected** (`gzipDecompress` needs every byte to belong to a member). GNU gzip warns about and ignores trailing zeros; zlib's `gz*` API stops at a non-gzip suffix. Consumers needing those behaviours must model them on top of `Gzip.decoder` (whose append law makes that straightforward) |
| Append law | Proved | `Gzip.local`, `Gzip.framing_local` |
| Encoder round trip | Proved | `Gzip.roundTrip` (fixed header). For any valid header (name, comment, extra, MTIME, OS, FHCRC): `GzipHeader.roundTrip`. `encodeMember default = Gzip.encoder`. Compressing: `Gzip.roundTripFixed` |
| Compliant compressor (§2.4: correct ID1, ID2, CM, CRC32, ISIZE) | Proved | the encoders above |

## External-encoder corpus

| Requirement | Status | Evidence |
| --- | --- | --- |
| The decoders agree with the reference zlib library on varied inputs: raw DEFLATE (level 1), zlib at levels 6 and 9 (with `memLevel = 1`: dynamic, fixed, dynamic blocks), `Z_HUFFMAN_ONLY`, `Z_RLE` (a length-258 match), `Z_FIXED`, `Z_SYNC_FLUSH` and `Z_FULL_FLUSH` inside a member, `windowBits = 9` (`CINFO = 1`), a preset dictionary (`zdict`), gzip with FNAME and MTIME (`gzip.GzipFile`), a two-member gzip file, and a member with FEXTRA, FNAME, FCOMMENT and FHCRC | Checked | `Corpus.Thms`: 12 vectors, 6130 bytes of output in all (≤ 768 per vector, distances up to 686), each also restated as an instance of `DeflateSpec.Stream`, `ZlibMember`, `ZlibDictMember` or `GzipFile` (`*_spec`). Generated with CPython 3.13.5 and zlib 1.3.1; the exact expressions are in the docstrings of `Corpus.Defs` |
| Corrupted inputs are rejected: a flipped bit in a dynamic block header, `FCHECK`, the Adler-32, CRC-32 and `ISIZE` trailers, FHCRC; a reserved `FLG` bit; a dictionary member with no or the wrong dictionary | Checked | `Corpus.Thms`: `badBody_take` … `zlibDict_wrongDictionary` |
| Large inputs and long distances (up to 32 KiB) | Not checked | kernel evaluation of the list-based decoder costs about a minute per KiB of output (quadratic), so the corpus stays small; long distances are covered by the proofs only |

## Streaming (zlib 1.3.1's inflater as a machine)

| Requirement | Status | Evidence |
| --- | --- | --- |
| Every finished call schedule outputs exactly the list decoder's result; failures are real rejections | Proved | `Inflate.member_sound`, `member_rejectSound`, `raw_sound`, `member_runs_agree` |
| Every accepted member or stream is finished by some schedule (former `Task.member_complete` and `Task.raw_complete`) | Proved | `Inflate.member_complete`, `zlib_complete`, `gzip_complete`, `raw_complete`, for both modelled versions |
| The machine is zlib's C code | Not formalized | it is a mathematical machine; erebor-lean relates zlib's binaries to it |

## Resources

| Requirement | Status | Evidence |
| --- | --- | --- |
| Post-hoc output limits for HTTP content codings | Proved | `Registry` (`Profile`, `bounded_*`) in #160 |
| Intrinsic output bound: decoded length ≤ 2064 × consumed input bytes, for every member and whole file (no limit applied after the fact) | Proved | `Deflate.output_le`, `withHistory_output_le`, `decompress_output_le`; `Zlib.output_le`, `Zlib.decompress_output_le`; `Gzip.output_le`, `members_output_le`, `decompress_output_le` |
| Operational bound: one call of the streaming machine emits at most its output capacity, and a schedule at most the sum of its capacities | Proved | `Inflate.raw_call_output`, `member_call_output`, `raw_run_output`, `member_run_output` |
| Decoders are total, fuel-bounded by the input length; fuel never causes a spurious failure | Proved | `decompressBlocks_stable`, `decodeSymbolsFuel_stable` |

## What is not claimed

- No compression ratio or performance claim. The compressing encoders (`encoderFixed`) use
  greedy LZ77 with one fixed-Huffman block. zlib's levels, lazy matching, dynamic-block construction and
  `deflateParams` are not modelled.
- The zlib library API (stream state, `Z_*` return codes, flush modes, `gz*` file
  semantics, `windowBits` selection) is not modelled here.
- Data structures and executable performance: the specifications are list-based. Executable
  `Array` mirrors are registered with `@[csimp]` and proved equal.

## Integration follow-ups (HTTP/1.1 track, #158 `CodingLib`)

Recorded for when the HTTP/1.1 work and this change have both landed:

- `CodingLib` decodes the `gzip` transfer coding as a single member
  (`Gzip.codec.decode.whole`). RFC 9112 §7.2 refers to the gzip *file* format
  (RFC 9110 §8.4.1.3, RFC 1952 §2.2), which may have several members. The preferred
  decoder is `Gzip.decompress` / `Gzip.decoder.members`, with `gzipDecompress_iff`
  (`ContainerSpec.Thms`) as its law. `Gzip.codec` stays as it is for compatibility.
- `CodingLib`'s docs can cite decoder correctness (`DeflateSpec.deflateTake_iff`,
  `ContainerSpec.gzipMember_iff`, `gzipDecompress_iff`, `zlib_take_iff`) only once this
  change is on main. Until then, its stored-codec round trip is not evidence of decoder
  correctness, and the docs should not present it as such.
- The qvalue parser (RFC 9110 §12.4.2) exists twice: in `Http1.Codings` (#156) and in
  `Net.Http.ContentCoding` (#160). Whichever lands second should reuse the other's.
