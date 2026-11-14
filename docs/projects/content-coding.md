# HTTP content codings

Named content codings (RFC 9110 §8.4) on top of the lossless compression
framework ([compression.md](compression.md)): the IANA registry as data, which
decoder each name denotes, bounded decoding, chains of codings, and the HTTP
fields that name them (Content-Encoding, Accept-Encoding).

## Modules

| Module | Contents |
| --- | --- |
| [`Formats/Compression/Registry/Defs.lean`](../../Silmaril/Formats/Compression/Registry/Defs.lean) | `Coding`, `registry` (`Entry`: name, aliases, layer, reference, `Status`), `ofName?`, `Externals`, `Coding.decoder?`/`encoder?`, `DecodeError`, `stage`, `guarded`, `decodeChain`/`encodeChain`/`guardedChain`, `StagesWithin`, `Profile`, `httpProfile`, `Decoder.bounded` |
| [`Formats/Compression/Registry/Thms.lean`](../../Silmaril/Formats/Compression/Registry/Thms.lean) | registry, decoder, round-trip, chain and bound theorems (proofs in `Proofs/Formats/Compression/Registry.lean`) |
| [`Formats/Compression/Zstd/{Defs,Thms}.lean`](../../Silmaril/Formats/Compression/Zstd/Defs.lean) | **partial** zstd: XXH64, frame header, raw and RLE blocks, skippable frames; known answers only |
| [`Formats/Compression/SyncFlush/{Defs,Thms}.lean`](../../Silmaril/Formats/Compression/SyncFlush/Defs.lean) | raw DEFLATE ending at a sync flush (an empty non-final stored block) or at `BFINAL`, with an installed LZ77 window; `inflateMessage`/`inflateMessages`: RFC 7692 §7.2.2 permessage-deflate decompression with context takeover and `max_window_bits`. This is the interface for the WebSocket track (the WebSocket framing and negotiation are not here). All RFC 7692 §7.2.3 examples are checked. The round trip with a sync-flushing encoder is planned |
| [`Net/Http/ContentCoding/Defs.lean`](../../Silmaril/Net/Http/ContentCoding/Defs.lean) | list elements, `parseContentEncoding`, `resolve`, `decodeContent`, `parseAcceptEncoding`, `qOf`, `select`, `selectFor` |
| [`Net/Http/ContentCoding/Thms.lean`](../../Silmaril/Net/Http/ContentCoding/Thms.lean) | selection and identity rules, Content-Encoding decoding, RFC 9110 examples (proofs in `Proofs/Net/Http/ContentCoding.lean`) |

## The registry

The IANA "HTTP Content Coding Registry" (RFC 9110 §18.6 plus later
registrations) and, for the boundary, the names of the "HTTP Transfer Coding
Registry" (RFC 9112 §7.3). Names are lowercase tokens matched
case-insensitively (RFC 9110 §8.4.1); `x-gzip` and `x-compress` are aliases.

| Name | Layer | Reference | Status | Decoder here | Evidence |
| --- | --- | --- | --- | --- | --- |
| `identity` | content (reserved) | RFC 9110 §12.5.3 | reserved | `some` (identity) | `decoder?_identity`, `decodeAll_identity` |
| `gzip` (`x-gzip`) | content, transfer | RFC 9110 §8.4.1.3, RFC 1952 | **proved** | `Gzip.decoder.members` (a gzip *file*: one or more members) | `decoder?_gzip`, `gzip_roundTrip`, `gzip_concat`, `gzip_trailing_zero`, `decodeContent_gzip`, `decodeContent_gnu`; plus the Gzip topic's theorems |
| `deflate` | content, transfer | RFC 9110 §8.4.1.2, RFC 1950 around RFC 1951 | **proved** | `Zlib.decoder.whole` (zlib, **not** raw DEFLATE) | `decoder?_deflate`, `deflate_ne_raw`, `deflate_rejects_raw`, `raw_rejects_deflate`, `deflate_roundTrip`, `decodeContent_deflate` |
| `zstd` | content | RFC 8878 §7.2, RFC 9659 | partial subset | `Zstd.decode ext.zstdWindowMax` (raw/RLE blocks only) | `decoder?_zstd`, Zstd known answers |
| `aes128gcm` | content | RFC 8188 | abstract | `Externals.aes128gcm` (a parameter; `none` by default) | `decoder?_aes128gcm` |
| `br` | content | RFC 7932 | planned | none | `decoder?_planned` |
| `compress` (`x-compress`) | content, transfer | RFC 9110 §8.4.1.1 (LZW) | planned | none | `decoder?_planned` |
| `dcb` | content | RFC 9842 §4 | planned (needs dictionary) | none | `decoder?_planned` |
| `dcz` | content | RFC 9842 §5 | planned (needs dictionary) | none | `decoder?_planned`, `Zstd.frame_dcz_header` |
| `exi` | content | W3C EXI 1.0 | planned | none | `decoder?_planned` |
| `pack200-gzip` | content | JSR 200 (removed by JEP 367) | deprecated | none | `status_pack200gzip` |
| `chunked` | transfer only | RFC 9112 §7.1 | not a content coding | — | `ofName?_chunked`, `decodeContent_chunked` |
| `trailers` | transfer (reserved) | RFC 9112 §7.3 | not a content coding | — | `ofName?_trailers` |

Status meanings (`Registry.Status`): **proved** — a decoder is defined in this
library and its round trip and container laws are proved; **checked** — a
decoder exists but is only checked on known answers (no coding currently);
**partial subset** — a strict subset of the format decodes, the rest is
rejected, known answers only; **abstract** — a parameter supplied by another
track; **planned** — not implemented, plan below; **deprecated**, **reserved**.
`status_proved`, `status_planned`, `status_zstd` record the table by `decide`.

## Proved, checked, defined

Proved (standard axioms only):

- chains: `decodeChain_append` (decoding `cs ++ ds` decodes `ds` first, then
  `cs`), `encodeChain_append`, `decodeChain_encodeChain` (per-coding round trips
  give every chain's round trip), `decodeChain_neutral`/`encodeChain_neutral`
  (a coding that decodes to its input, such as `identity`, is neutral anywhere),
  `decodeAll_encodeAll` for the registry;
- bounds: `guarded_eq_ok_iff`, `guardedChain_sound`, `guardedChain_complete`,
  `guardedChain_agree` (bounded = unbounded, or `tooLarge`), `Profile.decode_le`
  (every successful non-empty chain under a profile is at most `maxDecoded`),
  `Profile.decode_sound`, `Profile.decode_complete`; member level
  `bounded_eq_ok_iff`, `bounded_tooLarge_iff`, `bounded_malformed_iff`,
  `sound_bounded`;
- Accept-Encoding: `select_pos` (selected ⇒ `q > 0`), `select_mem` (selected ⇒
  server coding or `identity`), `select_max`, `select_eq_none`,
  `selectFor_supported` (selected ⇒ `identity` or `Profile.supports`),
  `qOf_identity_eq_zero_iff` and `acceptable_identity_iff` (rule 2),
  `select_empty` (empty field ⇒ `identity`), `select_noField` (rule 1),
  `Qvalue.parseQvalue_le` (shared with HTTP/1.1's `TE`), `parseAcceptEncoding_le`, `qOf_le`;
- Content-Encoding: `decodeContent_sound`, `decodeContent_le`,
  `decodeContent_none`, `decodeContent_gzip`, `decodeContent_deflate`.

Checked by `decide` (known answers): RFC 9110 §12.5.3's five examples, alias and
case normalisation, selection examples (`example_*`), `decodeContent_gnu` and
`decodeContent_gnu_tooLarge` (GNU gzip's vector under `x-gzip`), XXH64 published
values, zstd frames hand-built from RFC 8878.

Defined only: `Profile.maxRatio` (ratio limit, enforced by `Profile.limit` but
with no theorem beyond `limit_le`), `Profile.maxChain` (enforced by
`decodeContent`), `dczWindow`, `dcbWindow`.

## Assumptions and choices

- **The bound is semantic.** `guarded`, `Profile.decode` and `Decoder.bounded`
  are defined from the list-level specification, which computes the whole
  output before comparing its length with the limit. The theorems say which
  inputs a resource-safe decoder must reject (`tooLarge`) and that it agrees with
  the specification otherwise; they do not bound the memory of evaluating the
  specification. Operationally, zlib 1.3.1's streaming inflater
  (`Inflate.member`, `Inflate.raw`) takes an output capacity in every call;
  `sound_bounded` turns a finished run whose output fits the limit into the
  bounded decoder's answer. That a capacity-limited run *stops* by the limit is
  not stated. Completeness of the inflater is proved (`Inflate.gzip_complete`,
  `Inflate.zlib_complete`), and each streaming call appends at most its output
  capacity (`Inflate.member_call_output`).
- `Profile.within` bounds every stage of a chain, not only the last, so nested
  codings (`gzip, gzip`) cannot expand past `maxDecoded` at any stage.
- Accept-Encoding weights the RFC leaves open: an unlisted, non-excluded
  `identity` gets the least weight `1` (0.001), so a listed coding wins; with no
  field every coding has weight 1000 and the server's first choice wins; ties go
  to server order, `identity` last; the first entry for a repeated coding counts.
  `*` covers `identity` only through rule 2 (`*;q=0` excludes it).
- The list parser splits at commas; this is exact for these two fields, which
  admit no quoted strings. Parameters other than `q` are rejected.
- `gzip` requires at least one member; an empty body labelled `gzip` is
  malformed. Callers decide which bodies are decoded (e.g. not 204/304 or HEAD).
- `Coding.decoder?` for `deflate` is strict zlib. RFC 9110 §8.4.1.2 notes that
  some implementations send raw DEFLATE; accepting that would be a separate,
  explicitly lenient decoder (and `deflate_ne_raw` shows it differs).

## Content codings versus transfer codings

Transfer codings (`Transfer-Encoding`, `TE`, `chunked`; RFC 9112 §6.1, §7) are
properties of one HTTP/1.1 message and are owned by the HTTP/1.1 track
(`Silmaril/Net/Http1`), which this work does not touch. Content codings are
properties of the representation (RFC 9110 §8.4). A recipient removes transfer
codings first and then content codings. Here `chunked` and `trailers` resolve to
no content coding (`ofName?_chunked`, `ofName?_trailers`), so a
`Content-Encoding: chunked` is reported as `unknownCoding`
(`decodeContent_chunked`). `gzip`, `deflate` and `compress` are registered in
both registries with the same data format; the registry's `Layer` records this,
and a transfer-coding track can reuse `Coding.decoder?` for them.

## gzip coverage audit

Read from `Gzip/Basic.lean`, `Gzip/Defs.lean`, `Deflate/*`, `Checksum/*` and
`Inflate/Stream/GzipHeader.lean`:

| Item (RFC 1952 / 1951) | State |
| --- | --- |
| magic `1f 8b`, `CM = 8` | checked; other `CM` rejected |
| reserved `FLG` bits 5–7 | must be zero (rejected otherwise) |
| `FTEXT`, `MTIME`, `XFL`, `OS` | ignored by the member decoder (`Framing Unit`); exposed by the structured parser `GzipHeader.parseHeader`, which accepts exactly what the decoder accepts (`parseHeader_agrees`) |
| `FEXTRA` | the decoder skips `XLEN` bytes; `GzipHeader` exposes them and has a subfield (`SI1 SI2 LEN`) parser; subfields are not validated on decode |
| `FNAME`, `FCOMMENT` | skipped up to the zero byte by the decoder, exposed by `GzipHeader.parseHeader`; ISO 8859-1 content **not** validated |
| `FHCRC` | **checked**: low 16 bits of the CRC-32 of the header bytes before it |
| CRC-32 trailer | **checked** against `crc32` of the output |
| `ISIZE` trailer | **checked**: output length mod 2^32 |
| multi-member files | **proved** semantics: `decompress_eq` (= `decoder.members`), `members_encoder`, `decompress_append`; `gzip_concat` |
| trailing garbage | **rejected** (stricter than GNU gzip, which ignores trailing zeros with a warning): `gzip_trailing_zero` |
| encoder | `Gzip.encoder` (stored blocks) and `Gzip.encoderFixed` (greedy LZ77, one fixed-Huffman block), both round trips proved; no dynamic-Huffman encoder. The registry's `gzip` encoder is the stored one |
| DEFLATE decoder | sound and complete for the independent RFC 1951 semantics `DeflateSpec` (`DeflateSpec.deflateTake_iff`, zlib's `Policy.strict`); gzip files: `ContainerSpec.gzipDecompress_iff`; all block types, `BTYPE = 11`, distance codes 30/31, literal/length symbols 286/287, `HLIT > 286`/`HDIST > 30`, incomplete codes (except the single-code case) and distances past the output rejected |
| fuel | the decoder is fuel-bounded by `bitsLeft + 1`; fuel is never the cause of a failure: `decompressBlocks_stable` and `decodeSymbolsFuel_stable` (in `Raw/…/Inflate/Stream/{Progress,Fuel}.lean`) prove any adequate fuel gives the same result, every block/symbol consumes a bit; `readCodeLengths` gets `total + 1` steps, each adding at least one length |
| CRC-32 | the reflected shift register `crc32Byte` (polynomial `0xEDB88320`) is **proved** equal to the GF(2) polynomial definition (`Checksum.crc32_eq_spec`), plus published values |
| append law | **proved**: `Gzip.local`, from `Deflate.local` (and `Zlib.local`) |
| streaming | the zlib 1.3.1 gzip member machine is sound, rejection-sound and complete (`Inflate.gzip_sound`, `Inflate.gzip_complete`) |
| vectors | GNU gzip and CPython `hello`, a corrupted CRC rejected |

The former open tasks `Deflate.Task.local`, `Inflate.Task.member_complete` and
`Inflate.Task.raw_complete` are proved (`Deflate.task_local`, `Inflate.task_member_complete`,
`Inflate.task_raw_complete`).

## Plans

Each step is a topic `Formats/Compression/<Format>/{Defs,Thms}.lean` with a
member `Decoder`, known answers from an independent implementation (libzstd,
the brotli reference decoder) recorded with their tool versions, then laws.

### zstd (RFC 8878, RFC 9659)

Done: XXH64 (`Zstd.xxh64`, published values), frame header, window formula,
raw/RLE blocks, `Block_Maximum_Size`, `Frame_Content_Size` and checksum checks,
skippable frames, the 8 MiB HTTP limit as a parameter.

1. `Zstd/Fse`: FSE table construction from normalized counts (§4.1.1) and the
   decoding state machine; theorem: the built table has `2^Accuracy_Log` cells
   and each symbol appears `count` times.
2. `Zstd/Huffman`: Huffman literals (§4.2): weights (FSE-compressed or direct),
   `Max_Number_of_Bits`, 1 or 4 streams with the jump table; reuse
   `Deflate.Huffman`'s canonical-code lemmas where possible.
3. `Zstd/Literals`: the literals section (raw, RLE, compressed, treeless with a
   repeated table).
4. `Zstd/Sequences`: sequence header, the predefined/RLE/FSE/repeat modes for
   literal-length, match-length and offset codes, the interleaved backward
   bitstream (§3.1.1.3.2), and **repeat offsets** (§3.1.1.5) as a separate
   pure state machine with its three-slot update law proved.
5. `Zstd/Execute`: sequence execution against the window; theorem: output only
   copies from at most `Window_Size` back, so a `Window_Size ≤ 8 MiB` frame needs
   no more history (the RFC 9659 contract).
6. Dictionaries (§5): raw-content and structured (`0xEC30A437`) dictionaries,
   `Dictionary_ID` matching; `dcz` = the 40-byte skippable header (already
   accepted by `frame`) + a frame decoded with the dictionary whose SHA-256 is
   checked (Crypto region) and window `dczWindow`.
7. Laws: `frame.Consumes`, a stored-like encoder (`rawFrame` generalised to any
   size) with `RoundTrip`, then `Registry` status `proved`.

### brotli (RFC 7932)

1. `Brotli/Bits`: the LSB-first bit reader (reuse `Bits.Bitstream`) and the
   stream header `WBITS` (§9.1), window `2^WBITS - 16`.
2. `Brotli/MetaBlock`: meta-block header (§9.2): `ISLAST`, `MNIBBLES`, `MLEN`,
   `ISUNCOMPRESSED`, metadata meta-blocks; first milestone: streams made only of
   uncompressed and metadata meta-blocks, with an encoder and `RoundTrip`.
3. `Brotli/Prefix`: simple and complex prefix codes (§3.4, §3.5), code-length
   code, repeat codes 16/17; completeness check like `Deflate.validCodeLengths`.
4. `Brotli/Blocks`: block types and counts for the three categories, block-switch
   commands (§6).
5. `Brotli/Context`: context modes and the literal/distance context maps with
   inverse move-to-front and RLE of zeros (§7).
6. `Brotli/Commands`: insert-and-copy lengths, distance codes with the
   ring buffer of last distances and `NPOSTFIX`/`NDIRECT` (§4, §5).
7. `Brotli/Dictionary`: the 122,784-byte static dictionary (Appendix A, hash
   recorded, included as data rather than proof text) and the 121 transforms
   (Appendix B); theorem: transform output lengths.
8. Laws: `Consumes`, the uncompressed encoder's `RoundTrip`, vectors from the
   reference decoder; `dcb` = 36-byte header (`ff 44 43 42` + SHA-256) + Shared
   Brotli with a prefix dictionary, 16 MiB window (RFC 9842 §4).

### compress (LZW)

`Formats/Compression/Lzw`: the `.Z` header (`1f 9d`, max bits, block mode),
variable-width codes 9…`maxbits`, the `CLEAR` code (256) in block mode, and the
historical code-group alignment quirk after a width change; encoder and
`RoundTrip`; vectors from `ncompress`. Low priority: rarely used on the web.

### aes128gcm, exi, pack200-gzip

`aes128gcm` stays abstract here; the crypto track supplies AES-128-GCM and the
RFC 8188 record layer (salt, `rs`, `idlen`, keyid, HKDF-derived key and nonce,
padding delimiter) as an `Externals.aes128gcm` decoder. `exi` is a W3C XML
format outside this library's scope; `pack200-gzip` is deprecated.

## Check

```sh
lake build --wfail Silmaril.Formats.Compression.Registry.Thms \
  Silmaril.Formats.Compression.Zstd.Thms Silmaril.Net.Http.ContentCoding.Thms \
  Silmaril.Net.Http.Qvalue.Thms Silmaril.Net.Http1.Codings.Thms
```

## Integration follow-ups

- **qvalue parser:** shared. `Net.Http.Qvalue.parseQvalue` (RFC 9110 §12.4.2) is used by
  both Accept-Encoding here and HTTP/1.1's `TE` (`Http1.Codings`).
- **gzip in the HTTP/1.1 track:** #158's `CodingLib` decodes the `gzip` transfer coding
  as a file of one or more members (`Decoder.members`), like this registry, as RFC 9112
  §7.2 requires through RFC 9110 §8.4.1.3. `ContainerSpec.gzipDecompress_iff` and
  `ContainerSpec.zlib_take_iff` are the decoder laws for both; the status table here still
  cites the stored round trips.
- **xxHash:** `Zstd.xxh64` is `XxHash.xxh64` (#169), one definition for zstd and the
  `Checksum.xxh64Low32` streaming checksum.
