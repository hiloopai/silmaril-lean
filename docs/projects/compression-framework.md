# Compression formats: parameters, containers, capabilities, transforms

This page describes the layer of the compression framework at which formats are catalogued,
certified and composed. The member-decoder vocabulary (`Decoder`, `Consumes`, `Local`,
`RoundTrip`, `Framing`, `Checksum`, `Incremental`) is described in
[compression.md](compression.md). The layer keeps four things apart:

1. **What a format is**: its decoder, under explicit decode-side parameters.
2. **How containers wrap bodies**: header, body, trailer, where the body decoder may depend on
   the header.
3. **What is proved about a format**: a list of separately claimed capabilities, each with a
   proof. No guarantee is assumed to hold for every format.
4. **How whole-message transforms compose**: the shape that HTTP content-coding chains and keyed
   transforms plug into. Neither is part of this core.

## Modules

| Module | Contents |
| --- | --- |
| [`Compression/Defs.lean`](../../Silmaril/Formats/Compression/Defs.lean) | adds `Decoder.OutputLinear`, `Framing.wrapDep` and `Framing.WritesAt` |
| [`Compression/Thms.lean`](../../Silmaril/Formats/Compression/Thms.lean) | `wrap_eq_wrapDep`, `wrapDep_consumes`, `wrapDep_local`, `wrapDep_trailer`, `wrapDep_roundTrip`, `wrapDep_outputLinear`, `Decoder.whole_outputLinear`, `Decoder.members_outputLinear`, `RoundTrip.members_single` |
| [`Format/Defs.lean`](../../Silmaril/Formats/Compression/Format/Defs.lean) | `Format`, `Encoding`, `Scope`, `Rel`, `Capability`, `Capability.Holds`, `Kind`, `Certified`, and `Security` (`Assumption`, `Hazard`) |
| [`Format/Thms.lean`](../../Silmaril/Formats/Compression/Format/Thms.lean) | `Format.decode_ofDecoder`, `Certified.of`, `Certified.holds`, `Capability.deterministic_of_spec` |
| [`Transform/Defs.lean`](../../Silmaril/Formats/Compression/Transform/Defs.lean), [`Thms.lean`](../../Silmaril/Formats/Compression/Transform/Thms.lean) | `Transform`, `id`, `andThen`/`comp`, `whole`, `members`, `Inverts`, `LinearAt`, and the composition laws |
| [`Catalog/Defs.lean`](../../Silmaril/Formats/Compression/Catalog/Defs.lean), [`Thms.lean`](../../Silmaril/Formats/Compression/Catalog/Thms.lean) | `deflate`, `zlib`, `gzipMember`, `gzipFile`, `identity`, their encodings, claim lists and certificates |

## 1. Formats

```lean
structure Format where
  Params : Type                       -- decode-side parameters and context
  Error : Type                        -- format-specific rejection reasons
  decodeE : Params → List UInt8 → Except Error (List UInt8 × List UInt8)

def Format.decode (F : Format) (p : F.Params) : Decoder := Decoder.ofExcept (F.decodeE p)
```

`Params` holds only what a *decoder* needs: a preset dictionary or history, a window limit or a
dictionary table. Encoder choices such as levels or the header to write belong to
`Encoding F`:

```lean
structure Encoding (F : Format) where
  EParams : Type                 -- the encoder's own choices
  params : EParams → F.Params    -- the decode parameters its output is for
  encode : EParams → Encoder
```

An encoding is never assumed correct. Its round trip is the `roundTrip` capability.

## 2. Containers whose body depends on the header

`Framing.wrapDep (f : Framing H) (body : H → Decoder)` decodes the header, picks the body decoder
from the header metadata, and then checks the trailer. `Framing.wrap f body` is the special case
`f.wrapDep (fun _ => body)`, and `wrap_eq_wrapDep` proves this by `rfl`. Each `wrap_*` law has a
`wrapDep_*` counterpart that quantifies over every `h`. The round-trip law uses
`Framing.WritesAt hdr h trl`, which says the written header parses with metadata `h`, so the
encoder's body only has to round-trip through `body h`.

zlib is the first client. `zlib.decode dictionary` is
`(zlibFraming dictionary).wrapDep deflate.decode`, whose header (`zlibParseHeader`) resolves the
DEFLATE history:

- without `FDICT`, the history is empty;
- with `FDICT`, it is the 32 KiB suffix of the offered dictionary, provided the dictionary's
  Adler-32 matches `DICTID`;
- otherwise the member is rejected.

This is proved equal to the existing `Zlib.decoder` (`zlib_decode_none`) and
`Zlib.takeWithDictionary` (`zlib_decode_some`).

## 3. Capabilities and certificates

`Capability F` lists the kinds of claim. Each claim names the parameters it covers (`Scope F`:
`Scope.all`, `Scope.only p` or any predicate), because few laws hold uniformly.
`Capability.Holds` gives the meaning of each claim:

| Kind | Capability | `Holds` |
| --- | --- | --- |
| boundary | `consumes s`, `local s` | `(F.decode p).Consumes` / `.Local` for `p` in `s` |
| functional | `spec s R` | `F.decode p input = some (out, rest) ↔ R p input out rest` |
| functional | `deterministic s R` | `R` gives at most one `(out, rest)`. This is trivial for the decoder but not for a relation; it follows from `spec` (`deterministic_of_spec`) |
| vectors | `vector p input out rest` | a kernel-checked known answer |
| roundTrip | `roundTrip E` | `RoundTrip (F.decode (E.params e)) (E.encode e)` for every `e` |
| integrity | `trailer s trl` | every member ends with `trl out`, followed by the rest |
| integrity | `checksumSpec c ref` | `c.digest = ref`, an independent definition |
| resource | `outputLinear s k` | `Decoder.OutputLinear k`: at most `k` output bytes per consumed byte |
| resource | `callCapacity i output cap` | one call of machine `i` appends at most `cap call` to `output` |
| streaming | `streamSound p i`, `streamRejectSound p i`, `streamComplete p i` | `Incremental.Sound` / `RejectSound` / `Complete` against `F.decode p` |

```lean
structure Certified (F : Format) where
  claims : List (Capability F)
  proofs : ∀ c ∈ claims, c.Holds
  security : Security := {}
```

A certificate states exactly what is proved, and anything it does not list is not claimed.
`Certified.of claims h` builds a certificate from `h : Capability.All claims`, a conjunction with
one proof per claim, and `Certified.holds` reads a listed claim back.

**Security is data only.** `Security` records `assumptions : List Assumption` and
`hazards : List Hazard`. These are names, never Lean axioms or theorems. They mirror the crypto
catalogue of the crypto track (`Silmaril.Crypto.Catalog`, PR #157), where evidence
(recognized/implemented/vectors/functional/refinement) is kept apart from `Assumption`. There
is no `refinement` kind here because no compression decoder is proved to be computed by machine
code. The hazards recorded are:

- `checksumNotMac`: CRC-32 and Adler-32 detect accidents, not adversaries;
- `compressionLengthOracle`: CRIME/BREACH;
- `noIntegrity`.

## 4. Transforms and composition

```lean
structure Transform where
  Params : Type
  run : Params → List UInt8 → Option (List UInt8)
```

`Transform.whole F` (exactly one member) and `Transform.members F` (one or more members) turn a
format into a transform. `Transform.id` is the identity. `t.andThen u` runs `t` and then `u`
with paired parameters, and `comp u t` is the same composition written in function-composition
order. The following laws are proved:

- round trips compose (`inverts_andThen`);
- linear bounds multiply (`linearAt_andThen`, giving `l * k`);
- `id` is neutral (`id_andThen`, `andThen_id`) and composition is associative (`andThen_assoc`);
- a format's `RoundTrip` and `OutputLinear` claims become transform laws (`inverts_whole`,
  `inverts_members`, `linearAt_whole`, and `linearAt_members`, which also needs `Consumes`),
  directly or from a certificate (`Certified.inverts_whole`, `Certified.linearAt_members`).

As a non-vacuity example, `gzip_gzip_inverts` and `gzip_gzip_linear` cover the chain
`Content-Encoding: gzip, gzip`.

**Keyed transforms**, such as the `aes128gcm` content coding of RFC 8188 (decrypt, then
decompress), are `Transform`s whose `Params` hold key material and whose `Security.assumptions`
name the AEAD and KDF assumptions. Their definitions and proofs belong to the crypto track
(PR #157 and its follow-ups). Only the shape is fixed here.

## The certified formats

All proofs use only `propext`, `Classical.choice` and `Quot.sound`. The formats reuse the
existing decoders, so `Deflate.decoder`, `Zlib.decoder`, `Zlib.take`, `Gzip.decoder`,
`gzipMember`, `Gzip.decompress`, `Zlib.codec` and `Gzip.codec` are unchanged. The catalogue
proves that it denotes them.

### `deflate`

- **Parameters and errors.** `Params` is the preset history. `Error` is
  `Deflate.DecompressError`, and `decodeE` is `deflateTakeWithHistory`.
- **Link to the existing decoder.** `deflate_decode_nil : deflate.decode [] = Deflate.decoder`.
- **Claims** (`deflateClaims`):
  - `consumes all` and `local all`;
  - `spec (only []) deflateSpec` and `deterministic (only []) deflateSpec`, where
    `deflateSpec _ input out rest := DeflateSpec.Stream .strict input out rest`. These hold for
    the **empty history only**, because `DeflateSpec.Stream` describes streams decoded from an
    empty window. With a non-empty history no relational spec is claimed;
  - `vector []` (zlib's fixed-Huffman `"abc"`);
  - `roundTrip deflateStored` (stored blocks, for every history);
  - `roundTrip deflateFixed` (greedy LZ77 with one fixed-Huffman block, for the empty history);
  - `outputLinear all 2064`;
  - `callCapacity` for `Inflate.raw .v131` and `.develop`;
  - `streamSound []` and `streamComplete []` for `Inflate.raw .v131` and `.develop`.
- **Security.** Hazards: `noIntegrity`, `compressionLengthOracle`.

### `zlib`

- **Parameters.** `Params` is `Option (List UInt8)`, the offered dictionary.
- **Links to the existing decoders.** `zlib_decode_none`, `zlib_decode_some`, and
  `zlib_decompress` (`Zlib.decompress` is `Transform.whole zlib` at `none`).
- **Claims** (`zlibClaims`):
  - `consumes all` and `local all` (via `wrapDep`);
  - `trailer all Zlib.trailer`;
  - `checksumSpec adler32 adler32Ref`, the RFC 1950 §8.2 closed form;
  - two vectors: CPython `hello`, and the dictionary `AB` match;
  - `roundTrip` for `zlibStored`, `zlibFixed` and `zlibStoredWithDictionary` (an `FDICT`
    header, for every dictionary);
  - `outputLinear all 2064`;
  - `callCapacity` for the member machine (both versions);
  - `streamSound`, `streamRejectSound` and `streamComplete` at `none`, for both versions.
- **Security.** Hazards: `checksumNotMac "Adler-32"`, `compressionLengthOracle`.

### `gzipMember` and `gzipFile`

- **Links to the existing decoders.** `gzipMember.decode () = Gzip.decoder`, and `gzipFile`
  (`Transform.members gzipMember`) is `Gzip.decompress` (`gzipFile_decompress`).
- **Claims** (`gzipClaims`):
  - `consumes all`, `local all`, `trailer all Gzip.trailer`;
  - `checksumSpec crc32 crc32Spec`, the GF(2) definition;
  - `roundTrip gzipHeaders` (every *valid* header: the encoder parameter is
    `{h : GzipHeader.Header // h.Valid}`);
  - `roundTrip gzipFixed`;
  - `outputLinear all 2064`;
  - `callCapacity` and stream sound, reject-sound and complete for both versions.
- **Whole files.** `gzipFile_inverts` and `gzipFile_linear`.
- **Security.** Hazards: `checksumNotMac "CRC-32"`, `compressionLengthOracle`.

### `identity`

- **Decoder.** One member is the whole input.
- **Claims.** `consumes all`, `outputLinear all 1` and one vector.
- **Not self-delimiting.** `identity_not_local` proves this, so neither `local` nor a member
  round trip is claimed. As a transform it is `Transform.whole identity`, and `Transform.id` is
  the unparameterised identity.

### Deliberately not claimed

- A relational spec for DEFLATE with a non-empty history, or for zlib and gzip as wholes. Their
  bodies are DEFLATE, but no independent container relation is defined.
- Streaming for zlib with a dictionary (the member machine models dictionary-free members), and
  `streamRejectSound` for raw DEFLATE (not proved).
- Known-answer vectors for gzip in this catalogue. They exist as whole-file theorems
  (`Gzip.decompress_gnu`, `decompress_cpython`) and are not restated per member.
- Any security property, any compression ratio, and any machine-code refinement.

## Where future formats fit

| Format | Shape |
| --- | --- |
| zstd (RFC 8878) | `Params`: dictionaries by ID and a window limit (RFC 9659's 8 MiB HTTP limit is a parameter, not another format). Frame = `wrapDep` on the frame header (window size, dictionary ID, checksum flag). XXH64 is a `Checksum` with `checksumSpec`. Skippable frames and concatenation are `members` |
| brotli (RFC 7932) | raw self-delimiting `Format`, no container. `Params`: window bits (and a shared dictionary, for shared-dictionary brotli). The built-in static dictionary is part of the algorithm |
| LZ4 frame | `wrapDep` on the frame descriptor (block size, independence, checksum flags) around LZ4 blocks. xxHash-32 checksums |
| xz | container (stream header/footer, block headers, index) around LZMA2, whose filter chain and dictionary size come from the block header (`wrapDep`). CRC-32, CRC-64 and SHA-256 checks |
| bzip2 | stream header (block size), per-block and combined CRC-32 around BWT, MTF/RLE and Huffman. Concatenated streams are `members` |
| aes128gcm (RFC 8188) | keyed `Transform` from the crypto track, with `Security.assumptions` as data |

**The web layer is an adapter.** HTTP content-coding registry names, profiles with output limits,
and `Accept-Encoding` negotiation (PR #160's `Registry` and `Net/Http/ContentCoding`) sit on top
of this layer. They map coding names to `Certified` formats and chain them with
`Transform.andThen`, and the core imports nothing from HTTP. That PR's modules are not on this
branch and are not changed here. Adopting `Certified` there is follow-up work.

## Check

```sh
lake build --wfail Silmaril.Formats.Compression.Catalog.Thms Silmaril.Formats.Compression.Thms \
  Silmaril.Formats.Compression.Gzip.Thms
bash scripts/check-layout.sh
```
