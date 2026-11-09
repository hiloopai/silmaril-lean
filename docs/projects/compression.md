# Lossless compression

A small framework for lossless compressed formats, with DEFLATE
([RFC 1951](https://www.rfc-editor.org/rfc/rfc1951)), zlib
([RFC 1950](https://www.rfc-editor.org/rfc/rfc1950)), gzip
([RFC 1952](https://www.rfc-editor.org/rfc/rfc1952)) and a streaming model of
zlib 1.3.1's inflater as its first clients.

## The framework

[`Formats/Compression/Defs.lean`](../../Silmaril/Formats/Compression/Defs.lean)
and [`Thms.lean`](../../Silmaril/Formats/Compression/Thms.lean):

| Concept | Definition | Laws |
| --- | --- | --- |
| Member decoder | `Decoder := List UInt8 → Option (List UInt8 × List UInt8)`: one self-delimiting member at the front of the input, and the rest | `Consumes` (the rest is a suffix), `Local` (bytes after a member pass through) |
| Whole buffer, files | `Decoder.whole`, `Decoder.members` (one or more concatenated members) | `RoundTrip.members` |
| Encoder, codec | `Encoder`, `RoundTrip d e`, `Codec` | `RoundTrip.whole`, `.surjective`, `.injective` |
| Container | `Framing H` (header with metadata `H`, trailer check), `Framing.wrap`, `Framing.encode` | `wrap_consumes`, `wrap_local`, `wrap_trailer`, `wrap_roundTrip` |
| Checksum | `Checksum` (`init`, `update`, `finish`), `Checksum.digest` | `digest_append` |
| Streaming | `Incremental` (machine, calls, `status`), `Sound`, `RejectSound`, `Complete` | `sound_agree`, `local_of_sound_complete` |

The specification of a format is its member decoder; encoders are optional. A
new format adds a topic `Formats/Compression/<Format>/{Defs,Thms}.lean` with its
decoder. The framework docstring records where zstd, bzip2, xz/LZMA2, brotli
and LZ4 fit; none of them is implemented.

## Formats

| Topic | Decoder | Main results |
| --- | --- | --- |
| [Deflate](../../Silmaril/Formats/Compression/Deflate/Thms.lean) | `Deflate.decoder` (`deflateTake`): stored, fixed and dynamic Huffman blocks | consumes, stored round trip, LZ77 compressor soundness, zlib-produced vectors for each block type, two rejections |
| [Zlib](../../Silmaril/Formats/Compression/Zlib/Thms.lean) | `Zlib.decoder = framing.wrap Deflate.decoder` | consumes, Adler-32 trailer, round trip, CPython vectors, dictionaries |
| [Gzip](../../Silmaril/Formats/Compression/Gzip/Thms.lean) | `Gzip.decoder = framing.wrap Deflate.decoder`; files are `decoder.members` | consumes, CRC-32/ISIZE trailer, round trip, multi-member files, GNU and CPython vectors |
| [Checksum](../../Silmaril/Formats/Compression/Checksum/Thms.lean) | `Checksum.adler32`, `Checksum.crc32` | published check values |
| [Inflate](../../Silmaril/Formats/Compression/Inflate/Thms.lean) | `Inflate.member version kind`, `Inflate.raw version`: zlib 1.3.1's resumable inflater as `Incremental` machines | sound and rejection-sound for every call schedule, schedules agree, packed fixed tables agree with the canonical decoder |

Assumptions and scope:

- The decoders are total list-based specifications, fuel-bounded by the input
  length. The theorems are only as faithful as these definitions; the vectors
  produced by zlib, CPython and GNU gzip check them against independent
  implementations.
- The inflater is a mathematical machine, not a refinement of zlib's C code.
- Open and frozen as `def Task.… : Prop` with conditional theorems:
  `Deflate.Task.local` (the append law for DEFLATE members, from which
  `Zlib.local_of_deflate` follows), `Inflate.Task.member_complete` and
  `Inflate.Task.raw_complete` (completeness of the machines, which give the
  append laws through `Incremental.local_of_sound_complete`).

## Layout

Definitions are in `Silmaril/Formats/Compression/**` and their headers. The
ported proofs are in `Silmaril/Raw/Formats/Compression/**`, unrefined; header
proofs that relate them to the framework are in
`Silmaril/Proofs/Formats/Compression/`.

## Check

```sh
lake build --wfail Silmaril.Formats.Compression.Inflate.Thms Silmaril.Formats.Compression.Gzip.Thms
```

These two headers import every compression module; `make library`
builds all of them.
