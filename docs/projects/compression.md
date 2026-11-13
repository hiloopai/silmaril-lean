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
- The append laws and the completeness of the inflater are open; see Open goals.

## Building blocks

[`Formats/Compression/Bwt`](../../Silmaril/Formats/Compression/Bwt/Thms.lean)
holds the reversible transforms that bzip2 applies before its Huffman stage, as
total list functions: the Burrows–Wheeler transform (Burrows and Wheeler, SRC
Research Report 124, 1994) over any linearly ordered alphabet, specified by
sorting all rotations, with its inverse by the LF mapping (`ibwt_bwt`, for every
string, periodic ones included; the last column is a permutation of the input);
move-to-front over bytes (`mtfDecode_mtfEncode`, symbols below 256); and bzip2's
RUNA/RUNB zero-run coding (`zrleDecode_zrleEncode`). `banana`, `abracadabra` and
small move-to-front and run codes are checked by `decide`. This is not bzip2: there
is no `Decoder`, block format, Huffman stage, CRC or stream container, and the
initial run-length stage (RLE1) is missing. The `Defs.lean` docstring lists the
remaining steps to a bzip2 decoder.

## Open goals

Frozen as `def Task.… : Prop`, not proved; the theorems that need them take them as
hypotheses.

- `Silmaril.Formats.Compression.Deflate.Task.local`: bytes appended after a DEFLATE
  member never change how it decodes (`Deflate.decoder.Local`). Conditional:
  `Zlib.local_of_deflate` (the same law for zlib).
- `Silmaril.Formats.Compression.Inflate.Task.member_complete`: zlib 1.3.1's member
  machine (`Inflate.member .v131 .zlib`) finishes every member `Zlib.decoder` accepts,
  when the whole input is given at the start. Conditional: `Inflate.zlib_local_of_task`
  (the zlib append law, through `Incremental.local_of_sound_complete`).
- `Silmaril.Formats.Compression.Inflate.Task.raw_complete`: the same for the raw-DEFLATE
  machine (`Inflate.raw .v131`) against `Deflate.decoder`. Conditional:
  `Inflate.deflate_local_of_task`, which proves `Deflate.Task.local`.

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
