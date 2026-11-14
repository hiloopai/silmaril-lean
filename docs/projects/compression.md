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
| [Deflate](../../Silmaril/Formats/Compression/Deflate/Thms.lean) | `Deflate.decoder` (`deflateTake`): stored, fixed and dynamic Huffman blocks | consumes, append law, stored round trip, compressing round trip (`roundTripFixed`: greedy LZ77, one fixed-Huffman block), output bound `output_le`, zlib-produced vectors for each block type, two rejections |
| [Zlib](../../Silmaril/Formats/Compression/Zlib/Thms.lean) | `Zlib.decoder = framing.wrap Deflate.decoder` | consumes, append law, Adler-32 trailer, stored and compressing (`encoderFixed`) round trips, output bound, CPython vectors, dictionaries |
| [Gzip](../../Silmaril/Formats/Compression/Gzip/Thms.lean) | `Gzip.decoder = framing.wrap Deflate.decoder`; files are `decoder.members` | consumes, append law, CRC-32/ISIZE trailer, stored and compressing (`encoderFixed`) round trips, output bounds for members and whole files, multi-member files, GNU and CPython vectors |
| [Checksum](../../Silmaril/Formats/Compression/Checksum/Thms.lean) | `Checksum.adler32`, `Checksum.crc32` | published check values; CRC-32 equals `crc32Spec`, the GF(2) polynomial definition of ISO 3309 / ITU-T V.42 (`crc32_eq_spec`, over the polynomial model `GF2Poly`), and detects every single-bit error |
| [Inflate](../../Silmaril/Formats/Compression/Inflate/Thms.lean) | `Inflate.member version kind`, `Inflate.raw version`: zlib 1.3.1's resumable inflater as `Incremental` machines | sound, rejection-sound and complete, schedules agree, each call emits at most its output capacity, packed fixed tables agree with the canonical decoder |

Assumptions and scope:

- The decoders are total list-based specifications, fuel-bounded by the input
  length. The theorems are only as faithful as these definitions; the vectors
  produced by zlib, CPython and GNU gzip check them against independent
  implementations.
- The inflater is a mathematical machine, not a refinement of zlib's C code.
- The append laws (`Deflate.local`, `Zlib.local`, `Gzip.local`) and the
  completeness of the inflater (`Inflate.member_complete`, `Inflate.raw_complete`)
  are proved.
- Resource bounds are intrinsic: a DEFLATE member produces at most 2064 output
  bytes per input byte it consumes (a Huffman token consumes at least one bit
  and emits at most 258 bytes; a stored byte consumes eight bits), so
  `Deflate.output_le`, `Zlib.output_le`, `Gzip.output_le` and, for whole files,
  `Gzip.members_output_le` and the `decompress_output_le` theorems bound the
  output linearly in the input. Operationally, every streaming call appends at
  most its output capacity (`Inflate.raw_call_output`, `Inflate.member_call_output`).
- Encoders: the stored encoders (`encoder`) are linear-time and do not shrink
  data; `encoderFixed` (all three formats) compresses with greedy LZ77 and one
  fixed-Huffman block, whose match search is quadratic in the worst case.

## Open goals

None. The former open goals are kept as `def Task.… : Prop` for compatibility and
are proved:

- `Silmaril.Formats.Compression.Deflate.Task.local`: bytes appended after a DEFLATE
  member never change how it decodes; proved as `Deflate.local` (`Deflate.task_local`),
  hence `Zlib.local` and `Gzip.local`.
- `Silmaril.Formats.Compression.Inflate.Task.member_complete`: zlib 1.3.1's member
  machine (`Inflate.member .v131 .zlib`) finishes every member `Zlib.decoder` accepts,
  when the whole input is given at the start; proved as `Inflate.task_member_complete`
  (`Inflate.member_complete`, `zlib_complete` and `gzip_complete` cover both versions
  and both containers).
- `Silmaril.Formats.Compression.Inflate.Task.raw_complete`: the same for the raw-DEFLATE
  machine (`Inflate.raw .v131`) against `Deflate.decoder`; proved as
  `Inflate.task_raw_complete` (`Inflate.raw_complete` for both versions).

## Requirement-by-requirement evidence

[deflate-zlib-gzip.md](deflate-zlib-gzip.md) lists, for RFC 1951, RFC 1950 and RFC 1952, each
requirement with its theorem, check or documented policy, and the contract erebor-lean relies on.

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
