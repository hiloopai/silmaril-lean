# Brotli static dictionary address and base word

`StaticDictionary.splitAddress` takes the base length and the word ID from
a checked distance target. The existing distance law already identifies
the word ID as `distance - (maxBackward + 1)`. This slice checks lengths
4–24 and IDs below `121 * NWORDS[length]`, then divides the ID into the
base-word index and the transform ordinal. The quotient agrees with RFC
7932 §8's right shift by the per-length depth. The pair reconstructs the
original ID exactly.

`StaticDictionary.lookup` checks the length and base index and returns
the exact untransformed byte slice at `DOFFSET[length] + index * length`.
Bucket starts derive from RFC §8's recurrence using the established
`NDBITS` data. The byte slice fits its bucket and has exactly the base
length. Invalid lengths, IDs and indices have distinct typed errors.
Transforms and output expansion are a separate layer. The existing
decoder entry points retain their typed static dictionary refusal.

The machine-checked contracts are under
`Silmaril.Formats.Compression.Brotli.StaticDictionary`.

- `splitAddress_iff`, `splitAddress_sound` and `splitAddress_roundtrip`
  characterize exactly the accepted IDs, their two fields, and the inverse
  reconstruction.
- `canonical_size`, `bucketOffset_succ`, `dictionary_extent` and
  `wordExtent` establish the layout and the enclosing byte bounds.
- `lookup_iff`, `lookup_size` and `lookup_byte` bind each admitted word to
  the canonical bytes and exact length. `resolved_lookup` composes the
  existing distance witness with successful address and base-word lookup.

## Canonical data and independent replay

The bundled `data/brotli-static-dictionary/dictionary.bin` is copied byte for
byte from libbrotli v1.2.0 revision
`028fb5a23661f123017c060daa546b55cf4bde29`. The adjacent LICENSE preserves
the upstream MIT notice. The canonical byte length is 122,784 and the
RFC CRC-32 is `5136cb04`. The SHA-256 is
`20e42eb1b511c21806d4d227d07e5dd06877d8ce7b3a817f378f313653f35c70`.

The comparator independently extracts Appendix A from the pinned RFC
Editor text, checks its checksum, and compares the compiled pinned
libbrotli dictionary bytes, depths and offsets. It compares the embedded
Lean bytes and the concatenation of all 13,504 checked Lean word lookups
with the same reference. Boundary controls cover every bucket, the first
and last transform ordinals, quotient transitions and typed rejects.
Lean uses the bundled bytes through `include_bytes`. The independent
comparison checks provenance and the built bytes outside the kernel.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.StaticDictionary.Tests
python3 -B -I -u scripts/brotli-static-dictionary/check.py
```

The replay accepts an exact libbrotli checkout via `--brotli-source` and a
local copy of the pinned RFC text via `--rfc`.
[RFC 7932 §8](https://www.rfc-editor.org/rfc/rfc7932#section-8)
· [Appendix A](https://www.rfc-editor.org/rfc/rfc7932#appendix-A)
· [Pinned libbrotli bytes](https://github.com/google/brotli/blob/028fb5a23661f123017c060daa546b55cf4bde29/c/common/dictionary.bin)
