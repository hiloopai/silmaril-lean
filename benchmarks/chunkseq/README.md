# Canonical binary sequences

`Silmaril.Prelude.ChunkSeq.Balanced.Thms` provides `Seq` (one element per node)
and `Chunked` (one full array per node and one partial tail). `Chunked`'s width
parameter is one less than the actual chunk size. For `Side.left`, `insert`
appends; for `Side.right` it prepends, with the physical tree storing reversed
order. Only the chunk at the insertion end can be partial.
The direction is part of the type; a left-packed value cannot be accidentally
used as a right-packed value without an explicit conversion.

In storage order a perfect tree becomes the next left child; otherwise `push`
descends the right spine. As a result, every nonempty tree has a perfect left
child and a right subtree no bigger than the left. `Canonical` is the exact
normal form under `ofList`, not arbitrary locally balanced shape. It excludes
extra shapes, invalid caches, non-full interior chunks, and oversized tails.
For both directions the API proves `toList_ofList`, `ofList_toList`,
`toList_insert`, and `get?_eq`. The orientation proof does not run during lookup.
This is a standalone representation; it does not change the JSON parser yet.

## Reproduce

```sh
lake build --wfail Silmaril.Prelude.ChunkSeq.Balanced.Tests
python3 scripts/bench/chunkseq-kernel.py > /tmp/chunkseq-kernel.csv
python3 scripts/bench/chunkseq-kernel.py --sizes 100000 --widths 32
lake env lean -c /tmp/ChunkSeqNative.c benchmarks/chunkseq/Native.lean
lake env leanc -O3 -o /tmp/chunkseq-native /tmp/ChunkSeqNative.c \
  .lake/build/ir/Silmaril/Prelude/ChunkSeq/Balanced/{Defs,Thms}.c \
  .lake/build/ir/Silmaril/Proofs/Prelude/ChunkSeq/Balanced.c
for count in 1000 10000 100000 1000000; do
  for variant in node chunk1 chunk32; do
    /usr/bin/time -f '%e s wall, %M KiB peak RSS' /tmp/chunkseq-native "$variant" "$count"
  done
done
```

Kernel probes report a `decide +kernel`-style declaration check separate from
process startup and literal elaboration. The materialized probes use generated
Lean source (not expression emission) and query the raw constructors; they do
not certify that the generator produced the canonical shape. The storage API's
lookup/canonicality theorems do not depend on the generator. `.olean` size here
is an artifact-size proxy, including the harness, not heap size.

## Results

Lean nightly 2026-11-05, Linux x86-64. Native medians of three runs at one
million items; list construction is outside the timed build phase:

| Storage | Build | 1,000 inserts | 100,000 lookups | Process RSS |
| --- | ---: | ---: | ---: | ---: |
| One element per node | 86.1 ms | 0.112 ms | 22.5 ms | 62 MiB |
| Chunk size 1 | 108.9 ms | 0.135 ms | 40.4 ms | 94 MiB |
| Chunk size 32 | 11.0 ms | 0.033 ms | 10.6 ms | 34 MiB |

Do not implement the unchunked variant as chunk size 1 on this evidence.
Size 32 is useful for native construction and selective queries in precomputed
trees; it is not a faster general-purpose kernel builder. At 10,000 items,
kernel build + late lookup took 8.33 s (node); both chunk variants hit the
configured recursion limit. Materialized late lookup and append + lookup took
1.1/1.6 ms (node), 2.2/2.6 ms (chunk 1), and 2.3/3.3 ms (chunk 32), excluding
literal processing. The 10,000-item `.olean` sizes were 20.2, 35.7, and 12.1
MiB. At 100,000 items the chunk-32 source literal overflowed the Lean stack
before a lookup could run. These are bounded source-elaboration measurements,
not limits on a dedicated term emitter or on the runtime representation.
