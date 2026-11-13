# Kernel bytes benchmarks

`run.sh` times the operations of `Silmaril.KBytes` (`Silmaril/Prelude/Bytes`) on pseudo-random
data of a given size. It generates the data inside Lean, so no binaries are committed.

```
benchmarks/kernel-bytes/run.sh 1048576:native 4194304:native 16777216
```

Each line is `size <TAB> step <TAB> milliseconds`. A kernel step adds one theorem
`e = true := Eq.refl true` and times `addDecl`, with asynchronous elaboration off, so the
time is the kernel's. A native step times `Lean.Meta.nativeEqTrue`, the primitive
`edge_decide` uses: it compiles the term, runs it and adds the axiom. Native steps need
computable data (`kbytes_def … computable`).

## Results

Measured on 2026-11-13 on a 2-vCPU sandbox with Lean `nightly-2026-11-05`, one run each (no
repetitions, so expect noise of roughly ±20 %). Times are in ms. "Tree" is the canonical
`KBytes` (left-balanced, 4 KiB packed leaves, cached lengths). "Flat" is a list of 4 KiB
literals read by walking the list (`List.getD`, as `BinaryImage.byte` does). "One leaf" is the
whole file as one `Nat` (`KBytes.leaf n v`), read by the same `read`.

| step | 1 MiB | 4 MiB | 16 MiB |
|---|---:|---:|---:|
| encode 4 KiB chunks (interpreted meta code) | 525 | 2,105 | 8,455 |
| `kbytes_def`, noncomputable (defs, kernel-checked `eq_ofChunks`, `wf`) | 123 | 601 | 2,904 |
| `kbytes_def`, computable | 182 | 927 | not run |
| kernel: 100 random 1-byte reads, tree | 25 | 40 | 54 |
| kernel: 100 random 1-byte reads, flat chunk list | 272 | 1,391 | 6,072 |
| kernel: 100 random 1-byte reads, one leaf | 97 | 317 | 974 |
| kernel: 1000 random 8-byte reads, tree | 319 | 401 | 530 |
| kernel: 100 random 4096-byte reads, tree | 33 | 63 | 55 |
| kernel: `rfl` between two canonical trees of the same bytes | 0.7 | 2.1 | 9.4 |
| kernel: `beq` (structural) | 15 | 67 | 292 |
| kernel: `sameBytes 65536` | 30 | 149 | 661 |
| kernel: `sameBytes 4096` | 81 | 582 | 2,881 |
| kernel: `sameBytes 65536`, rope (slice+append at an unaligned cut) vs tree | 79 | 514 | 1,772 |
| kernel: `beq (canon 4096 rope)` vs tree | 165 | 906 | 4,434 |
| kernel: whole-value read `read 0 n` of two trees, compared | 37 | 210 | 568 |
| kernel: 8-byte read inside a 16 MiB zero leaf | 0.3 | 0.4 | 0.3 |
| native: `sameBytes 65536`, rope vs tree | 7 | 23 | not run |
| native: `eqByteArray t t.toByteArray` | 959 | 4,031 | not run |

The raw output is in the pull request that added this directory.

## What the numbers say

* **Random access needs the tree.** Per read, the tree costs 0.25 to 0.55 ms from 1 to
  16 MiB, growing with depth. The flat chunk list grows linearly (61 ms per read at 16 MiB),
  because the kernel walks the list. One whole-file `Nat` grows too (10 ms per read at
  16 MiB), because each shift copies the big number.
* **Wide reads cost the same as byte reads.** A 4 KiB read costs about what a 1-byte read
  does, so names, records and table windows should be read as one `read`/`readLE`.
* **Equality of canonical trees is `rfl`.** 9 ms at 16 MiB: the kernel compares the shared
  literals and does no arithmetic. The elaborator always writes canonical trees, so equal
  files are `rfl`-equal.
* **Ropes need work in proportion to their size.** A slice or append is one node. Comparing a
  rope with a canonical tree by 64 KiB windows costs about 110 ms per MiB in the kernel, about
  2.5 times less than canonicalising first. Natively it costs about 6 ms per MiB.
* **Zero runs are free.** A run of zero bytes is one leaf `leaf n 0`, whatever `n` is. Power-
  of-two constant subtrees are not needed in this representation.
* **Building is dominated by encoding.** The interpreter's chunk encoding takes 0.5 s per MiB.
  The kernel check of `eq_ofChunks` takes about 0.18 s per MiB.
* **`bytes.eqByteArray` is slow natively** (about 1 s per MiB), because it builds both byte
  lists. It is only the fallback for raw terms that are not chunk literals. The structural
  bridge (`kbytes_rel`, `kbytes_def … of_include`) needs no evaluation.

## Not adopted, and why

* **Shared named definitions per page.** A prototype gave each 4 KiB leaf its own constant.
  It made `rfl` against an unnamed tree slower (38 ms against 7 ms at 16 MiB, prototype
  numbers), because the kernel unfolds each constant. It gave no speed-up on reads or `beq`.
  The `.olean` already shares identical literals.
* **1 KiB leaves.** Not benchmarked here. `Silmaril.Data.IncludeBytes` measured them at 22 %
  `.olean` overhead against 5 % for 4 KiB; reads would gain at most two tree levels.
* **Power-of-two constant subtrees.** Not built: zero runs are one leaf already, and a
  constant non-zero run is a single literal `b * (256^n - 1) / 255`.
