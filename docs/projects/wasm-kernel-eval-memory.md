# Memory representations for kernel evaluation

This note follows [wasm-kernel-eval.md](wasm-kernel-eval.md). It compares how Wasm linear memory
can be represented when Lean's kernel evaluates code. It measures the kernel and native
execution separately, and proves that each representation computes the same loads and
stores as the reference memory.

**Code:**

| Module | Contents |
| --- | --- |
| `Silmaril.Wasm.KernelEval.Memories` | `Overlay`, `PageMem`, byte views, `MemSimOn` (definitions) |
| `Silmaril.Wasm.KernelEval.MemThms` | Statements for `Memories`; proofs in `Silmaril.Proofs.Wasm.KernelEval.Memories` |
| `Silmaril.Wasm.KernelEval.CoreMem` | Core's `ByteArray` memory, accessed two ways |
| `Silmaril.Wasm.KernelEval.CoreMemThms` | Statements for `CoreMem`; proofs in `Silmaril.Proofs.Wasm.KernelEval.CoreMem` |
| `Silmaril.Wasm.KernelEval.KBytesMem` | `Silmaril.KBytes` as Wasm memory, two ways |
| `Silmaril.Wasm.KernelEval.KBytesMemThms` | Statements for `KBytesMem`; proofs in `Silmaril.Proofs.Wasm.KernelEval.KBytesMem` |
| `Silmaril.Wasm.KernelEval.MemTests` | Kernel tests |

**Benchmarks:**

- `benchmarks/wasm-kernel-eval/mem_bench.py`: kernel benchmarks.
- `benchmarks/wasm-kernel-eval/NativeBench.lean`: native benchmarks, built as the
  `kernel-eval-bench` executable.
- Results: [docs/benchmarks/wasm-kernel-eval-memory-2026-11-13.json](../benchmarks/wasm-kernel-eval-memory-2026-11-13.json).

```sh
lake build --wfail Silmaril.Wasm.KernelEval.MemTests
lake build kernel-eval-bench && .lake/build/bin/kernel-eval-bench          # native, seconds
python3 -I benchmarks/wasm-kernel-eval/mem_bench.py -o out.json           # kernel, about 1.5 h
```

**`KBytes`.** `Silmaril.KBytes` is the shared kernel byte string of the core work
(`Silmaril/Prelude/Bytes`, Init-only). This branch merges it from `prelude/kernel-bytes-trust`
(#125) at `792e7ed6` (the frozen interface; its `Defs`/`Thms` are unchanged since `28418c29`). It is a length-cached binary tree of
packed 4 KiB leaves with `read`, `readLE`, `get?`, `slice`, `++` and `canon`. Its interface
has no write, so it is measured two ways:

- `KRope` uses the interface only;
- `KPath` adds a path-copying write, `kwrite`. `kwrite` is defined and proved in this topic,
  not in `KBytes`, whose interface is frozen.

The other baselines are the memory paths that the existing evaluators use, named by their
exact declarations.

## Representations

| Name | What it is | Load | Store | Shares with other memories | Validity condition |
| --- | --- | --- | --- | --- | --- |
| `CoreMem` | Core's `Memory.Bytes` (`ByteArray`) with `Memory.load`/`Memory.store` (`extract`, `copySlice`), the functions Core 3.0 execution and `runInvoke?` use | `extract`, then decode | `copySlice` into the array | No; a store copies or mutates the array | None |
| `KMem` | The same `ByteArray`, with `Silmaril.Wasm.Verify.Kernel`'s `fload`/`fstore` (the bytes as a `List.rec` list), as used by `runInvokeK`. The zero memory is `⟨⟨List.replicate n 0⟩⟩`, lazy as in `Auto2.Kernel` | `dropX`/`takeX`, then decode | `writeL` splice | The list suffix after the write | None |
| `ListMem` | A list of `BitVec 8` (the prototype's reference) | `drop`/`take`, then decode | `take ++ encode ++ drop` | The list suffix | None |
| `NatMem` | All bytes packed into one natural number | `>>>`, `%` (GMP) | `-`, `+`, `<<<` (GMP), which rebuilds the whole number | None | None |
| `Overlay` | An immutable packed base plus a log of byte writes, newest first | Search the log for each byte, then the base | Prepend `k` entries | The whole base, and older logs | None |
| `KRope` | `Silmaril.KBytes` (zero memory `kzeros`: the canonical tree of 4 KiB zero leaves) | `readLE` | The rope `slice 0 a ++ leaf k v ++ slice (a+k) rest` (interface only) | Untouched subtrees, but each store adds nodes, so depth grows | `wf` (cached lengths) |
| `KPath` | `Silmaril.KBytes` with the path-copying write `kwrite` | `readLE` | Rewrite the leaves the window falls in, digit by digit (`%`, `/`, `*`, `+`), and copy their paths; the shape is unchanged | Every untouched subtree | `wf` |
| `PageMem` | A persistent complete binary tree of packed pages of `2^pbits` bytes | Walk one path, then shift within the page; byte by byte across a page boundary | Copy one path and rebuild one page | Every untouched subtree; a zero tree is one shared leaf per level | `PageMem.Wf`: the tree is complete and each page is below `256^pageSize` |

## What is proved

All declarations use only `propext`, `Classical.choice` and `Quot.sound`. None uses
`sorry`, axioms or `native_decide`.

- **Runs under a validity condition.**
  - `MemSimOn inv g`: loads and stores commute with `g` on memories satisfying `inv`, and
    stores preserve `inv`.
  - `run_mapMem_on`, `returns_mapMem_on`: such a simulation lifts to whole runs of the
    subset machine.
  - `memSimOn_of_memSim` covers the case without a condition.
- **Byte views.** `memSimOn_ofView` reduces a simulation to the list reference to
  pointwise facts:
  - a load decodes `byte a … byte (a+k-1)`;
  - an in-bounds store changes exactly bytes `a … a+k-1`, to the little-endian bytes of the
    value, and keeps the size and `inv`;
  - an out-of-bounds store fails.

  This is the adapter boundary for future representations.
- **Overlays and page trees.**
  - `memSimOn_overlay` (no condition) and `memSimOn_pageMem` (`PageMem.Wf`, true of
    `PageMem.zeros` by `wf_zeros`).
  - `overlay_zeros_toList` and `pageMem_zeros_toList` give their zero memories.
  - The page proofs reuse `write_toNatMem` for the in-page arithmetic.
- **`KBytes`.**
  - `memSimOn_kRope` and `memSimOn_kPath`: both simulate the list reference under
    `kToListMem`, given `wf`. They are proved from the `KBytes` interface theorems
    (`readLE_eq`, `toList_slice`, `toList_append`, `wf_slice`, `wf_append`).
  - `kwrite_spec`: the path-copying write keeps `wf` and splices the written bytes in, with
    no condition on leaf digits.
  - `wf_kzeros` and `kzeros_toListMem` give the zero memory, from `toList_ofChunks`.
- **Core's memory.**
  - `memSim_coreMem`, `memSim_kMem`: Core's `Memory.load`/`Memory.store` and the kernel
    evaluator's `fload`/`fstore` both simulate the same list reference under
    `toListMem : Memory.Bytes → ListMem`.
  - `kmem_load_eq`, `kmem_store_eq`: the two access paths are equal. They are derived from
    `Verify.Kernel`'s `fload_eq`/`fstore_eq`.

  So every representation here computes, byte for byte, the loads and stores of Core's
  memory functions on the corresponding `ByteArray`.
- **Tests (`MemTests`).**
  - `fillSort8_returns_pages` evaluates on a page tree and transports the result to the
    reference run on a 64 KiB list memory.
  - A cross-page word store with 4-byte pages.
  - The same program on `Overlay` and on `KMem`.
  - `fillSort8_returns_kbytes` evaluates on `KBytes` (`KPath`) and transports the result to
    the reference run.
  - A word store across a 4 KiB `KBytes` leaf boundary, for both `KRope` and `KPath`.

**Not proved:**

- that the subset machine agrees with Core's `Step` (as in the first note);
- that `runInvokeK` can run on these representations. Core's `Store` fixes the memory type
  to `ByteArray`, so using `PageMem` inside `runInvokeK` needs a store whose memory type is
  a parameter, plus this simulation;
- the native `ByteMem` in the benchmarks: it copies the algorithm of `Memory.load`/`store`
  but is not the library declaration.

## Workloads

| Workload | What it does | Size |
| --- | --- | --- |
| `fillSort n` | Insertion sort of `n…1` in memory (first note) | `fillSort 16`: 3,734 steps, 151 stores |
| `scatter 128` | 128 word stores spread evenly over the memory (stride `size/128 − 4`), then 128 loads of them, summed | 4,370 steps |
| `updates 200` | 200 word stores, stride `size/200 − 4`, then one load | Called directly, not through the machine |
| `sharing 64` | Fill 64 words. Make 64 variants of that base, each with one word written, and keep them all. Check each variant's own word, and the base's word at a probe address | Called directly |

Memory sizes are 256 B, 64 KiB (one Wasm page) and 1 MiB (16 pages).

## Kernel results

| Workload | Size | `CoreMem` | `ListMem` | `KMem` | `NatMem` | `Overlay` | `PageMem` | `KBytes` rope (`KRope`) | `KBytes` path (`KPath`) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fillSort 8 | 256 B | 207.00 s (25.3 GB) | 349 ms (2.2 GB) | 436 ms (2.2 GB) | 186 ms (2.2 GB) | 384 ms (2.2 GB) | 193 ms (2.2 GB) | 234 ms (2.2 GB) | 203 ms (2.2 GB) |
| fillSort 16 | 64 KiB | — | 6.99 s (3.4 GB) | 1.55 s (2.4 GB) | 739 ms (2.3 GB) | 2.13 s (2.6 GB) | 846 ms (2.4 GB) | 1.62 s (2.4 GB) | 848 ms (2.4 GB) |
| scatter 128 | 64 KiB | — | timeout after 280 s, 33 GB | timeout after 204 s, 29 GB | 1.04 s (2.4 GB) | 6.67 s (3.5 GB) | 1.04 s (2.4 GB) | 3.88 s (2.9 GB) | 1.07 s (2.4 GB) |
| scatter 128 | 1 MiB | — | timeout after 202 s, 30 GB | timeout after 233 s, 28 GB | 1.57 s (2.8 GB) | 6.47 s (3.5 GB) | 1.30 s (2.4 GB) | 5.92 s (3.2 GB) | 1.32 s (2.4 GB) |
| updates 200 | 64 KiB | — | timeout after 279 s, 33 GB | timeout after 224 s, 29 GB | 97 ms (2.1 GB) | 15 ms (2.1 GB) | 38 ms (2.1 GB) | 91 ms (2.1 GB) | 37 ms (2.1 GB) |
| updates 200 | 1 MiB | — | timeout after 241 s, 29 GB | timeout after 216 s, 27 GB | 785 ms (2.7 GB) | 14 ms (2.1 GB) | 39 ms (2.1 GB) | 285 ms (2.2 GB) | 138 ms (2.1 GB) |
| sharing 64 | 64 KiB | — | timeout after 262 s, 35 GB | 205.00 s (27.1 GB) | 52 ms (2.1 GB) | 309 ms (2.1 GB) | 77 ms (2.1 GB) | 260 ms (2.2 GB) | 72 ms (2.1 GB) |
| sharing 64 | 1 MiB | — | timeout after 234 s, 30 GB | timeout after 239 s, 29 GB | 219 ms (2.3 GB) | 321 ms (2.1 GB) | 104 ms (2.1 GB) | 472 ms (2.2 GB) | 203 ms (2.2 GB) |

`NatMem`, `Overlay`, `PageMem` and both `KBytes` columns come from one later session. `CoreMem`, `ListMem` and `KMem` come from the first session, whose kernel times for the shared columns read up to about 1.3× higher. The imports-only baseline is 2.1 GB peak RSS. At 256 B, `PageMem` uses 256 B pages. "Timeout" is Lean's kernel deterministic timeout at the default `maxHeartbeats`.

## Native results

| Workload | Size | `ListMem` | `ByteArray` (Core algorithm) | `NatMem` | `Overlay` | `PageMem` 4 KiB | `KRope` | `KPath` |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| fillSort 16 | 64 KiB | 32.7 ms | 313 µs | 452 µs | 410 µs | 638 µs | 2.0 ms | 513 µs |
| fillSort 32 | 64 KiB | 133 ms | 1.2 ms | 1.7 ms | 1.9 ms | 2.4 ms | 8.4 ms | 2.2 ms |
| scatter 128 | 64 KiB | 123 ms | 302 µs | 10.7 ms | 787 µs | 970 µs | 3.7 ms | 845 µs |
| scatter 128 | 1 MiB | — | 462 µs | 279 ms | 718 µs | 834 µs | 24.3 ms | 689 µs |
| updates 200 | 64 KiB | 157 ms | 368 µs | 7.5 ms | 94 µs | 794 µs | 7.1 ms | 9.7 ms |
| updates 200 | 1 MiB | — | 7.1 ms | 162 ms | 549 µs | 577 µs | 41.9 ms | 520 µs |
| sharing 64 | 64 KiB | 80.7 ms | 461 µs | 4.4 ms | 276 µs | 392 µs | 2.2 ms | 290 µs |
| sharing 64 | 1 MiB | — | 5.0 ms | 53.2 ms | 207 µs | 485 µs | 21.5 ms | 345 µs |

Times are the mean of 5–20 repetitions (ListMem: 1–2) in one compiled process.

## The store through the published interface

The `KBytes` interface is frozen without a write primitive (#125 at `792e7ed6`). The core
work's proposed store is the rope `slice t 0 off ++ leaf w v ++ slice t (off + w) (len - off - w)`
on a zero memory `leaf n 0`.

- **This is `KRope` on `kzero1`.** A store checks `off + w ≤ len`; an out-of-range store
  fails, which is a Wasm trap (tested). The value is taken modulo `256 ^ w`.
- **Semantics.** `memSimOn_kRope` proves it equal to the list reference, from
  `toList_slice`, `toList_append` and `readLE_eq`. `kzero1_toListMem` proves the zero
  memory, and `fillSort8_returns_rope_leaf` checks a whole run end to end.
- **Comparison.** The table compares it with the canonical 4 KiB-leaf zero and with this
  topic's path-copying write `kwrite` on both zeros. All numbers are measured, not assumed.

**Kernel (`decide +kernel`):**

| Store, zero memory | fillSort 16 64 KiB | scatter 128 64 KiB | scatter 128 1 MiB | updates 200 64 KiB | updates 200 1 MiB | sharing 64 64 KiB | sharing 64 1 MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Rope stores, `leaf n 0` zero (`KRope`, `kzero1`) | 1.11 s | 3.73 s | 3.56 s | 48 ms | 46 ms | 205 ms | 238 ms |
| Rope stores, 4 KiB-leaf zero (`KRope`, `kzeros`) | 1.62 s | 3.88 s | 5.92 s | 91 ms | 285 ms | 260 ms | 472 ms |
| Path stores, 4 KiB-leaf zero (`KPath`, `kzeros`) | 848 ms | 1.07 s | 1.32 s | 37 ms | 138 ms | 72 ms | 203 ms |
| Path stores, `leaf n 0` zero (`KPath`, `kzero1`) | 739 ms | 1.11 s | 1.58 s | 682 ms | 15.60 s | 64 ms | 283 ms |

**Native (compiled):**

| Store, zero memory | fillSort 16 64 KiB | scatter 128 64 KiB | scatter 128 1 MiB | updates 200 64 KiB | updates 200 1 MiB | sharing 64 64 KiB | sharing 64 1 MiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Rope stores, `leaf n 0` zero (`KRope`, `kzero1`) | 1.6 ms | 4.2 ms | 19.0 ms | 6.5 ms | 30.3 ms | 1.7 ms | 16.5 ms |
| Rope stores, 4 KiB-leaf zero (`KRope`, `kzeros`) | 2.0 ms | 3.9 ms | 23.4 ms | 7.0 ms | 41.2 ms | 2.1 ms | 20.9 ms |
| Path stores, 4 KiB-leaf zero (`KPath`, `kzeros`) | 513 µs | 994 µs | 691 µs | 9.6 ms | 518 µs | 297 µs | 352 µs |
| Path stores, `leaf n 0` zero (`KPath`, `kzero1`) | 509 µs | 11.1 ms | 186 ms | 546 ms | 14.2 s | 2.5 ms | 50.3 ms |

**What the measurements show:**

- **Rope stores on `leaf n 0` work at every size without a timeout.**
  - Writes and sharing are cheap and do not depend on size: `updates` 46–49 ms, `sharing`
    205–238 ms in the kernel. Each store adds a few nodes and copies nothing.
  - Read-heavy loops pay for the depth the ropes accumulate: `scatter` takes 3.6–3.7 s
    against 1.1–1.3 s for path stores on 4 KiB leaves.
  - In the kernel the one-leaf zero is as fast as or faster than the 4 KiB-leaf zero under
    rope stores on every workload here, since slicing a single leaf is one shift.
- **Path stores need the 4 KiB leaves.** On `leaf n 0` the path-copying write rewrites the
  whole memory's number on every store: `updates` at 1 MiB takes 15.6 s in the kernel and
  14 s natively.
- **Choosing.**
  - Rope stores through the frozen interface suit the default.
  - For read-heavy loops after many stores, the measured options are a path write on 4 KiB
    leaves (`kwrite`, kept local to this topic) or `canon 4096` every few hundred stores.
    The `canon` option has not been measured here.

## Reading the numbers

- **The `ByteArray` paths do not scale in the kernel.**
  - `CoreMem` (`extract`/`copySlice`) needs 207 s and 25 GB for 8-element sort on a
    256-byte memory, where `NatMem` takes 0.23 s.
  - `KMem` (the `Verify.Kernel` path) is usable while accesses stay near the start of a
    lazily zero memory: 1.55 s for `fillSort 16` in 64 KiB.
  - Once accesses spread across 64 KiB, `KMem` and `ListMem` both exceed the default kernel
    budget at 28–35 GB, because each access walks the list to its address.
  - The asymptotic problem is the representation, not the evaluator.
- **`NatMem` is the fastest single memory to read, but every write rebuilds the whole
  number.** Its kernel cost grows with memory size when writes dominate: `updates 200` takes
  97 ms at 64 KiB and 785 ms at 1 MiB. Natively it is the slowest representation apart from
  lists and ropes (279 ms for `scatter 128` at 1 MiB): each store allocates a 1 MiB number.
- **`KBytes` with path-copying stores (`KPath`) and `PageMem` are the strongest
  all-round representations here, but they are not at parity.** Both are trees of packed
  4 KiB pages.
  - **Kernel.** Within 15 % of `NatMem` on the dense sort (848 and 846 ms against
    739 ms). At least as fast on scattered access at 1 MiB (1.32 and 1.30 s against
    1.57 s). Much faster on writes at 1 MiB (138 and 39 ms against 785 ms).
  - **Native.** `KPath` is within 3× of the mutable `ByteArray`, except write-dense
    `updates` at 64 KiB (26×; see the write cost below). It is faster than
    `ByteArray` at 1 MiB on `updates` (0.52 against 7.1 ms) and `sharing` (0.35 against
    5.0 ms), where `ByteArray` copies on write.
  - **Differences.** `KPath` uses the shared type and needs only `wf`. Its leaves stay
    canonical-sized, so a fresh memory compares by `canon`/`rfl` like any other `KBytes`.
    `PageMem` needs a power-of-two page count and `PageMem.Wf`.
  - **Write cost.** A `KPath` write costs more where many writes fall in one leaf
    (`updates` at 64 KiB natively: 9.7 ms against 0.79 ms for `PageMem`), because each one
    rewrites a 4 KiB number digit by digit.
  - **Where `PageMem` is ahead.** Kernel `updates` at 1 MiB take 39 ms against 138 ms, and
    kernel `sharing` at 1 MiB 104 ms against 203 ms.
  - **Caveat.** These rows come from one run per case, across sessions (see the kernel
    table). Both remain benchmark baselines.
- **`KBytes` through its published interface (`KRope`) works, at 2–5× the cost of
  `KPath`.**
  - Every store adds slice nodes, so reads descend deeper over time: `scatter` takes
    3.9–5.9 s in the kernel and 24 ms natively at 1 MiB.
  - Periodic `canon` would restore the shape, but that is a full rebuild.
  - The path-copying write `kwrite` on 4 KiB leaves, local to this topic, is the cheaper fix.
- **`Overlay` is the cheapest to update, and the worst to read after many writes.**
  - Kernel `updates` take 14–15 ms, independent of size.
  - Each load scans the log byte by byte, so read-heavy loops with hundreds of earlier
    stores are 2.5–6.5× slower than `PageMem`/`KPath`.
  - Natively it is among the fastest for `updates` and `sharing`.
  - It needs no validity condition. It fits one immutable image (a data segment or
    snapshot, which could itself be a `KBytes` literal) with a few writes per variant, or a
    log compacted every few hundred writes.
- **Sharing many slightly different memories.**
  - 64 live variants of a 1 MiB memory cost the kernel 104 ms (`PageMem`), 203 ms
    (`KPath`), 219 ms (`NatMem`), 321 ms (`Overlay`) and 472 ms (`KRope`).
  - Natively: 0.49, 0.35, 53, 0.21 and 21 ms, against 5.0 ms for the copying `ByteArray`.
  - Kernel evaluation is lazy (a variant is computed only as far as a load reads it), which
    is why `NatMem`'s kernel number is low compared with its native one.
- **Kernel laziness affects the write-heavy rows.** In `updates`, a write that no later
  load reads costs little, except for `NatMem`, whose single number has to be computed in
  full. The native rows have no such effect.

**Status and recommendation.**

- **`KBytes` as the shared memory type.** `memSimOn_kRope`/`memSimOn_kPath` and
  `memSim_coreMem` tie its stores to Core's `Memory.load`/`Memory.store`. Memories, files
  and data segments then share one type and one equality check (`canon`, `sameBytes`).
- **Through the frozen interface.** The store is the rope through `slice`/`++`, on a
  `leaf n 0` zero memory (`KRope`, `kzero1`). It is proved, did not time out on any
  workload here, and its write and sharing costs do not grow with memory size. It is not
  the cheapest on any of them: `Overlay` has cheaper writes and `PageMem` cheaper sharing.
- **Path-copying write.** `kwrite` with `kwrite_spec` stays in this topic for review. Moving
  it into `KBytes` is a possible later, small change, after compatibility with the latest
  core and CI.
- **Baselines.** `PageMem` stays as a benchmark baseline beside `KPath`, since the
  measurements do not show parity.
- **Not in this slice.** Using any of these inside `runInvokeK` needs Core's `Store` to take
  the memory type as a parameter. That refactor is not part of this change.

## Limitations

- **Sizes and runs.** At most 1 MiB, and one run per case on a 2-vCPU sandbox, across two
  sessions (see the kernel table). Kernel times under the Mathlib-closure imports read about
  1.5–2× slower than the same cases in the first note, which imported only core Lean.
- **`KBytes` is not on `main`.** This branch merges #125 at
  `792e7ed6`, so it lands after #125.
- **RSS includes imports.** Peak memory includes about 2.2 GB of imported `.olean` files
  (the baseline row).
- **Coverage.** `Overlay`, `PageMem`, `KRope` and `KPath` cover only the subset's accesses: 1- and 4-byte loads
  and stores. They have no `memory.grow`, `memory.copy`/`fill` or multiple memories.
  Growing a `PageMem` means adding a level (doubling) or keeping a page count beside the
  tree.
- **Overlay logs are not compacted.** A real implementation would flush the log into a new
  base every few hundred writes, or key it by page.
- **Native timings** come from a compiled executable for the core-only representations.
  `KMem` is `noncomputable` (kernel only). `CoreMem`'s closure imports Mathlib, so its
  algorithm is timed through the `ByteMem` copy.
