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
| `Silmaril.Wasm.KernelEval.MemTests` | Kernel tests |

**Benchmarks:**

- `benchmarks/wasm-kernel-eval/mem_bench.py`: kernel benchmarks.
- `benchmarks/wasm-kernel-eval/NativeBench.lean`: native benchmarks, built as the
  `kernel-eval-bench` executable.
- Results: [docs/benchmarks/wasm-kernel-eval-memory-2026-11-13.json](../benchmarks/wasm-kernel-eval-memory-2026-11-13.json).

```sh
lake build --wfail Silmaril.Wasm.KernelEval.MemTests
lake build kernel-eval-bench && .lake/build/bin/kernel-eval-bench          # native, seconds
python3 -I benchmarks/wasm-kernel-eval/mem_bench.py -o out.json           # kernel, about 1 h
```

**No `KBytes` comparison yet.** There is no type or interface named `KBytes` in the
repository or on its branches. The baselines below are the memory paths that the existing
evaluators actually use, named by their exact declarations. A new kernel-byte type from the
core work can be compared by adding one `MemOps` instance and one simulation, as
`CoreMem`/`KMem` do. That comparison is pending until the type exists.

## Representations

| Name | What it is | Load | Store | Shares with other memories | Validity condition |
| --- | --- | --- | --- | --- | --- |
| `CoreMem` | Core's `Memory.Bytes` (`ByteArray`) with `Memory.load`/`Memory.store` (`extract`, `copySlice`), the functions Core 3.0 execution and `runInvoke?` use | `extract`, then decode | `copySlice` into the array | No; a store copies or mutates the array | None |
| `KMem` | The same `ByteArray`, with `Silmaril.Wasm.Verify.Kernel`'s `fload`/`fstore` (the bytes as a `List.rec` list), as used by `runInvokeK`. The zero memory is `⟨⟨List.replicate n 0⟩⟩`, lazy as in `Auto2.Kernel` | `dropX`/`takeX`, then decode | `writeL` splice | The list suffix after the write | None |
| `ListMem` | A list of `BitVec 8` (the prototype's reference) | `drop`/`take`, then decode | `take ++ encode ++ drop` | The list suffix | None |
| `NatMem` | All bytes packed into one natural number | `>>>`, `%` (GMP) | `-`, `+`, `<<<` (GMP), which rebuilds the whole number | None | None |
| `Overlay` | An immutable packed base plus a log of byte writes, newest first | Search the log for each byte, then the base | Prepend `k` entries | The whole base, and older logs | None |
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

| Workload | Size | `CoreMem` | `ListMem` | `KMem` | `NatMem` | `Overlay` | `PageMem` |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| fillSort 8 | 256 B | 207.00 s (25.3 GB) | 349 ms (2.2 GB) | 436 ms (2.2 GB) | 226 ms (2.2 GB) | 475 ms (2.2 GB) | 252 ms (2.2 GB) |
| fillSort 16 | 64 KiB | — | 6.99 s (3.4 GB) | 1.55 s (2.4 GB) | 884 ms (2.3 GB) | 5.00 s (2.6 GB) | 1.09 s (2.4 GB) |
| scatter 128 | 64 KiB | — | timeout after 280 s, 33 GB | timeout after 204 s, 29 GB | 1.40 s (2.4 GB) | 7.52 s (3.5 GB) | 1.26 s (2.4 GB) |
| scatter 128 | 1 MiB | — | timeout after 202 s, 30 GB | timeout after 233 s, 28 GB | 1.97 s (2.8 GB) | 8.41 s (3.5 GB) | 1.37 s (2.4 GB) |
| updates 200 | 64 KiB | — | timeout after 279 s, 33 GB | timeout after 224 s, 29 GB | 137 ms (2.1 GB) | 16 ms (2.1 GB) | 46 ms (2.1 GB) |
| updates 200 | 1 MiB | — | timeout after 241 s, 29 GB | timeout after 216 s, 27 GB | 971 ms (2.7 GB) | 18 ms (2.1 GB) | 48 ms (2.1 GB) |
| sharing 64 | 64 KiB | — | timeout after 262 s, 35 GB | 205.00 s (27.1 GB) | 53 ms (2.1 GB) | 359 ms (2.1 GB) | 82 ms (2.1 GB) |
| sharing 64 | 1 MiB | — | timeout after 234 s, 30 GB | timeout after 239 s, 29 GB | 248 ms (2.3 GB) | 348 ms (2.1 GB) | 118 ms (2.1 GB) |

The imports-only baseline is 2.1 GB peak RSS. At 256 B, `PageMem` uses 256 B pages. "Timeout" is Lean's kernel deterministic timeout at the default `maxHeartbeats`.

## Native results

| Workload | Size | `ListMem` | `ByteArray` (Core algorithm) | `NatMem` | `Overlay` | `PageMem` 4 KiB |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| fillSort 16 | 64 KiB | 35.2 ms | 349 µs | 489 µs | 441 µs | 690 µs |
| fillSort 32 | 64 KiB | 141 ms | 1.3 ms | 1.9 ms | 2.1 ms | 2.7 ms |
| scatter 128 | 64 KiB | 140 ms | 373 µs | 12.2 ms | 872 µs | 1.1 ms |
| scatter 128 | 1 MiB | — | 605 µs | 305 ms | 1.1 ms | 926 µs |
| updates 200 | 64 KiB | 167 ms | 353 µs | 7.9 ms | 97 µs | 829 µs |
| updates 200 | 1 MiB | — | 7.3 ms | 189 ms | 802 µs | 657 µs |
| sharing 64 | 64 KiB | 91.1 ms | 590 µs | 4.6 ms | 278 µs | 430 µs |
| sharing 64 | 1 MiB | — | 5.6 ms | 66.1 ms | 211 µs | 518 µs |

Times are the mean of 5–20 repetitions (ListMem: 1–2) in one compiled process.

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
  137 ms at 64 KiB and 971 ms at 1 MiB. Natively it is the slowest representation apart
  from lists (305 ms for `scatter 128` at 1 MiB): each store allocates a 1 MiB number.
- **`PageMem` (4 KiB pages) is the best all-round representation.**
  - In the kernel it is within about 20 % of `NatMem` on the dense sort and faster on
    scattered and write-heavy workloads.
  - Its costs are flat from 64 KiB to 1 MiB: 1.26 → 1.37 s, 46 → 48 ms and 82 → 118 ms.
  - Natively it is within 3× of the mutable `ByteArray` and faster than it at 1 MiB on
    `updates` and `sharing`, where `ByteArray` copies on write.
  - It needs a validity condition (`PageMem.Wf`). `PageMem.zeros` and every store preserve
    it.
- **`Overlay` is the cheapest to update and to share, and the worst to read after many
  writes.**
  - In the kernel it has the fastest `updates` (16–18 ms), and its sharing cost does not
    depend on size.
  - Each load scans the log byte by byte, so read-heavy loops with hundreds of earlier
    stores are 4–6× slower than `PageMem` (`scatter`, `fillSort`).
  - Natively it is the fastest for `updates` and `sharing`.
  - It needs no validity condition. It fits the case of one immutable image (a data segment
    or snapshot) with a few writes per variant, or a log compacted every few hundred
    writes.
- **Sharing many slightly different memories.**
  - 64 live variants of a 1 MiB memory cost the kernel 118 ms (`PageMem`), 348 ms
    (`Overlay`) and 248 ms (`NatMem`).
  - Natively: 0.5 ms, 0.2 ms and 66 ms, against 5.6 ms for the copying `ByteArray`.
  - The kernel numbers for `NatMem` are lower than its native ones suggest because kernel
    evaluation is lazy: a variant's number is only computed as far as a load reads it.
- **Kernel laziness affects the write-heavy rows.** In `updates`, a write that no later
  load reads costs only its bounds check, except for `NatMem`, whose single number has to be
  computed in full. The native rows have no such effect.

**Recommendation.** For the kernel evaluator (`Verify.Kernel`'s `runInvokeK`), the
representation to adopt is a page tree of packed pages:

- it uses the same 4 KiB `Nat` pages as `IncludeBytes` and ELF's `pages`;
- `Overlay` serves sharing-heavy checks of one image;
- its simulation is `memSimOn_pageMem`, and `memSim_coreMem` ties it to Core's
  `Memory.load`/`Memory.store`.

Moving it into `runInvokeK` itself needs a store whose memory type is a parameter. That is
a change to Core's runtime types and is not attempted here.

## Limitations

- **Sizes.** At most 1 MiB, and one run each on a 2-vCPU sandbox. Kernel times under the
  Mathlib-closure imports read about 1.5–2× slower than the same cases in the first note,
  which imported only core Lean.
- **RSS includes imports.** Peak memory includes about 2.2 GB of imported `.olean` files
  (the baseline row).
- **Coverage.** `Overlay` and `PageMem` cover only the subset's accesses: 1- and 4-byte loads
  and stores. They have no `memory.grow`, `memory.copy`/`fill` or multiple memories.
  Growing a `PageMem` means adding a level (doubling) or keeping a page count beside the
  tree.
- **Overlay logs are not compacted.** A real implementation would flush the log into a new
  base every few hundred writes, or key it by page.
- **Native timings** come from a compiled executable for the core-only representations.
  `KMem` is `noncomputable` (kernel only). `CoreMem`'s closure imports Mathlib, so its
  algorithm is timed through the `ByteMem` copy.
