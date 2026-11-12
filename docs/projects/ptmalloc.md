# glibc's allocator: the tcache paths of `malloc` and `free`, end to end

A verified model of glibc's ptmalloc (glibc 2.39 as built by Ubuntu, with data for 2.36 and
2.40) and two end-to-end theorems: on their tcache paths, the x86-64 machine code of
`__libc_malloc` and `__libc_free` simulates the algorithm model, and the model's step meets the
allocator institution's loose `malloc`/`free` contract. The development is in four layers, each
parametric in the per-version configuration, so most of it is proved once for every version.

| Layer | Modules | Content |
| --- | --- | --- |
| (a) institution | `Silmaril.Libc.Ptmalloc.Bridge`, `Refine` | `relModel`, `heapModel`; the refinement invariant `Algo.RefInv` (well-formed world, ghost tokens matching `Silmaril.Libc.Alloc`'s heap) |
| (b) algorithm | `Config`, `Chunk`; components `Tcache`, `Fastbins`, `Bins`, `Unsorted`, `Top`, `Mmap`, `Kernel`; `Heap` (composition), `Algo` | plain Lean ptmalloc (`Algo.ptmalloc C : Ops C`) over a partitioned, arena-parametric world: `_int_malloc`, `_int_free`, `sysmalloc`, `systrim`, `heap_trim`, `malloc_consolidate`, the arena choice |
| (c) representation | `Layout`, `Rep`, `Env`; `Silmaril.Data.{Cells,SepList,Bitmap,BoundaryTag}` | one decidable byte fragment per component (`LocalRep`), the frame rule, the surroundings (`envFrag`, `SurrInv`) |
| (d) x86 | `Sim`, `X86sim`, `Version` | Hoare triples over a machine with footprints (`Mach.Triple`), block simulations of `tcache_get` and `tcache_put`, per-pin records (`pin236`, `pin239`, `pin240`) |

Proofs are under `Silmaril.Proofs.Libc.Ptmalloc`. `Silmaril.Libc.Ptmalloc.E2e.Thms` gathers the
tops; `Silmaril.Libc.Ptmalloc.Difftest` holds the soundness lemmas of a differential tester's
checks (the tester itself is not part of this release).

## What is proved

**`Silmaril.Libc.Ptmalloc.E2e.mallocTcache239`** (`Silmaril.Proofs.Libc.Ptmalloc.E2e.V239Sys`). For
every load base, thread pointer, TLS offset, abstract state `x`, request `n`, stack pointer,
return address and register file, every thread `tid`, world `w` and token heap `h` with
`RefInv pin239.config tid ⟨w, h⟩`, and `x.1` the view of the thread's arena: from any `Str9K`
state that holds `x`'s representation (`LocalAt`) and is at the tcache-hit entry of
`__libc_malloc (n)` (`X86sim.V239.HitEntry`: the 796 code bytes loaded at `base + 0xad750`, `rip`
there, `rdi = n`, a writable 32-byte stack window apart from the code and the heap, the GOT slot
of `tcache`, and a non-empty tcache bin for `n`), the machine reaches a state where

* `(ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l')` for some `p`, `l'`, and the
  new state holds `l'`'s representation;
* `rip = ret`, `rax = p`, `rsp = sp + 8`, and every System V callee-saved register is restored;
* `RefInv` holds again with `p` added to the token heap, and
  `allocLoose h (.malloc n) (.ok h' p)`: the institution's loose `malloc` contract;
* the run wrote only its stack window and `tcache_get`'s cells (the triple's footprint).

**`Silmaril.Libc.Ptmalloc.E2e.freeTcache239`**: the same for `free (ch.addr + 16)` on
`__libc_free`'s tcache path (`X86sim.V239.FreeEntry`: `__libc_free`'s 272 bytes at `0xade30` and
`_int_free`'s tcache part, 897 bytes at `0xab250`), for a chunk that is lent out
(`h (ch.addr + 16)` is defined), not `mmap`ed, in a thread with a tcache; the model's `free`
makes the same step, the token is removed, and the run writes only its two stack frames and
`tcache_put`'s cells.

Both are **unconditional**: no `Task`, no invariant-preservation hypothesis and no machine
simulation hypothesis. Their proofs discharge, on the way, every per-body obligation of the
algorithm model that the tcache paths depend on (`Algo.bodyFree`, `Algo.totalFree`,
`Algo.consolidateBody`, `Algo.sysMainBody`, `Algo.sysHeapBody`, …); `E2e.Thms` lists the
conditional intermediate forms (`_sys`, `_main`, `_heap`, `_bodies`, `_load`, `_safe`).

Further results:

* **glibc 2.40** (`E2e.V240`, data only): `E2e.mallocTcache240`, the generic gcc 13/14 path
  `X86sim.Gcc13.mallocTcacheHitK'` at 2.40's bytes; `E2e.freeTcache240_of`.
* **glibc 2.36** (`E2e.V236`): `E2e.mallocTcache236` (gcc 12 keeps the bin index in `rbp`; the
  register-parametric `tcache_get`), `E2e.freeTcache236_of` (from a simulation of `_int_free`).
* **Versions**: `Versions.pin236_matches`, `pin239_matches`, `pin240_matches` check every number
  of the hand-written pin records against generated facts (`decide`); `Version.Thms` proves the
  configurations' sanity conditions.

**`calloc` and `realloc`, algorithm level** (`Silmaril.Proofs.Libc.Ptmalloc.Algo.{ReallocSteps,
ReallocBody, Mremap, WorldRealloc, CallocReallocInst}`), unconditional for every `C` with `C.Ok`:

* `Algo.bodyRealloc` (= `Task.algo.bodyRealloc`) and `Algo.wfIntRealloc`
  (= `Task.algo.wfIntRealloc`): `_int_realloc` of a lent-out arena chunk, on all its paths (keep;
  shrink with the remainder `_int_free`d; grow into top; grow into a free next chunk; and
  `_int_malloc`, then glibc's in-place `newp == next` fusion or copy and `_int_free`), keeps
  `LocalWF`, has a `Frame` and replaces the old payload by one of at least `nb - SIZE_SZ` bytes;
* `Algo.mremap_body`: `mremap_chunk` moving an `mmap`ed chunk;
* `Algo.wfCallocRealloc` (= `Task.algo.wfCallocRealloc C (ptmalloc C)`): `__libc_calloc` and
  `__libc_realloc` (all paths: `realloc (p, 0)`, `mmap`ed chunks, arena chunks, the
  multi-threaded retry) keep `WorldWF` and the thread set and change the live set as `allocLoose`
  allows;
* `Algo.calloc_refines`, `Algo.realloc_refines`: with ghost tokens (`RefInv`) a `calloc` or
  `realloc` step meets the institution's `calloc`/`realloc` and keeps `RefInv`; at the pins:
  `E2e.calloc239`, `E2e.realloc239`, and the data-only `calloc236`, `realloc236`, `calloc240`,
  `realloc240`;
* `Algo.noAbort` (= `Task.algo.noAbort C (ptmalloc C)`, stated on a view with its spatial facts):
  `_int_malloc` and `_int_free` of a live arena payload never abort.

The `_int_realloc` model's fallback (`Algo.reallocCopy`) states two facts about glibc's
`next == newp` test as `internal` aborts (states the model's invariants exclude): `next` was
not lent out before `_int_malloc`, and the new chunk is the old one's neighbour in the tiling
(glibc's `next` is then a fence post or a lent-out chunk, which `_int_malloc` never returns).
`wfIntRealloc` and `bodyRealloc` are about successful runs; that these aborts are unreachable (a
`realloc` totality theorem) is not proved.

Open: the other obligations remain `def Task.… : Prop` (for example the x86 simulations of the
non-tcache paths, `Task.sim.*`, and the design's `Task.algo.wfIntMalloc`, stated without the
view's spatial facts; its proved form is `Task.algo.bodyMalloc`); the theorems that use them take
them as hypotheses. They are defined in `Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs`,
`Silmaril.Libc.Ptmalloc.Sim.Defs` and the modules they concern.

## Trusted base

The theorems rest on Lean's kernel and the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); no `sorry`, `axiom` or `native_decide`. What a reader must check to believe that
they say something about glibc:

1. **The machine.** `Silmaril.X86.Str9K` (`Str9G` with system calls, the kernel's answers as an
   oracle), through `X86sim.str9kMach`; its instruction semantics are the x86 tree's
   (`docs/x86.md`). The tcache paths make no system call, so the oracle plays no part in them.
2. **The code bytes.** `X86sim.V239.{mallocCode, freeCode, intFreeCode}` (and the 2.36/2.40
   `Versions.*.Code`) are list literals transcribed from the pinned `libc.so.6` files. The
   theorems are about these literals; `scripts/ptmalloc/check-code.py DIR` checks them against
   the files (sha256 and byte-for-byte). Only these ranges are stored (7 ranges, 4866 bytes in
   all); see `NOTICES/glibc-malloc`.
3. **The pin records.** `Version.pin239` (struct layouts, static and GOT offsets, entry
   addresses) is checked against `Version.Facts`, which an untrusted generator produced from the
   pinned file and its `libc6-dbg` DWARF. A wrong fact makes a theorem about the wrong address,
   not a false proof; the entry conditions `HitEntry`/`FreeEntry` name the addresses they use.
4. **The entry conditions and the representation.** `HitEntry`, `FreeEntry` (in
   `Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239`), `LocalAt` and `LocalRep`: what it means for
   memory to hold an abstract heap. They are decidable on concrete memory, which is what the
   differential tester's soundness lemmas (`Difftest.Thms`) exploit.
5. **The contract.** `Silmaril.Libc.Alloc.allocLoose` and the token heap `Heap` (the allocator
   institution), and `Algo.RefInv`.

Not covered: the x86 code of other paths of `malloc` and `free` (they are stated,
conditionally), the x86 code of `__libc_calloc` and `__libc_realloc` (proved at the algorithm
level only; glibc 2.39's `calloc` has no tcache path, it always runs `_int_malloc`), threads
running concurrently (the model is arena-parametric but the triples are sequential), `memalign`,
and the loading of `libc.so.6` itself (the entry condition asks for the bytes to be in memory at
the load base).

## Pins

| Pin | Package | `libc.so.6` sha256 |
| --- | --- | --- |
| `ubuntu_2_39_0ubuntu8_9` | Ubuntu 24.04 `libc6` 2.39-0ubuntu8.9 amd64 | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |
| `ubuntu_2_40_1ubuntu3_1` | Ubuntu 24.10 `libc6` 2.40-1ubuntu3.1 amd64 | `132ba50d4abaeff314e64f5d84daa4e4e6d9b227135bc035fde1b69a81aab204` |
| `debian_2_36_9_deb12u14` | Debian 12 `libc6` 2.36-9+deb12u14 amd64 | `6b4a45352fd0c540a9c7c718f35ce8c8e46a4e482f9d3885a910c32d1a0e1421` |

To check the transcribed bytes, extract `libc.so.6` from each package into `DIR/<pin>/libc.so.6`
and run `python3 scripts/ptmalloc/check-code.py DIR`.

## Build

```
lake build Silmaril.Libc.Ptmalloc.E2e.Thms
```

The headline theorems alone: `lake build Silmaril.Proofs.Libc.Ptmalloc.E2e.V239Sys`.
