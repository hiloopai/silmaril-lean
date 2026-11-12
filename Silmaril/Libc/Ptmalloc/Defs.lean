module

public import Silmaril.Libc.Ptmalloc.Config.Defs
public import Silmaril.Libc.Ptmalloc.Chunk.Defs
public import Silmaril.Libc.Ptmalloc.Tcache.Defs
public import Silmaril.Libc.Ptmalloc.Fastbins.Defs
public import Silmaril.Libc.Ptmalloc.Bins.Defs
public import Silmaril.Libc.Ptmalloc.Unsorted.Defs
public import Silmaril.Libc.Ptmalloc.Top.Defs
public import Silmaril.Libc.Ptmalloc.Mmap.Defs
public import Silmaril.Libc.Ptmalloc.Kernel.Defs
public import Silmaril.Libc.Ptmalloc.Layout.Defs
public import Silmaril.Libc.Ptmalloc.Heap.Defs
public import Silmaril.Libc.Ptmalloc.Algo.Defs
public import Silmaril.Libc.Ptmalloc.Rep.Defs
public import Silmaril.Libc.Ptmalloc.Env.Defs
public import Silmaril.Libc.Ptmalloc.Sim.Defs
public import Silmaril.Libc.Ptmalloc.Version.Defs
public import Silmaril.Libc.Ptmalloc.Bridge.Defs

/-!
# ptmalloc

The glibc allocator proofs, layered. Four layers, each parametric in the
per-version `Config`:

| layer | modules | content |
|---|---|---|
| (a) institution | `Bridge` → `Silmaril.Libc.X86Alloc.Spec`, `Silmaril.Libc.Shapes.Alloc` | `relModel`, `heapModel`, `Task.bridge.model` |
| (b) algorithm | `Config`, `Chunk`; components `Tcache`, `Fastbins`, `Bins`, `Unsorted`, `Top`, `Mmap`, `Kernel`; `Heap` (composition), `Algo` | plain Lean ptmalloc over a partitioned, arena-parametric heap composed of sub-models; WF and refinement obligations (`Task.algo.*`) |
| (c) representation | `Layout`, `Rep`, `Env`; generic library `Silmaril.Data.{Cells,SepList,Bitmap,BoundaryTag}` | one decidable fragment per component, `LocalRep`, the frame rule; the surroundings apart (`envFrag`, `SurrInv`) |
| (d) x86 | `Sim`, `Version` | `Mach`, `Triple` with footprints and its composition rules, `BlockSim`, `Inlined`; per-pin records (`pin239`) |

## Variants

A monolithic proof of glibc 2.39's four entry points against one `heapRep` over x86 memory,
path by path, with whole-run machine proofs, makes every model fix touch every path proof. This
development separates
what changes for different reasons: a version (only `Version`), a model fix in the
surroundings (only `Env` and `Sim.Callee`), the algorithm (only `Algo`, proved without x86), and
the code (block obligations in `Sim`). It costs an explicit simulation relation and the
abstract/concrete split of every path; it pays off when the same algorithm-level theorems
serve 2.36, 2.39 and 2.40, and when threads are added (the bodies are already arena-parametric).
-/
