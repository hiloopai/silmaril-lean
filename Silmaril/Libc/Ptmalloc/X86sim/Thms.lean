module

public import Silmaril.Libc.Ptmalloc.X86sim.Defs
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocHit
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.TcPut
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocSingle
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreePath

/-!
# ptmalloc: x86 block simulation — theorems

Proved (standard axioms only). The layer-(c) steps are proved here, x86-free:
`repTcacheGet : Task.x86sim.repTcacheGet` (`repTcacheGet_of`) and
`repTcachePut : Task.x86sim.repTcachePut` (`repTcachePut_of`); so the primed theorems take only
the layer-(b) leaf lemma (`Task.algo.leafTcacheGet`/`leafTcachePut`, proved as
`Algo.leafTcacheGet`/`leafTcachePut` on the algo branch):

* generic, any version: `tcGetSim`/`tcGetCore` (the `tcache_get` block simulates
  `Local.tcacheGet`), `tcPutSim` (the `tcache_put` block simulates `Local.tcachePut`),
  `localAt_ww` (the frame of `LocalAt` under writes that miss it), `memView_storeN`,
  `cell_load`, `within_of_ww`, `Triple.liftK`, `BlockSim.liftK`;
* glibc 2.39: `V239.tcacheGet239 : Task.sim.tcacheGet pin239.config (pin239.repAt …) str9kMach …`
  (`__libc_malloc`'s copy), `V239.tcachePut239`/`tcachePut239' : Task.sim.tcachePut …` (`_int_free`'s copy),
  `V239.mallocTcacheHit239K` / `mallocTcacheHit239K'`: `__libc_malloc`'s whole tcache-hit path on
  `Str9K`, any arena; `V239.tcacheGet239'`;
  `V239.prologueSingle239 : Task.sim.prologueSingle …` (`__libc_malloc`'s `SINGLE_THREAD_P` block,
  handing the body `rdi = av`);
  `V239.freeTcachePut239K` / `freeTcachePut239K'`: `__libc_free`'s whole tcache path on `Str9K`
  (entry, `_int_free`'s checks, the `e->key` double-free walk, the generic `tcPutCore`, both
  epilogues, `errno` restored), any arena.
-/
