module

public import Silmaril.Libc.Ptmalloc.Thms
public import Silmaril.Libc.Ptmalloc.X86sim.Thms
public import Silmaril.Libc.Ptmalloc.Difftest.Thms
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.TcGet
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.Inst
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V239
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V239Sys
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V240
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V236
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.CallocRealloc
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.PinsSys

/-!
# ptmalloc: end to end

The top of the development: the four layers composed (guide: `docs/projects/ptmalloc.md`).

* version-generic (`Silmaril.Proofs.Libc.Ptmalloc.E2e.Inst`): `E2e.malloc_tcacheHit`,
  `E2e.free_intFree` (the model's world-level calls on the tcache paths are the leaf/body on the
  thread's arena), `E2e.malloc_inst`, `E2e.free_inst` (any `SafeMF` model's steps meet the
  institution's `allocLoose`), `E2e.mallocTcache_post`, `E2e.freeTcache_post`,
  `E2e.intFree_tcache_exists`;
* glibc 2.39, **unconditional** (`…E2e.V239Sys`): **`E2e.mallocTcache239`** (x86 `__libc_malloc`
  tcache hit → model → institution, any arena, from any world with `RefInv`) and
  **`E2e.freeTcache239`** (`__libc_free`'s tcache path), with no `Task`, `SafeMF` or `hX`
  hypothesis; the conditional steps `_sys` (on the four `sysmalloc` Tasks), `_main`, `_heap`;
* glibc 2.39 (`…E2e.V239`): `E2e.hitBin_eq` (the code's tcache index is `utidx`),
  `E2e.mallocTcache239_safe` (for any `SafeMF` invariant),
  `E2e.freeTcache239_of` (the same for `__libc_free`, from any x86 simulation of `_int_free`),
  `E2e.freeTcache239_safe`; their load-time forms `E2e.mallocTcache239_load`/`freeTcache239_load`
  (conditional on `Task.algo.wfWorld` and `mallocTotal`) and `E2e.mallocTcache239_bodies`/
  `freeTcache239_bodies` (conditional only on `Task.algo.{bodyMalloc, bodyFree, totalMalloc,
  totalFree}`);
* glibc 2.40 (`…E2e.V240`), data only: **`E2e.mallocTcache240`** (x86sim's generic gcc 13/14
  path `X86sim.Gcc13.mallocTcacheHitK'` at `Versions.V240.mallocPin240`), `E2e.freeTcache240_of`;
  `E2e.hitBin_utidx` (`…E2e.Malloc`) is the code's index for any LP64 configuration;
* glibc 2.36 (`…E2e.V236`): **`E2e.mallocTcache236`** (gcc 12: 2.36's own non-heap runs
  `Versions.V236.MallocRun`, the register-parametric `tcache_get` with the bin in `rbp`),
  `E2e.freeTcache236_of`.

* glibc 2.36 and 2.40, **unconditional** (`…E2e.PinsSys`): **`E2e.mallocTcache236_refInv`**,
  **`E2e.mallocTcache240_refInv`**: the tcache hit of `__libc_malloc` from any world with `RefInv`
  (`E2e.safeMF_refInv`: `SafeMF` for `RefInv` at every configuration, all body obligations proved);
* `calloc`/`realloc`, algorithm level (`…E2e.CallocRealloc`): **`E2e.calloc239`**,
  **`E2e.realloc239`** (and the 2.36/2.40 data-only instances `calloc236`, `realloc236`,
  `calloc240`, `realloc240`): with `RefInv`, the model's `calloc (k, m)` and `realloc (p, n)` of a
  token meet the institution's `calloc`/`realloc` and keep `RefInv` (`Algo.calloc_refines`,
  `Algo.realloc_refines`); no x86 simulation of `__libc_calloc`/`__libc_realloc` yet.

This header also gathers the variant's other tops: the x86 block simulations
(`Silmaril.Libc.Ptmalloc.X86sim.Thms`), glibc 2.40's `tcache_get` and `tcache_put` blocks
(`Versions.V240.tcacheGet240`, `tcachePut240`), glibc 2.36's `tcache_get` block
(`Versions.V236.tcacheGet236`) and the differential tester's soundness lemmas.
-/
