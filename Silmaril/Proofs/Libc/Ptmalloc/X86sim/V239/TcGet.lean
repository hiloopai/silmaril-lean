module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGet
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.Code
public import Silmaril.Libc.Ptmalloc.Version.Thms

/-!
# ptmalloc x86sim, glibc 2.39: `Task.sim.tcacheGet` for `__libc_malloc`'s copy

The instance of the generic `tcGetSim` at `pin239`: `__libc_malloc` loaded at `base + 0xad750`,
its inlined `tcache_get` at offset 342, on `Str9K`, for every load base, thread pointer and TLS
offset. All per-version content is `V239.mallocTcGet` (decode facts) and `tcShape239` (`decide`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.X86sim.V239

open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.X86 (Word)

/-- `__libc_malloc`'s address at load base `base`. -/
def mallocAt (base : Nat) : Word := BitVec.ofNat 64 (base + pin239.entries.malloc)

/-- glibc 2.39 has the x86-64 tcache shape. -/
theorem tcShape239 : TcShape pin239.config pin239.layout := ⟨pin239_ok, rfl, rfl, rfl, rfl⟩

/-- The located copies of `tcache_get` in glibc 2.39 (so far `__libc_malloc`'s; `_int_malloc`'s
`return_cached` copy is not located yet). -/
def tcGetCopies (base tp off : Nat) : List (Block str9kMach AState) :=
  [liftBlock (tcGetBlock pin239.config (pin239.repAt base tp off) mallocCode (mallocAt base) 342)]

/-- **`Task.sim.tcacheGet` for glibc 2.39** (its located copies), from the leaf lemmas of
layers (b) and (c). -/
theorem tcacheGet239 (hA : Task.algo.leafTcacheGet) (hR : Task.x86sim.repTcacheGet)
    (base tp off : Nat) :
    Task.sim.tcacheGet pin239.config (pin239.repAt base tp off) str9kMach (tcGetCopies base tp off) := by
  intro b hb
  simp only [tcGetCopies, List.mem_singleton] at hb
  subst hb
  exact BlockSim.liftK (fun a x => localAt_k _ _ a x) (tcGetSim tcShape239 mallocTcGet _ hA hR)

/-- `tcacheGet239` with the representation step discharged (`repTcacheGet`): only the
algorithm-level leaf lemma remains (`Algo.leafTcacheGet` on the algo branch). -/
theorem tcacheGet239' (hA : Task.algo.leafTcacheGet) (base tp off : Nat) :
    Task.sim.tcacheGet pin239.config (pin239.repAt base tp off) str9kMach (tcGetCopies base tp off) :=
  tcacheGet239 hA repTcacheGet base tp off

end Silmaril.Libc.Ptmalloc.X86sim.V239
