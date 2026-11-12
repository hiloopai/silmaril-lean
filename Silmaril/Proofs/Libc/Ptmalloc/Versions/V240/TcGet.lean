module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGet
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.Code
public import Silmaril.Libc.Ptmalloc.Version.Thms

/-!
# ptmalloc versions, glibc 2.40: `Task.sim.tcacheGet` for `__libc_malloc`'s copy

The 2.40 instance of x86sim's generic block simulation `X86sim.tcGetSim`, exactly as x86sim's
`X86sim.V239.tcacheGet239`: `__libc_malloc` loaded at `base + 0xb2c60`, its inlined
`tcache_get` at offset 350, on `Str9K`, for every load base, thread pointer and TLS offset. The
per-version content is `V240.mallocTcGet` (decode facts of the 2.40 bytes, by `decide`) and
`tcShape240` (`decide`/`rfl`); no new proof of the simulation.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Versions.V240

open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.X86 (Word)

/-- `__libc_malloc`'s address at load base `base`. -/
def mallocAt (base : Nat) : Word := BitVec.ofNat 64 (base + pin240.entries.malloc)

/-- glibc 2.40 has the x86-64 tcache shape. -/
theorem tcShape240 : TcShape pin240.config pin240.layout := ⟨pin240_ok, rfl, rfl, rfl, rfl⟩

/-- The located copies of `tcache_get` in glibc 2.40 (as for 2.39: `__libc_malloc`'s). -/
def tcGetCopies (base tp off : Nat) : List (Block str9kMach AState) :=
  [liftBlock (tcGetBlock pin240.config (pin240.repAt base tp off) mallocCode (mallocAt base) 350)]

/-- **`Task.sim.tcacheGet` for glibc 2.40** (its located copies), from the leaf lemmas of
layers (b) and (c), with no new simulation proof. -/
theorem tcacheGet240 (hA : Task.algo.leafTcacheGet) (hR : Task.x86sim.repTcacheGet)
    (base tp off : Nat) :
    Task.sim.tcacheGet pin240.config (pin240.repAt base tp off) str9kMach
      (tcGetCopies base tp off) := by
  intro b hb
  simp only [tcGetCopies, List.mem_singleton] at hb
  subst hb
  exact BlockSim.liftK (fun _ _ => Iff.rfl) (tcGetSim tcShape240 mallocTcGet _ hA hR)

end Silmaril.Libc.Ptmalloc.Versions.V240
