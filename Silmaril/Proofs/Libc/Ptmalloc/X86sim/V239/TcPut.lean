module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcPut
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.TcGet

/-!
# ptmalloc x86sim, glibc 2.39: `Task.sim.tcachePut` for `_int_free`'s copy

The instance of the generic `tcPutSim` at `pin239`: `_int_free` loaded at `base + 0xab250`, its
inlined `tcache_put` at offset 472 (reading `tcache_key` at `base + 0x20b178`), leaving to the
epilogue at offset 301, on `Str9K`, for every load base, thread pointer and TLS offset.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.X86sim.V239

open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.X86 (Word)

/-- `_int_free`'s address at load base `base`. -/
def intFreeAt (base : Nat) : Word := BitVec.ofNat 64 (base + 0xab250)

theorem intFreeAt_entry : pin239.entries.intFree = some 0xab250 := rfl

/-- Adding a literal to a word at `base + a` (no kernel evaluation of `base + _`). -/
theorem ofNat_add_lit {base a b c : Nat} (h : a + b = c) :
    BitVec.ofNat 64 (base + a) + BitVec.ofNat 64 b = BitVec.ofNat 64 (base + c) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc, h]

/-- The rip-relative read of `tcache_key` lands on the static. -/
theorem tcKey239 (base tp off : Nat) :
    intFreeAt base + BitVec.ofNat 64 (472 + 7) + (0x15fd49#32).signExtend 64 =
      BitVec.ofNat 64 (pin239.repAt base tp off).statics.tcacheKey := by
  have hk : (pin239.repAt base tp off).statics.tcacheKey = base + pin239.syms.tcacheKey := rfl
  have hk2 : pin239.syms.tcacheKey = 0x20b178 := rfl
  have hs : (0x15fd49#32).signExtend 64 = BitVec.ofNat 64 0x15fd49 := by decide
  rw [hk, hk2, hs, intFreeAt, ofNat_add_lit (c := 701487) rfl, ofNat_add_lit (c := 0x20b178) rfl]

/-- The located copies of `tcache_put` in glibc 2.39 (so far `_int_free`'s; `_int_malloc`'s
refill copies are not located yet). -/
def tcPutCopies (base tp off : Nat) : List (Block str9kMach AState) :=
  [liftBlock (tcPutBlock pin239.config (pin239.repAt base tp off) intFreeCode (intFreeAt base) 472
    0xffffff22#32)]

/-- **`Task.sim.tcachePut` for glibc 2.39** (its located copies), from the leaf lemmas of
layers (b) and (c). -/
theorem tcachePut239 (hA : Task.algo.leafTcachePut) (hR : Task.x86sim.repTcachePut)
    (base tp off : Nat) :
    Task.sim.tcachePut pin239.config (pin239.repAt base tp off) str9kMach (tcPutCopies base tp off) := by
  intro b hb
  simp only [tcPutCopies, List.mem_singleton] at hb
  subst hb
  exact BlockSim.liftK (fun a x => localAt_k _ _ a x)
    (tcPutSim tcShape239 intFreeTcPut _ (tcKey239 base tp off) hA hR)

/-- `tcachePut239` with the representation step discharged (`repTcachePut`): only the
algorithm-level leaf lemma remains (`Algo.leafTcachePut` on the algo branch). -/
theorem tcachePut239' (hA : Task.algo.leafTcachePut) (base tp off : Nat) :
    Task.sim.tcachePut pin239.config (pin239.repAt base tp off) str9kMach (tcPutCopies base tp off) :=
  tcachePut239 hA repTcachePut base tp off

end Silmaril.Libc.Ptmalloc.X86sim.V239
