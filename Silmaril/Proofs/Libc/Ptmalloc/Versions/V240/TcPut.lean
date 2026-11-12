module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcPut
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.TcGet

/-!
# ptmalloc versions, glibc 2.40: `Task.sim.tcachePut` for `_int_free`'s copy

The 2.40 instance of x86sim's generic block simulation `X86sim.tcPutSim`, as x86sim's
`X86sim.V239.tcachePut239`: `_int_free` loaded at `base + 0xb07c0`, its inlined `tcache_put` at
offset 472 (reading `tcache_key` at `base + 0x218178`), leaving to the epilogue at offset 301,
on `Str9K`, for every load base, thread pointer and TLS offset. The 2.40-specific inputs are
`V240.intFreeTcPut` (decode facts, `decide`), `tcKey240` (where the rip-relative read lands) and
`tcShape240`; no new simulation proof.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Versions.V240

open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.X86 (Word)

/-- `_int_free`'s address at load base `base`. -/
def intFreeAt (base : Nat) : Word := BitVec.ofNat 64 (base + 0xb07c0)

theorem intFreeAt_entry : pin240.entries.intFree = some 0xb07c0 := rfl

/-- Adding a literal to a word at `base + a` (no kernel evaluation of `base + _`). -/
theorem ofNat_add_lit {base a b c : Nat} (h : a + b = c) :
    BitVec.ofNat 64 (base + a) + BitVec.ofNat 64 b = BitVec.ofNat 64 (base + c) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc, h]

/-- The rip-relative read of `tcache_key` lands on the static. -/
theorem tcKey240 (base tp off : Nat) :
    intFreeAt base + BitVec.ofNat 64 (472 + 7) + (0x1677d9#32).signExtend 64 =
      BitVec.ofNat 64 (pin240.repAt base tp off).statics.tcacheKey := by
  have hk : (pin240.repAt base tp off).statics.tcacheKey = base + pin240.syms.tcacheKey := rfl
  have hk2 : pin240.syms.tcacheKey = 0x218178 := rfl
  have hs : (0x1677d9#32).signExtend 64 = BitVec.ofNat 64 0x1677d9 := by decide
  rw [hk, hk2, hs, intFreeAt, ofNat_add_lit (c := 723359) rfl, ofNat_add_lit (c := 0x218178) rfl]

/-- The located copies of `tcache_put` in glibc 2.40 (`_int_free`'s). -/
def tcPutCopies (base tp off : Nat) : List (Block str9kMach AState) :=
  [liftBlock (tcPutBlock pin240.config (pin240.repAt base tp off) intFreeCode (intFreeAt base) 472
    0xffffff22#32)]

/-- **`Task.sim.tcachePut` for glibc 2.40** (its located copies), from the leaf lemmas of
layers (b) and (c), with no new simulation proof. -/
theorem tcachePut240 (hA : Task.algo.leafTcachePut) (hR : Task.x86sim.repTcachePut)
    (base tp off : Nat) :
    Task.sim.tcachePut pin240.config (pin240.repAt base tp off) str9kMach (tcPutCopies base tp off) := by
  intro b hb
  simp only [tcPutCopies, List.mem_singleton] at hb
  subst hb
  exact BlockSim.liftK (fun a x => localAt_k _ _ a x)
    (tcPutSim tcShape240 intFreeTcPut _ (tcKey240 base tp off) hA hR)

/-- `tcachePut240` with the representation step discharged (`repTcachePut`). -/
theorem tcachePut240' (hA : Task.algo.leafTcachePut) (base tp off : Nat) :
    Task.sim.tcachePut pin240.config (pin240.repAt base tp off) str9kMach (tcPutCopies base tp off) :=
  tcachePut240 hA repTcachePut base tp off

end Silmaril.Libc.Ptmalloc.Versions.V240
