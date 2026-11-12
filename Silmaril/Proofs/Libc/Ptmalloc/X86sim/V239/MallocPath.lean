module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocRun
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.TcGet

/-!
# ptmalloc x86sim, glibc 2.39: `malloc` served from the tcache, end to end

`mallocTcacheHit239`: the whole tcache-hit path of glibc 2.39's `__libc_malloc` (prologue, checks,
the bin's count test, the inlined `tcache_get`, epilogue) simulates `Local.tcacheGet` through
`LocalAt`, for **any** arena (`x.1.avAddr` is never named) and any load base, thread pointer and
TLS offset. It is a composition of blocks:

* `prologue`, `checks` (copied runs, no heap state; `MallocRun`), `countTest` and `epilogue`
  (here): they touch only registers and the stack slots, and keep `LocalAt` by the frame lemma
  `localAt_ww` (the stack window holds no cell of the representation or the surroundings);
* the `tcache_get` block: the generic `tcGetCore` (`Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGet`).

So the heap reasoning of the path is exactly the one leaf lemma pair `Task.algo.leafTcacheGet`
/ `Task.x86sim.repTcacheGet`, as for every other copy of `tcache_get`.

The entry facts (`HitEntry`) are machine facts about the call (registers, the stack window, the
return address), image facts (the code, the GOT slot of `tcache`'s TLS offset), address facts
(the stack window and the block's cells apart from the representation and the code), and the
abstract tcache hit (`__malloc_initialized`, a tcache, a non-empty bin `tcIdx n`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.Ext (Loaded loadN storeN subFlagsN logicFlagsN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Data
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239
variable {A : Word}
set_option maxRecDepth 100000

/-! ## The two small blocks -/

set_option maxHeartbeats 4000000 in
/-- **The bin's count test** (offsets `0x148`–`0x155`): `counts[i] > 0`, on to `tcache_get`. -/
theorem countTest {m : MState} {tc idx cnt : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 328) (hrdx : m.core.read .rdx = tc)
    (hr12 : m.core.read .r12 = idx)
    (hcnt : loadN m.memory (tc + (idx <<< 1)) 2 = some cnt) (hcnt0 : cnt.setWidth 16 ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 342 ∧
      m'.core.read .rcx = ((cnt.setWidth 16).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rcx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdx hr12 hcnt ⊢
  refine ex_head (stepC mallocCode_length (o := 328) (l := 5) hl hrip (by decide) d328
    (exec_movzw (v := cnt) (by rw [hrdx, hr12]; exact hcnt))) ?_
  refine ex_head (stepC mallocCode_length (o := 333) (l := 3) hl (by simp [hrip, rip_add]) (by decide)
    d333 exec_test16) ?_
  refine ex_head (stepC mallocCode_length (o := 336) (l := 6) hl (by simp [hrip, rip_add]) (by decide)
    d336 (exec_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]
      exact hcnt0))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, rfl, rfl⟩
  · simp [hrip, rip_add]
  · simp
  · intro r h; simp [h]

set_option maxHeartbeats 4000000 in
/-- **The epilogue** (offsets `0x185`–`0x18f`): the frame popped, return. -/
theorem epilogue {m : MState} {sp ret b0 b1 b2 b3 : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 389) (hrsp : m.core.read .rsp = sp - 0x38#64)
    (hsp : 32 ≤ sp.toNat) (hsp2 : sp.toNat + 8 < 2 ^ 64)
    (hs3 : m.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [b3]))
    (hs2 : m.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [b2]))
    (hs1 : m.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [b1]))
    (hs0 : m.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [b0]))
    (hsr : m.memory.readBytes sp.toNat 8 = some (encodeWords [ret])) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = ret ∧ m'.core.read .rsp = sp + 8#64 ∧
      m'.core.read .rbx = b3 ∧ m'.core.read .r12 = b2 ∧ m'.core.read .r13 = b1 ∧
      m'.core.read .rbp = b0 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .rbp → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hs3 hs2 hs1 hs0 hsr ⊢
  have e18 : (0x18#8).signExtend 64 = 0x18#64 := by decide
  refine ex_fC mallocCode_length hl (o := 389) (l := 4) hrip (by decide) d389
    (exec_aluI8r (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC mallocCode_length (o := 393) (l := 1) hl (by simp [hrip, rip_add]) (by decide) d393
    (exec_pop (v := b3) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs3 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 394) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d394
    (exec_pop (v := b2) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs2 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 396) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d396
    (exec_pop (v := b1) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs1 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 398) (l := 1) hl (by simp [hrip, rip_add]) (by decide) d398
    (exec_pop (v := b0) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs0 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 399) (l := 1) hl (by simp [hrip, rip_add]) (by decide) d399
    (exec_ret (v := ret) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hsr using 2; bv_omega))) ?_
  refine ⟨_, Reaches.refl _ _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega
  · simp
  · simp
  · simp
  · simp
  · intro r a b c d e; simp [a, b, c, d, e]

end Silmaril.Libc.Ptmalloc.X86sim.V239
