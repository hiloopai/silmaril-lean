module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocHit

/-!
# ptmalloc x86sim, glibc 2.39: `__libc_malloc`'s `SINGLE_THREAD_P` prologue, apart from the body

`singleBlock`: offsets `0x65` → `0x190` → `0x19d` of `__libc_malloc` (after a tcache miss):
`if (SINGLE_THREAD_P) victim = _int_malloc (&main_arena, bytes)` up to the call. It reads the
surroundings' single-thread cell (`__libc_single_threaded`, through `envFrag`), takes the
single-threaded branch, and hands the body `rdi = rbx = av` and `rsi` = the request: the body
`_int_malloc` is then proved for that arbitrary arena address (`Local.avAddr`), never for
`main_arena` by name. It writes nothing.

`prologueSingle239 : Task.sim.prologueSingle pin239.config (pin239.repAt base tp off) str9kMach …`.
The `Task`'s step (`x' = x ∧ singleThreaded ∧ isMain`) forces the block's pre to assume the
single-threaded case and the main arena; the multi-threaded exit (`arena_get`) is the other
branch of the same test and is not a `prologueSingle` obligation.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN subFlagsN logicFlagsN Mem)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.X86
open Silmaril.Data
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239
set_option maxRecDepth 100000

theorem s101 : Str9Fs.decode ((mallocCode.drop 101).take 7) =
    some (ix (.cmpI8 (.mem (Ext.Mem.ofRip 0x15e884#32)) 0#8), 7) := by decide
theorem s108 : Str9Fs.decode ((mallocCode.drop 108).take 6) = some (ix (.jcc .ne 0x11e#32), 6) := by
  decide
theorem s400 : Str9Fs.decode ((mallocCode.drop 400).take 3) = some (ix (.mov .q (.reg .rsi) .rbx), 3) := by
  decide
theorem s403 : Str9Fs.decode ((mallocCode.drop 403).take 7) =
    some (ix (.lea .q .rbx (Ext.Mem.ofRip 0x1571d6#32)), 7) := by decide
theorem s410 : Str9Fs.decode ((mallocCode.drop 410).take 3) = some (ix (.mov .q (.reg .rdi) .rbx), 3) := by
  decide

/-- **The `SINGLE_THREAD_P` block** of `__libc_malloc` at load base `base`. -/
def singleBlock (base : Nat) : Block fsMach AState where
  entry := (mallocAt base + BitVec.ofNat 64 101).toNat
  exits := [(mallocAt base + BitVec.ofNat 64 413).toNat]
  pre x s := Loaded s.memory (mallocAt base) mallocCode ∧ x.2.1.singleThreaded = true ∧
    x.1.isMain = true ∧ x.1.avAddr = pin239.mainArena base
  post x s := Loaded s.memory (mallocAt base) mallocCode ∧
    s.core.read .rdi = BitVec.ofNat 64 x.1.avAddr ∧ s.core.read .rbx = BitVec.ofNat 64 x.1.avAddr
  fp _ _ := False

theorem ofNat_base {base a b : Nat} (h : a = b) : BitVec.ofNat 64 (base + a) = BitVec.ofNat 64 (base + b) := by
  rw [h]

set_option maxHeartbeats 4000000 in
/-- **The run of the `SINGLE_THREAD_P` block** (offsets `0x65` → `0x190` → `0x19d`), the flag set. -/
theorem singleRun {A : Word} {m : MState} {f : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 101)
    (hf : loadN m.memory (A + BitVec.ofNat 64 108 + BitVec.ofNat 64 0x15e884) 1 = some f)
    (hf0 : f.setWidth 8 ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 413 ∧
      m'.core.read .rdi = A + BitVec.ofNat 64 410 + BitVec.ofNat 64 0x1571d6 ∧
      m'.core.read .rbx = A + BitVec.ofNat 64 410 + BitVec.ofNat 64 0x1571d6 ∧
      m'.core.read .rsi = m.core.read .rbx ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hf ⊢
  have e11e : (0x11e#32).signExtend 64 = BitVec.ofNat 64 0x11e := by decide
  have e884 : (0x15e884#32).signExtend 64 = BitVec.ofNat 64 0x15e884 := by decide
  have hs2 : (0x1571d6#32).signExtend 64 = BitVec.ofNat 64 0x1571d6 := by decide
  refine ex_head (stepC mallocCode_length (o := 101) (l := 7) hl hrip (by decide) s101
    (exec_cmpI8m (v := f) (by
      simp only [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip,
        Silmaril.X86.Ext.Base.value_rip, Option.map_none, Option.getD_none, BitVec.add_zero]
      rw [hrip, e884, rip_add A 101 7]; exact hf))) ?_
  refine ex_head (stepC mallocCode_length (o := 108) (l := 6) hl (by simp [hrip, rip_add]) (by decide) s108
    (exec_jcc (b := true) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot]
      exact hf0))) ?_
  refine ex_head (stepC mallocCode_length (o := 400) (l := 3) hl
    (by simp [hrip, rip_add, e11e]) (by decide) s400 exec_movrr) ?_
  refine ex_head (stepC mallocCode_length (o := 403) (l := 7) hl
    (by simp [hrip, rip_add, e11e]) (by decide) s403 fx_learip) ?_
  refine ex_head (stepC mallocCode_length (o := 410) (l := 3) hl
    (by simp [hrip, rip_add, e11e]) (by decide) s410 exec_movrr) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, rfl⟩
  · simp [hrip, rip_add, e11e]
  · simp [hrip, rip_add, e11e, hs2]
  · simp [hrip, rip_add, e11e, hs2]
  · simp

set_option maxHeartbeats 4000000 in
/-- **The `SINGLE_THREAD_P` block simulates the prologue's choice** (no state change; the body
gets the arena in `rdi`). -/
theorem singleSim (base tp off : Nat) :
    BlockSim (LocalAt pin239.config (pin239.repAt base tp off) fsMach)
      (fun x x' => x' = x ∧ x.2.1.singleThreaded = true ∧ x.1.isMain = true) (singleBlock base) := by
  rintro x m ⟨hLA, ⟨hl, hst, hmain, hav⟩, hpc⟩
  have hLA' := hLA
  obtain ⟨-, -, henv, -, -⟩ := hLA'
  have hmem : (⟨(pin239.repAt base tp off).env.singleAddr, (pin239.repAt base tp off).env.singleWidth,
      if x.2.1.singleThreaded then (pin239.repAt base tp off).env.singleVal
      else (pin239.repAt base tp off).env.multiVal⟩ : Cell) ∈
      envFrag pin239.config (pin239.repAt base tp off).layout (pin239.repAt base tp off).env x.2.1 :=
    List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [hst] at hmem
  have kS := (cell_load (henv _ hmem) (by show (0:Nat) < 1; decide)).1
  have hmm : pin239.entries.malloc = 0xad750 := rfl
  have aS : mallocAt base + BitVec.ofNat 64 108 + BitVec.ofNat 64 0x15e884 =
      BitVec.ofNat 64 (pin239.repAt base tp off).env.singleAddr := by
    have ha : (pin239.repAt base tp off).env.singleAddr = base + pin239.syms.singleThreaded := rfl
    have ha2 : pin239.syms.singleThreaded = 0x20c040 := rfl
    rewrite [ha, ha2, mallocAt, hmm, ofNat_lit_add, ofNat_lit_add]
    exact ofNat_base (by decide)
  have hav' : mallocAt base + BitVec.ofNat 64 410 + BitVec.ofNat 64 0x1571d6 =
      BitVec.ofNat 64 x.1.avAddr := by
    have hm : pin239.mainArena base = base + pin239.syms.mainArena := rfl
    have hm2 : pin239.syms.mainArena = 0x204ac0 := rfl
    rewrite [hav, hm, hm2, mallocAt, hmm, ofNat_lit_add, ofNat_lit_add]
    exact ofNat_base (by decide)
  obtain ⟨m', hr, hrip', hrdi, hrbx, -, hmem'⟩ := singleRun (f := BitVec.ofNat 64 1) hl
    (BitVec.eq_of_toNat_eq hpc) (by rw [aS]; exact kS) (by decide)
  refine ⟨m', hr, ⟨by show m'.core.rip.toNat ∈ [_]; rw [hrip']; exact List.mem_singleton_self _, x, ⟨rfl, hst, hmain⟩, localAt_mem hLA hmem',
    by rw [hmem']; exact hl, by rw [hrdi, hav'], by rw [hrbx, hav']⟩, fun a _ => ?_⟩
  simp [fsMach, hmem']

/-- **`Task.sim.prologueSingle` for glibc 2.39's `__libc_malloc`.** -/
theorem prologueSingle239 (base tp off : Nat) :
    Task.sim.prologueSingle pin239.config (pin239.repAt base tp off) str9kMach
      (liftBlock (singleBlock base)) :=
  BlockSim.liftK (fun a x => localAt_k _ _ a x) (singleSim base tp off)

end Silmaril.Libc.Ptmalloc.X86sim.V239
