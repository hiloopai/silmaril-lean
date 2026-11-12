module

public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V236.Code
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.MallocKit

/-!
# ptmalloc versions, glibc 2.36: `__libc_malloc`'s non-heap blocks, as machine runs

gcc 12 compiled glibc 2.36's `__libc_malloc` with a different frame and register allocation
from 2.39/2.40 (`X86sim.Gcc13`), so its prologue, checks, count test and epilogue are stepped
here; the heap block is the generic `tcache_get` (`V236.mallocTcGet`, bin in `rbp`).

* `prologue` (`0x0`–`0xb`): `push r12; push rbp; push rbx; mov rdi,rbx; sub $0x10,rsp`;
* `checks` (`0xb`–`0x5a`): `__malloc_initialized`, the sign of the request, the bin `tcIdx n`
  into `rbp`, the thread's tcache pointer through the GOT slot of its TLS offset (via `r12`),
  `tc_idx < mp_.tcache_bins`; on to the count test at `0x140`;
* `countTest` (`0x140`–`0x14d`); `epilogue` (`0x17a`–`0x182`).

They touch no heap state (writes: the three stack slots only).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN subFlagsN logicFlagsN Mem)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.Malloc
namespace Silmaril.Libc.Ptmalloc.Versions.V236
variable {A : Word}
set_option maxRecDepth 100000

theorem d0 : Str9Fs.decode ((mallocCode.drop 0).take 2) = some (ix (.push .r12), 2) := by decide
theorem d2 : Str9Fs.decode ((mallocCode.drop 2).take 1) = some (ix (.push .rbp), 1) := by decide
theorem d3 : Str9Fs.decode ((mallocCode.drop 3).take 1) = some (ix (.push .rbx), 1) := by decide
theorem d4 : Str9Fs.decode ((mallocCode.drop 4).take 3) = some (ix (.mov .q (.reg .rbx) .rdi), 3) := by decide
theorem d7 : Str9Fs.decode ((mallocCode.drop 7).take 4) =
    some (ix (.aluI8 .q .sub (.reg .rsp) 0x10#8), 4) := by decide
theorem d11 : Str9Fs.decode ((mallocCode.drop 11).take 7) =
    some (ix (.cmpI8 (.mem (Ext.Mem.ofRip 0x141b46#32)) 0#8), 7) := by decide
theorem d18 : Str9Fs.decode ((mallocCode.drop 18).take 6) = some (ix (.jcc .e 0x1f8#32), 6) := by decide
theorem d24 : Str9Fs.decode ((mallocCode.drop 24).take 3) = some (ix (.test .q (.reg .rbx) .rbx), 3) := by decide
theorem d27 : Str9Fs.decode ((mallocCode.drop 27).take 6) = some (ix (.jcc .s 0x1fd#32), 6) := by decide
theorem d33 : Str9Fs.decode ((mallocCode.drop 33).take 4) =
    some (ix (.lea .q .rax (Ext.Mem.ofReg .rbx none 0x17#32)), 4) := by decide
theorem d37 : Str9Fs.decode ((mallocCode.drop 37).take 2) = some (ix (.alu .d .xor (.reg .rbp) .rbp), 2) := by decide
theorem d39 : Str9Fs.decode ((mallocCode.drop 39).take 4) =
    some (ix (.aluI8 .q .cmp (.reg .rax) 0x1f#8), 4) := by decide
theorem d43 : Str9Fs.decode ((mallocCode.drop 43).take 2) = some (ix (.jcc8 .be 0x0c#8), 2) := by decide
theorem d45 : Str9Fs.decode ((mallocCode.drop 45).take 4) =
    some (ix (.aluI8 .q .and (.reg .rax) 0xf0#8), 4) := by decide
theorem d49 : Str9Fs.decode ((mallocCode.drop 49).take 4) =
    some (ix (.lea .q .rbp (Ext.Mem.ofReg .rax none 0xffffffef#32)), 4) := by decide
theorem d53 : Str9Fs.decode ((mallocCode.drop 53).take 4) =
    some (ix (.shift .q .shr (.reg .rbp) (.imm 0x04#8)), 4) := by decide
theorem d57 : Str9Fs.decode ((mallocCode.drop 57).take 7) =
    some (ix (.load .q .r12 (Ext.Mem.ofRip 0x13a408#32)), 7) := by decide
theorem d64 : Str9Fs.decode ((mallocCode.drop 64).take 5) =
    some (.new (.fs (.ext8 (.base (.load .q .rdx (Mem.fsAt 0#32)))) (Ext.Mem.ofReg .r12 none 0#32)), 5) := by
  decide
theorem d69 : Str9Fs.decode ((mallocCode.drop 69).take 3) = some (ix (.test .q (.reg .rdx) .rdx), 3) := by decide
theorem d72 : Str9Fs.decode ((mallocCode.drop 72).take 6) = some (ix (.jcc .e 0xba#32), 6) := by decide
theorem d78 : Str9Fs.decode ((mallocCode.drop 78).take 7) =
    some (ix (.aluR .q .cmp .rbp (.mem (Ext.Mem.ofRip 0x13aa23#32))), 7) := by decide
theorem d85 : Str9Fs.decode ((mallocCode.drop 85).take 6) = some (ix (.jcc .b 0xe5#32), 6) := by decide
theorem d320 : Str9Fs.decode ((mallocCode.drop 320).take 4) =
    some (ix (.movx false .d .w .rcx (.mem (Ext.Mem.ofReg .rdx (some ⟨.rbp, 1#2, by decide⟩) 0#32))), 4) := by
  decide
theorem d324 : Str9Fs.decode ((mallocCode.drop 324).take 3) =
    some (.str9 (.ext9 (.new (.test16 (.reg .rcx) .rcx))), 3) := by decide
theorem d327 : Str9Fs.decode ((mallocCode.drop 327).take 6) = some (ix (.jcc .e 0xffffff0e#32), 6) := by decide
theorem d378 : Str9Fs.decode ((mallocCode.drop 378).take 4) =
    some (ix (.aluI8 .q .add (.reg .rsp) 0x10#8), 4) := by decide
theorem d382 : Str9Fs.decode ((mallocCode.drop 382).take 1) = some (ix (.pop .rbx), 1) := by decide
theorem d383 : Str9Fs.decode ((mallocCode.drop 383).take 1) = some (ix (.pop .rbp), 1) := by decide
theorem d384 : Str9Fs.decode ((mallocCode.drop 384).take 2) = some (ix (.pop .r12), 2) := by decide
theorem d386 : Str9Fs.decode ((mallocCode.drop 386).take 1) = some (ix .ret, 1) := by decide

set_option maxHeartbeats 4000000 in
/-- **The prologue** (offsets `0x0`–`0xb`): three pushes into the slots `sp - 8` (`r12`),
`sp - 16` (`rbp`), `sp - 24` (`rbx`), the request into `rbx`, the frame. -/
theorem prologue {m : MState} {sp : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp) (hsp : 32 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 32) 32)
    (hr : m.memory.Permitted .read (sp.toNat - 32) 32)
    (hcode : ∀ i < mallocCode.length, ¬ stk sp (A.toNat + i)) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 11 ∧
      m'.core.read .rsp = sp - 0x28#64 ∧ m'.core.read .rbx = m.core.read .rdi ∧
      (∀ r, r ≠ .rsp → r ≠ .rbx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (stk sp) ∧
      m'.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [m.core.read .rbx]) := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hw hr ⊢
  refine ex_push (k := 0) hl hrip (by rw [mallocCode_length]; decide) d0 (by decide) hsp (by simp [hrsp]) hw hr hcode
    (fun mem1 hw1 hb1 hw1' hr1' hl1 => ?_)
  refine ex_push (k := 1) hl1 (by simp [hrip, rip_add]) (by rw [mallocCode_length]; decide) d2 (by decide) hsp
    (by simp [hrsp]) hw1' hr1' hcode (fun mem2 hw2 hb2 hw2' hr2' hl2 => ?_)
  refine ex_push (k := 2) hl2 (by simp [hrip, rip_add]) (by rw [mallocCode_length]; decide) d3 (by decide) hsp
    (by simp [hrsp]; bv_omega) hw2' hr2' hcode (fun mem3 hw3 hb3 hw3' hr3' hl3 => ?_)
  refine ex_head (stepC mallocCode_length (o := 4) (l := 3) hl3 (by simp [hrip, rip_add]) (by decide) d4 exec_movrr) ?_
  refine ex_fC mallocCode_length hl3 (by simp [hrip, rip_add]) (by decide) d7 exec_subrsp (fun f => ?_)
  have e10 : (0x10#8).signExtend 64 = 0x10#64 := by decide
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp [hrsp, e10]; bv_omega
  · simp
  · intro r h1 h2; simp [Silmaril.X86.State.read_write, h1, h2]
  · rfl
  · exact ((hw1.mono fun a h => slot_stk (by decide) hsp h).trans
      (hw2.mono fun a h => slot_stk (by decide) hsp h)).trans
      (hw3.mono fun a h => slot_stk (by decide) hsp h)
  · have := rd_ww hw3 (fun i hi h => slot_apart (k := 0) (j := 2) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
      (rd_ww hw2 (fun i hi h => slot_apart (k := 0) (j := 1) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb1)
    simpa using this
  · have := rd_ww hw3 (fun i hi h => slot_apart (k := 1) (j := 2) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb2
    simpa using this
  · simpa using hb3

set_option maxHeartbeats 4000000 in
/-- The second half of the checks (offsets `0x39`–`0x5a`): the tcache pointer, its test, the
bin bound; on to the count test at `0x140`. -/
theorem checks2 {m : MState} {off tc idx : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 57) (hrbp : m.core.read .rbp = idx)
    (hgot : loadN m.memory (A + 0x13a448#64) 8 = some off)
    (htc : loadN m.memory (m.core.fsBase + off) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + 0x13aa78#64) 8 = some 64#64) (hidx : idx.toNat < 64) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 320 ∧
      m'.core.read .rbp = idx ∧ m'.core.read .rdx = tc ∧
      (∀ r, r ≠ .r12 → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrbp hgot htc hbins ⊢
  have a57 : c0.rip + BitVec.ofNat 64 7 + (0x13a408#32).signExtend 64 = A + 0x13a448#64 := by
    rw [hrip]; simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, rip_add, BitVec.add_assoc]
  refine ex_head (stepC mallocCode_length (o := 57) (l := 7) hl hrip (by decide) d57 (exec_loadrip (by rw [a57]; exact hgot))) ?_
  refine ex_head (stepC mallocCode_length (o := 64) (l := 5) hl (by simp [hrip, rip_add]) (by decide) d64
    (exec_fsload (by simpa using htc))) ?_
  refine ex_head (stepC mallocCode_length (o := 69) (l := 3) hl (by simp [hrip, rip_add]) (by decide) d69 exec_testrr) ?_
  refine ex_head (stepC mallocCode_length (o := 72) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d72
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]; exact htc0))) ?_
  refine ex_head (stepC mallocCode_length (o := 78) (l := 7) hl (by simp [hrip, rip_add]) (by decide) d78
    (exec_cmprip (v := 64#64) (by simp [hrip, BitVec.add_assoc]; exact hbins))) ?_
  refine ex_head (stepC mallocCode_length (o := 85) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d85
    (exec_jcc (b := true) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbp, BitVec.ult]
      exact hidx))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip]; simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, rip_add, BitVec.add_assoc]
  · simp [hrbp]
  · simp
  · intro r h1 h2; simp [h1, h2]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- **The checks** (offsets `0xb`–`0x5a`): initialised, `n ≥ 0`, the index into `rbp`, the
tcache pointer from TLS, `idx < mp_.tcache_bins`; on to the count test at `0x140`. -/
theorem checks {m : MState} {n off tc : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 11) (hrbx : m.core.read .rbx = n) (hn : n.msb = false)
    (hinit : loadN m.memory (A + 0x141b58#64) 1 = some 1#64)
    (hgot : loadN m.memory (A + 0x13a448#64) 8 = some off)
    (htc : loadN m.memory (m.core.fsBase + off) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + 0x13aa78#64) 8 = some 64#64) (hidx : (tcIdx n).toNat < 64) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 320 ∧
      m'.core.read .rbp = tcIdx n ∧ m'.core.read .rdx = tc ∧
      (∀ r, r ≠ .rax → r ≠ .rbp → r ≠ .r12 → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrbx hinit hgot htc hbins ⊢
  have a11 : (Silmaril.X86.Ext.Mem.ofRip 0x141b46#32).addr c0 (c0.rip + BitVec.ofNat 64 7) = A + 0x141b58#64 := by
    rw [hrip]; simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, rip_add, BitVec.add_assoc]
  refine ex_head (stepC mallocCode_length (o := 11) (l := 7) hl hrip (by decide) d11 (exec_cmpI8m (v := 1#64) (by rw [a11]; exact hinit))) ?_
  refine ex_head (stepC mallocCode_length (o := 18) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d18
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.isZeroN]))) ?_
  refine ex_head (stepC mallocCode_length (o := 24) (l := 3) hl (by simp [hrip, rip_add]) (by decide) d24 exec_testrr) ?_
  refine ex_head (stepC mallocCode_length (o := 27) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d27
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, hrbx, hn]))) ?_
  refine ex_head (stepC mallocCode_length (o := 33) (l := 4) hl (by simp [hrip, rip_add]) (by decide) d33 exec_lea) ?_
  refine ex_fC mallocCode_length hl (by simp [hrip, rip_add]) (by decide) d37 exec_xor32 (fun f1 => ?_)
  refine ex_head (stepC mallocCode_length (o := 39) (l := 4) hl (by simp [hrip, rip_add]) (by decide) d39 exec_cmpI8r) ?_
  have e1f : (0x1f#8).signExtend 64 = 0x1f#64 := by decide
  by_cases hs : (n + 0x17#64).toNat ≤ 0x1f
  · refine ex_head (stepC mallocCode_length (o := 43) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d43
      (exec_jcc8 (b := true) (by
        simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbx, BitVec.ult,
          e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN]
        rcases Nat.lt_or_ge ((BitVec.toNat n + 23) % 18446744073709551616) 31 with h | h
        · simp [h]
        · have h2 : (n + 23#64 - 31#64 == 0#64) = true := by
            simp only [beq_iff_eq]; simp only [BitVec.toNat_add] at hs; bv_omega
          simp only [h2]
          generalize decide ((BitVec.toNat n + 23) % 18446744073709551616 < 31) = d; cases d <;> rfl))) ?_
    refine ex_of (checks2 (off := off) (tc := tc) (idx := 0) hl
      (by simp [hrip, rip_add, BitVec.add_assoc]) (by simp) hgot (by simpa using htc) htc0 hbins (by decide)) ?_
    rintro m' ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, ?_, h3, ?_, ?_, h6⟩
    · rw [h2]; unfold tcIdx; split
      · rfl
      · rename_i hne; exact absurd hs hne
    · intro r a b c d; rw [h4 r c d]; simp [a, b]
    · rw [h5]; rfl
  · refine ex_head (stepC mallocCode_length (o := 43) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d43
      (exec_jcc8 (b := false) (by
        simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbx, BitVec.ult,
          e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN]
        have h1 : ¬ ((BitVec.toNat n + 23) % 18446744073709551616 < 31) := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hs; omega
        have h2 : (n + 23#64 - 31#64 == 0#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hs; bv_omega
        simp [h1, h2]))) ?_
    refine ex_fC mallocCode_length hl (by simp [hrip, rip_add]) (by decide) d45 (exec_aluI8r (op := .and) (by decide)) (fun f2 => ?_)
    refine ex_head (stepC mallocCode_length (o := 49) (l := 4) hl (by simp [hrip, rip_add]) (by decide) d49 exec_lea) ?_
    refine ex_fC mallocCode_length hl (by simp [hrip, rip_add]) (by decide) d53 exec_shr (fun f3 => ?_)
    have ef0 : (0xf0#8).signExtend 64 = 0xfffffffffffffff0#64 := by decide
    have eef : ∀ x : Word, x + (0xffffffef#32).signExtend 64 = x - 0x11#64 := by
      intro x; rw [show (0xffffffef#32).signExtend 64 = 0 - 0x11#64 by decide]; bv_omega
    refine ex_of (checks2 (off := off) (tc := tc) (idx := tcIdx n) hl
      (by simp [hrip, rip_add, BitVec.add_assoc]) ?_ hgot (by simpa using htc) htc0 hbins hidx) ?_
    · simp [Silmaril.X86.Ext.AluOp.resultN, ef0, eef, hrbx, tcIdx, hs]
      have hs' : ¬ ((BitVec.toNat n + 23) % 18446744073709551616 ≤ 31) := by
        simpa [BitVec.toNat_add] using hs
      simp only [hs', ↓reduceIte]
      have e17 : ∀ x : Word, x + 18446744073709551599#64 = x - 17#64 := fun x => by bv_omega
      rw [e17]
    rintro m' ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, ?_, h6⟩
    · intro r a b c d; rw [h4 r c d]; simp [a, b]
    · rw [h5]; rfl

set_option maxHeartbeats 4000000 in
/-- **The bin's count test** (offsets `0x140`–`0x14c`): `counts[i] > 0`, on to `tcache_get`. -/
theorem countTest {m : MState} {tc idx cnt : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 320) (hrdx : m.core.read .rdx = tc)
    (hrbp : m.core.read .rbp = idx)
    (hcnt : loadN m.memory (tc + (idx <<< 1)) 2 = some cnt) (hcnt0 : cnt.setWidth 16 ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 333 ∧
      m'.core.read .rcx = ((cnt.setWidth 16).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rcx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdx hrbp hcnt ⊢
  refine ex_head (stepC mallocCode_length (o := 320) (l := 4) hl hrip (by decide) d320
    (exec_movzw (v := cnt) (by rw [hrdx, hrbp]; exact hcnt))) ?_
  refine ex_head (stepC mallocCode_length (o := 324) (l := 3) hl (by simp [hrip, rip_add]) (by decide)
    d324 exec_test16) ?_
  refine ex_head (stepC mallocCode_length (o := 327) (l := 6) hl (by simp [hrip, rip_add]) (by decide)
    d327 (exec_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]
      exact hcnt0))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, rfl, rfl⟩
  · simp [hrip, rip_add]
  · simp
  · intro r h; simp [h]

set_option maxHeartbeats 4000000 in
/-- **The epilogue** (offsets `0x17a`–`0x182`): the frame popped, return. -/
theorem epilogue {m : MState} {sp ret b0 b1 b2 : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 378) (hrsp : m.core.read .rsp = sp - 0x28#64)
    (hsp : 32 ≤ sp.toNat) (hsp2 : sp.toNat + 8 < 2 ^ 64)
    (hs2 : m.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [b2]))
    (hs1 : m.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [b1]))
    (hs0 : m.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [b0]))
    (hsr : m.memory.readBytes sp.toNat 8 = some (encodeWords [ret])) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = ret ∧ m'.core.read .rsp = sp + 8#64 ∧
      m'.core.read .rbx = b2 ∧ m'.core.read .rbp = b1 ∧ m'.core.read .r12 = b0 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hs2 hs1 hs0 hsr ⊢
  have e10 : (0x10#8).signExtend 64 = 0x10#64 := by decide
  refine ex_fC mallocCode_length hl (o := 378) (l := 4) hrip (by decide) d378
    (exec_aluI8r (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC mallocCode_length (o := 382) (l := 1) hl (by simp [hrip, rip_add]) (by decide) d382
    (exec_pop (v := b2) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e10, hrsp]
      convert hs2 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 383) (l := 1) hl (by simp [hrip, rip_add]) (by decide) d383
    (exec_pop (v := b1) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e10, hrsp]
      convert hs1 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 384) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d384
    (exec_pop (v := b0) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e10, hrsp]
      convert hs0 using 2; bv_omega))) ?_
  refine ex_head (stepC mallocCode_length (o := 386) (l := 1) hl (by simp [hrip, rip_add]) (by decide) d386
    (exec_ret (v := ret) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e10, hrsp]
      convert hsr using 2; bv_omega))) ?_
  refine ⟨_, Reaches.refl _ _, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [Silmaril.X86.Ext.AluOp.resultN, e10, hrsp]; bv_omega
  · simp
  · simp
  · simp
  · intro r a b c d; simp [a, b, c, d]

end Silmaril.Libc.Ptmalloc.Versions.V236
