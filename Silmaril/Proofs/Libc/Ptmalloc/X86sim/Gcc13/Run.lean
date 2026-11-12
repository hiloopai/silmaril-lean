module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.MallocKit

/-!
# ptmalloc x86sim, gcc 13/14: `__libc_malloc`'s tcache-hit path as a decode-fact bundle

`MallocSeq code dInit dGot dBins tInit tGot tBins oc`: the instructions of `__libc_malloc`'s
tcache-hit path as gcc 13/14 compiles glibc 2.39/2.40 (`endbr64`; frame `rbp`, `r13`, `r12`,
`rbx`; the bin in `r12`, the tcache in `rdx`): the prologue and checks at offsets `0`–`101`, whose
three rip-relative operands (`__malloc_initialized`, the GOT slot of `tcache`'s TLS offset,
`mp_.tcache_bins`) have displacements `dInit`, `dGot`, `dBins` and land at `A + tInit`,
`A + tGot`, `A + tBins`; the bin's count test at `oc`; the inlined `tcache_get` at `oc + 14`
(`X86sim.TcGetSeq`); the epilogue at `oc + 61`. The 2.39 and 2.40 listings of this path are
identical up to these displacements and `oc` (328 in 2.39, 336 in 2.40, where gcc 14 pads with a
longer `nop`).

The runs of the non-heap blocks are proved once, for every code carrying the bundle:
`prologue`, `checks`, `countTest`, `epilogue`. A pin proves `MallocSeq myCode …` by `decide`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN Mem subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.Malloc
namespace Silmaril.Libc.Ptmalloc.X86sim.Gcc13
variable {A : Word}
set_option maxRecDepth 100000

/-- **gcc 13/14's `__libc_malloc` tcache-hit path**, as decode facts of `code` (see the module
docstring for the parameters). -/
structure MallocSeq (code : List Byte) (dInit dGot dBins : BitVec 32) (tInit tGot tBins oc : Nat) :
    Prop where
  fit : oc + 72 ≤ code.length
  ge : 101 ≤ oc
  rInit : BitVec.ofNat 64 27 + dInit.signExtend 64 = BitVec.ofNat 64 tInit
  rGot : BitVec.ofNat 64 74 + dGot.signExtend 64 = BitVec.ofNat 64 tGot
  rBins : BitVec.ofNat 64 95 + dBins.signExtend 64 = BitVec.ofNat 64 tBins
  d0 : Str9Fs.decode ((code.drop 0).take 4) = some (ix .endbr64, 4)
  d4 : Str9Fs.decode ((code.drop 4).take 1) = some (ix (.push .rbp), 1)
  d5 : Str9Fs.decode ((code.drop 5).take 3) = some (ix (.mov .q (.reg .rbp) .rsp), 3)
  d8 : Str9Fs.decode ((code.drop 8).take 2) = some (ix (.push .r13), 2)
  d10 : Str9Fs.decode ((code.drop 10).take 2) = some (ix (.push .r12), 2)
  d12 : Str9Fs.decode ((code.drop 12).take 1) = some (ix (.push .rbx), 1)
  d13 : Str9Fs.decode ((code.drop 13).take 3) = some (ix (.mov .q (.reg .rbx) .rdi), 3)
  d16 : Str9Fs.decode ((code.drop 16).take 4) = some (ix (.aluI8 .q .sub (.reg .rsp) 0x18#8), 4)
  d20 : Str9Fs.decode ((code.drop 20).take 7) = some (ix (.cmpI8 (.mem (Ext.Mem.ofRip dInit)) 0#8), 7)
  d27 : ∃ rel, Str9Fs.decode ((code.drop 27).take 6) = some (ix (.jcc .e rel), 6)
  d33 : Str9Fs.decode ((code.drop 33).take 3) = some (ix (.test .q (.reg .rbx) .rbx), 3)
  d36 : ∃ rel, Str9Fs.decode ((code.drop 36).take 6) = some (ix (.jcc .s rel), 6)
  d42 : Str9Fs.decode ((code.drop 42).take 4) = some (ix (.lea .q .rax (Ext.Mem.ofReg .rbx none 0x17#32)), 4)
  d46 : Str9Fs.decode ((code.drop 46).take 3) = some (ix (.alu .d .xor (.reg .r12) .r12), 3)
  d49 : Str9Fs.decode ((code.drop 49).take 4) = some (ix (.aluI8 .q .cmp (.reg .rax) 0x1f#8), 4)
  d53 : Str9Fs.decode ((code.drop 53).take 2) = some (ix (.jcc8 .be 0x0c#8), 2)
  d55 : Str9Fs.decode ((code.drop 55).take 4) = some (ix (.aluI8 .q .and (.reg .rax) 0xf0#8), 4)
  d59 : Str9Fs.decode ((code.drop 59).take 4) =
    some (ix (.lea .q .r12 (Ext.Mem.ofReg .rax none 0xffffffef#32)), 4)
  d63 : Str9Fs.decode ((code.drop 63).take 4) = some (ix (.shift .q .shr (.reg .r12) (.imm 0x04#8)), 4)
  d67 : Str9Fs.decode ((code.drop 67).take 7) = some (ix (.load .q .r13 (Ext.Mem.ofRip dGot)), 7)
  d74 : Str9Fs.decode ((code.drop 74).take 5) =
    some (.new (.fs (.ext8 (.base (.load .q .rdx (Mem.fsAt 0#32)))) (Ext.Mem.ofReg .r13 none 0#32)), 5)
  d79 : Str9Fs.decode ((code.drop 79).take 3) = some (ix (.test .q (.reg .rdx) .rdx), 3)
  d82 : ∃ rel, Str9Fs.decode ((code.drop 82).take 6) = some (ix (.jcc .e rel), 6)
  d88 : Str9Fs.decode ((code.drop 88).take 7) = some (ix (.aluR .q .cmp .r12 (.mem (Ext.Mem.ofRip dBins))), 7)
  d95 : ∃ rel, Str9Fs.decode ((code.drop 95).take 6) = some (ix (.jcc .b rel), 6) ∧
    BitVec.ofNat 64 101 + rel.signExtend 64 = BitVec.ofNat 64 oc
  c0 : Str9Fs.decode ((code.drop oc).take 5) =
    some (ix (.movx false .d .w .rcx (.mem (Ext.Mem.ofReg .rdx (some ⟨.r12, 1#2, by decide⟩) 0#32))), 5)
  c5 : Str9Fs.decode ((code.drop (oc + 5)).take 3) =
    some (.str9 (.ext9 (.new (.test16 (.reg .rcx) .rcx))), 3)
  c8 : ∃ rel, Str9Fs.decode ((code.drop (oc + 8)).take 6) = some (ix (.jcc .e rel), 6)
  get : TcGetSeq code (oc + 14)
  e0 : Str9Fs.decode ((code.drop (oc + 61)).take 4) = some (ix (.aluI8 .q .add (.reg .rsp) 0x18#8), 4)
  e4 : Str9Fs.decode ((code.drop (oc + 65)).take 1) = some (ix (.pop .rbx), 1)
  e5 : Str9Fs.decode ((code.drop (oc + 66)).take 2) = some (ix (.pop .r12), 2)
  e7 : Str9Fs.decode ((code.drop (oc + 68)).take 2) = some (ix (.pop .r13), 2)
  e9 : Str9Fs.decode ((code.drop (oc + 70)).take 1) = some (ix (.pop .rbp), 1)
  e10 : Str9Fs.decode ((code.drop (oc + 71)).take 1) = some (ix .ret, 1)

variable {code : List Byte} {dInit dGot dBins : BitVec 32} {tInit tGot tBins oc : Nat}

set_option maxHeartbeats 4000000 in
theorem prologue (hq : MallocSeq code dInit dGot dBins tInit tGot tBins oc) {m : MState} {sp : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp) (hsp : 32 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 32) 32)
    (hr : m.memory.Permitted .read (sp.toNat - 32) 32)
    (hcode : ∀ i < code.length, ¬ stk sp (A.toNat + i)) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 20 ∧
      m'.core.read .rsp = sp - 0x38#64 ∧ m'.core.read .rbp = sp - 8#64 ∧
      m'.core.read .rbx = m.core.read .rdi ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rbx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (stk sp) ∧
      m'.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [m.core.read .r13]) ∧
      m'.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [m.core.read .rbx]) := by
  have hN : code.length = code.length := rfl
  have hf := hq.fit
  have hge := hq.ge
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hw hr ⊢
  refine ex_head (stepC hN (o := 0) (l := 4) hl hrip (by omega) hq.d0 exec_endbr) ?_
  refine ex_push (k := 0) hl (by simp [hrip]) (by omega) hq.d4 (by decide) hsp (by simp [hrsp]) hw hr hcode
    (fun mem1 hw1 hb1 hw1' hr1' hl1 => ?_)
  refine ex_head (stepC hN (o := 5) (l := 3) hl1 (by simp [hrip, rip_add]) (by omega) hq.d5 exec_movrr) ?_
  refine ex_push (k := 1) hl1 (by simp [hrip, rip_add]) (by omega) hq.d8 (by decide) hsp (by simp [hrsp]) hw1' hr1' hcode
    (fun mem2 hw2 hb2 hw2' hr2' hl2 => ?_)
  refine ex_push (k := 2) hl2 (by simp [hrip, rip_add]) (by omega) hq.d10 (by decide) hsp (by simp [hrsp]; bv_omega) hw2' hr2' hcode
    (fun mem3 hw3 hb3 hw3' hr3' hl3 => ?_)
  refine ex_push (k := 3) hl3 (by simp [hrip, rip_add]) (by omega) hq.d12 (by decide) hsp (by simp [hrsp]; bv_omega) hw3' hr3' hcode
    (fun mem4 hw4 hb4 hw4' hr4' hl4 => ?_)
  refine ex_head (stepC hN (o := 13) (l := 3) hl4 (by simp [hrip, rip_add]) (by omega) hq.d13 exec_movrr) ?_
  refine ex_fC hN hl4 (by simp [hrip, rip_add]) (by omega) hq.d16 exec_subrsp (fun f => ?_)
  have e18 : (0x18#8).signExtend 64 = 0x18#64 := by decide
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp [hrsp, e18]; bv_omega
  · simp [hrsp]
  · simp
  · intro r h1 h2 h3; simp [Silmaril.X86.State.read_write, h1, h2, h3]
  · rfl
  · exact (((hw1.mono fun a h => slot_stk (by decide) hsp h).trans
      (hw2.mono fun a h => slot_stk (by decide) hsp h)).trans
      (hw3.mono fun a h => slot_stk (by decide) hsp h)).trans
      (hw4.mono fun a h => slot_stk (by decide) hsp h)
  · have := rd_ww hw4 (fun i hi h => slot_apart (k := 0) (j := 3) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
      (rd_ww hw3 (fun i hi h => slot_apart (k := 0) (j := 2) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
        (rd_ww hw2 (fun i hi h => slot_apart (k := 0) (j := 1) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb1))
    simpa using this
  · have := rd_ww hw4 (fun i hi h => slot_apart (k := 1) (j := 3) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
      (rd_ww hw3 (fun i hi h => slot_apart (k := 1) (j := 2) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb2)
    simpa using this
  · have := rd_ww hw4 (fun i hi h => slot_apart (k := 2) (j := 3) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb3
    simpa using this
  · simpa using hb4

set_option maxHeartbeats 4000000 in
/-- The second half of the checks (offsets `0x43`–`0x64`). -/
theorem checks2 (hq : MallocSeq code dInit dGot dBins tInit tGot tBins oc) {m : MState} {off tc idx : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 67) (hr12 : m.core.read .r12 = idx)
    (hgot : loadN m.memory (A + BitVec.ofNat 64 tGot) 8 = some off)
    (htc : loadN m.memory (m.core.fsBase + off) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + BitVec.ofNat 64 tBins) 8 = some 64#64) (hidx : idx.toNat < 64) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 oc ∧
      m'.core.read .r12 = idx ∧ m'.core.read .rdx = tc ∧
      (∀ r, r ≠ .r13 → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  have hN : code.length = code.length := rfl
  have hf := hq.fit
  have hge := hq.ge
  obtain ⟨r82, d82⟩ := hq.d82
  obtain ⟨r95, d95, e95⟩ := hq.d95
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hr12 hgot htc hbins ⊢
  have a67 : c0.rip + BitVec.ofNat 64 7 + dGot.signExtend 64 = A + BitVec.ofNat 64 tGot := by
    rw [hrip]; exact ripRel hq.rGot
  refine ex_head (stepC hN (o := 67) (l := 7) hl hrip (by omega) hq.d67 (exec_loadrip (by rw [a67]; exact hgot))) ?_
  refine ex_head (stepC hN (o := 74) (l := 5) hl (by simp [hrip, rip_add]) (by omega) hq.d74
    (exec_fsload (by simpa using htc))) ?_
  refine ex_head (stepC hN (o := 79) (l := 3) hl (by simp [hrip, rip_add]) (by omega) hq.d79 exec_testrr) ?_
  refine ex_head (stepC hN (o := 82) (l := 6) hl (by simp [hrip, rip_add]) (by omega) d82
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]; exact htc0))) ?_
  refine ex_head (stepC hN (o := 88) (l := 7) hl (by simp [hrip, rip_add]) (by omega) hq.d88
    (exec_cmprip (v := 64#64) (by simp only [hrip, rip_add, Bool.false_eq_true, ↓reduceIte]; rw [ripRel' hq.rBins]; exact hbins))) ?_
  refine ex_head (stepC hN (o := 95) (l := 6) hl (by simp [hrip, rip_add]) (by omega) d95
    (exec_jcc (b := true) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hr12, BitVec.ult]
      exact hidx))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hrip, rip_add]; rw [ite_eq_right Bool.false_ne_true, rip_add, ripRel' e95, ite_eq_left trivial]
  · simp [hr12]
  · simp
  · intro r h1 h2; simp [h1, h2]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- **The checks** (offsets `0x14`–`0x64`): initialised, `n ≥ 0`, the index, the tcache
pointer from TLS, `idx < mp_.tcache_bins`; on to the tcache read at `0x148`. -/
theorem checks (hq : MallocSeq code dInit dGot dBins tInit tGot tBins oc) {m : MState} {n off tc : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 20) (hrbx : m.core.read .rbx = n) (hn : n.msb = false)
    (hinit : loadN m.memory (A + BitVec.ofNat 64 tInit) 1 = some 1#64)
    (hgot : loadN m.memory (A + BitVec.ofNat 64 tGot) 8 = some off)
    (htc : loadN m.memory (m.core.fsBase + off) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + BitVec.ofNat 64 tBins) 8 = some 64#64) (hidx : (tcIdx n).toNat < 64) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 oc ∧
      m'.core.read .r12 = tcIdx n ∧ m'.core.read .rdx = tc ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .r13 → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  have hN : code.length = code.length := rfl
  have hf := hq.fit
  have hge := hq.ge
  obtain ⟨r27, d27⟩ := hq.d27
  obtain ⟨r36, d36⟩ := hq.d36
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrbx hinit hgot htc hbins ⊢
  have a20 : (Silmaril.X86.Ext.Mem.ofRip dInit).addr c0 (c0.rip + BitVec.ofNat 64 7) = A + BitVec.ofNat 64 tInit := by
    have := ripRel (A := A) (o := 20) (l := 7) hq.rInit
    rw [hrip]
    simpa [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, rip_add, BitVec.add_assoc] using this
  refine ex_head (stepC hN (o := 20) (l := 7) hl hrip (by omega) hq.d20 (exec_cmpI8m (v := 1#64) (by rw [a20]; exact hinit))) ?_
  refine ex_head (stepC hN (o := 27) (l := 6) hl (by simp [hrip, rip_add]) (by omega) d27
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.isZeroN]))) ?_
  refine ex_head (stepC hN (o := 33) (l := 3) hl (by simp [hrip, rip_add]) (by omega) hq.d33 exec_testrr) ?_
  refine ex_head (stepC hN (o := 36) (l := 6) hl (by simp [hrip, rip_add]) (by omega) d36
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, hrbx, hn]))) ?_
  refine ex_head (stepC hN (o := 42) (l := 4) hl (by simp [hrip, rip_add]) (by omega) hq.d42 exec_lea) ?_
  refine ex_fC hN hl (by simp [hrip, rip_add]) (by omega) hq.d46 exec_xor32 (fun f1 => ?_)
  refine ex_head (stepC hN (o := 49) (l := 4) hl (by simp [hrip, rip_add]) (by omega) hq.d49 exec_cmpI8r) ?_
  have e1f : (0x1f#8).signExtend 64 = 0x1f#64 := by decide
  by_cases hs : (n + 0x17#64).toNat ≤ 0x1f
  · refine ex_head (stepC hN (o := 53) (l := 2) hl (by simp [hrip, rip_add]) (by omega) hq.d53
      (exec_jcc8 (b := true) (by
        simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbx, BitVec.ult,
          e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN]
        rcases Nat.lt_or_ge ((BitVec.toNat n + 23) % 18446744073709551616) 31 with h | h
        · simp [h]
        · have h2 : (n + 23#64 - 31#64 == 0#64) = true := by
            simp only [beq_iff_eq]; simp only [BitVec.toNat_add] at hs; bv_omega
          simp only [h2]
          generalize decide ((BitVec.toNat n + 23) % 18446744073709551616 < 31) = d; cases d <;> rfl))) ?_
    refine ex_of (checks2 hq (off := off) (tc := tc) (idx := 0) hl
      (by simp [hrip, rip_add, BitVec.add_assoc]) (by simp) hgot (by simpa using htc) htc0 hbins (by decide)) ?_
    rintro m' ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, ?_, h3, ?_, ?_, h6⟩
    · rw [h2]; unfold tcIdx; split
      · rfl
      · rename_i hne; exact absurd hs hne
    · intro r a b c d; rw [h4 r c d]; simp [a, b]
    · rw [h5]; rfl
  · refine ex_head (stepC hN (o := 53) (l := 2) hl (by simp [hrip, rip_add]) (by omega) hq.d53
      (exec_jcc8 (b := false) (by
        simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbx, BitVec.ult,
          e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN]
        have h1 : ¬ ((BitVec.toNat n + 23) % 18446744073709551616 < 31) := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hs; omega
        have h2 : (n + 23#64 - 31#64 == 0#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hs; bv_omega
        simp [h1, h2]))) ?_
    refine ex_fC hN hl (by simp [hrip, rip_add]) (by omega) hq.d55 (exec_aluI8r (op := .and) (by decide)) (fun f2 => ?_)
    refine ex_head (stepC hN (o := 59) (l := 4) hl (by simp [hrip, rip_add]) (by omega) hq.d59 exec_lea) ?_
    refine ex_fC hN hl (by simp [hrip, rip_add]) (by omega) hq.d63 exec_shr (fun f3 => ?_)
    have ef0 : (0xf0#8).signExtend 64 = 0xfffffffffffffff0#64 := by decide
    have eef : ∀ x : Word, x + (0xffffffef#32).signExtend 64 = x - 0x11#64 := by
      intro x; rw [show (0xffffffef#32).signExtend 64 = 0 - 0x11#64 by decide]; bv_omega
    refine ex_of (checks2 hq (off := off) (tc := tc) (idx := tcIdx n) hl
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
/-- **The bin's count test** (offsets `0x148`–`0x155`): `counts[i] > 0`, on to `tcache_get`. -/
theorem countTest (hq : MallocSeq code dInit dGot dBins tInit tGot tBins oc) {m : MState} {tc idx cnt : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 oc) (hrdx : m.core.read .rdx = tc)
    (hr12 : m.core.read .r12 = idx)
    (hcnt : loadN m.memory (tc + (idx <<< 1)) 2 = some cnt) (hcnt0 : cnt.setWidth 16 ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 (oc + 14) ∧
      m'.core.read .rcx = ((cnt.setWidth 16).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rcx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  have hN : code.length = code.length := rfl
  have hf := hq.fit
  obtain ⟨r8, c8⟩ := hq.c8
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdx hr12 hcnt ⊢
  refine ex_head (stepC hN (o := oc) (l := 5) hl hrip (by omega) hq.c0
    (exec_movzw (v := cnt) (by rw [hrdx, hr12]; exact hcnt))) ?_
  refine ex_head (stepC hN (o := oc + 5) (l := 3) hl (by simp [hrip, rip_add]) (by omega)
    hq.c5 exec_test16) ?_
  refine ex_head (stepC hN (o := oc + 8) (l := 6) hl (by simp [hrip, rip_add]) (by omega)
    c8 (exec_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]
      exact hcnt0))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, rfl, rfl⟩
  · simp [hrip, rip_add]
  · simp
  · intro r h; simp [h]

set_option maxHeartbeats 4000000 in
/-- **The epilogue** (offsets `0x185`–`0x18f`): the frame popped, return. -/
theorem epilogue (hq : MallocSeq code dInit dGot dBins tInit tGot tBins oc) {m : MState} {sp ret b0 b1 b2 b3 : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 (oc + 61)) (hrsp : m.core.read .rsp = sp - 0x38#64)
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
  have hN : code.length = code.length := rfl
  have hf := hq.fit
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hs3 hs2 hs1 hs0 hsr ⊢
  have e18 : (0x18#8).signExtend 64 = 0x18#64 := by decide
  refine ex_fC hN hl (o := oc + 61) (l := 4) hrip (by omega) hq.e0
    (exec_aluI8r (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC hN (o := oc + 65) (l := 1) hl (by simp [hrip, rip_add]) (by omega) hq.e4
    (exec_pop (v := b3) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs3 using 2; bv_omega))) ?_
  refine ex_head (stepC hN (o := oc + 66) (l := 2) hl (by simp [hrip, rip_add]) (by omega) hq.e5
    (exec_pop (v := b2) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs2 using 2; bv_omega))) ?_
  refine ex_head (stepC hN (o := oc + 68) (l := 2) hl (by simp [hrip, rip_add]) (by omega) hq.e7
    (exec_pop (v := b1) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs1 using 2; bv_omega))) ?_
  refine ex_head (stepC hN (o := oc + 70) (l := 1) hl (by simp [hrip, rip_add]) (by omega) hq.e9
    (exec_pop (v := b0) (by
      simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]
      convert hs0 using 2; bv_omega))) ?_
  refine ex_head (stepC hN (o := oc + 71) (l := 1) hl (by simp [hrip, rip_add]) (by omega) hq.e10
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

end Silmaril.Libc.Ptmalloc.X86sim.Gcc13
