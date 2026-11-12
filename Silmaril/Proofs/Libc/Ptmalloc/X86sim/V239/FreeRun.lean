module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreeDecode
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocRun

/-!
# ptmalloc x86sim, glibc 2.39: `__libc_free`'s entry and `_int_free`'s checks, as machine runs

The non-heap blocks of `free`'s tcache path with the memory abstract (loads, permissions and
apartness as hypotheses): the stack slots of the two frames (`fstk`), `free_pro`/`free_head`
(`__libc_free` up to the call), `int_pro` and `int_chk1a`…`int_chk3b` (`_int_free`'s checks).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN Mem Index RM Sz Narrow Cond subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239
set_option maxRecDepth 100000
/-! ## The two frames' stack slots -/

/-- The stack slots `[sp - 96, sp)` of `__libc_free`'s and `_int_free`'s frames. -/
def fstk (sp : Word) (a : Nat) : Prop := sp.toNat - 96 ≤ a ∧ a < sp.toNat

theorem slot_fstk {sp : Word} {k : Nat} (hk : k < 12) (hsp : 96 ≤ sp.toNat) {a : Nat}
    (h : slot sp k a) : fstk sp a := by unfold slot at h; unfold fstk; omega

theorem slot_apartF {sp : Word} {k j : Nat} (hkj : k ≠ j) (hsp : 96 ≤ sp.toNat) (hk : k < 12) (hj : j < 12) :
    ∀ i < 8, ¬ slot sp j (sp.toNat - 8 * (k + 1) + i) := by
  intro i hi ⟨h1, h2⟩; omega

theorem push_slotF {c : State} {mem : Memory} {v sp : Word} (k : Nat) (hk : k < 12)
    (hsp : 96 ≤ sp.toNat) (hrsp : c.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : mem.Permitted .write (sp.toNat - 96) 96) (hr : mem.Permitted .read (sp.toNat - 96) 96) :
    ∃ mem', Silmaril.X86.pushWord c mem v = some (c.write .rsp (c.read .rsp - 8#64), mem') ∧
      mem.WritesWithin mem' (slot sp k) ∧
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [v]) ∧
      mem'.Permitted .write (sp.toNat - 96) 96 ∧ mem'.Permitted .read (sp.toNat - 96) 96 := by
  have ha : (c.read .rsp - 8#64).toNat = sp.toNat - 8 * (k + 1) := by
    rw [hrsp]; bv_omega
  have hsub : ∀ {acc}, mem.Permitted acc (sp.toNat - 96) 96 → mem.Permitted acc (sp.toNat - 8 * (k + 1)) 8 := by
    intro acc h
    simp only [Memory.Permitted, Memory.checkSpan_iff] at h ⊢
    refine ⟨by omega, by omega, fun o ho => ?_⟩
    have := h.2.2 (96 - 8 * (k + 1) + o) (by omega)
    rwa [show sp.toNat - 96 + (96 - 8 * (k + 1) + o) = sp.toNat - 8 * (k + 1) + o by omega] at this
  have hp := Silmaril.X86.pushWord_eq_some (s := c) (value := v) (by rw [ha]; exact hsub hw)
  have wo := Silmaril.X86.pushWord_writesOnly hp
  rw [Memory.writesOnly_iff_writesWithin] at wo
  refine ⟨_, hp, ?_, ?_, ?_, ?_⟩
  · refine wo.mono ?_
    intro a ⟨h1, h2⟩; rw [ha] at h1 h2; exact ⟨h1, h2⟩
  · rw [← ha]; exact Silmaril.X86.pushWord_readBytes hp (by rw [ha]; exact hsub hr)
  · simpa [Memory.Permitted, Memory.checkSpan, Memory.permits] using hw
  · simpa [Memory.Permitted, Memory.checkSpan, Memory.permits] using hr

/-- **A push as a continuation**: into slot `k` of `fstk`. -/
theorem ex_pushC {code : List Byte} {N : Nat} (hN : code.length = N) {A : Word} {P : MState → Prop}
    {m : MState} {sp : Word} {k o l : Nat} {r : Reg}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o)
    (hfit : o + l ≤ N)
    (hdec : Str9Fs.decode ((code.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.push r)))), l))
    (hk : k < 12) (hsp : 96 ≤ sp.toNat) (hrsp : m.core.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (cont : ∀ mem', m.memory.WritesWithin mem' (slot sp k) →
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [m.core.read r]) →
      mem'.Permitted .write (sp.toNat - 96) 96 → mem'.Permitted .read (sp.toNat - 96) 96 →
      ∃ u, Reaches Str9Fs.step
        ⟨nx (m.core.write .rsp (m.core.read .rsp - 8#64)) (m.core.rip + BitVec.ofNat 64 l), mem'⟩ u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  obtain ⟨mem', hp, hw', hb, hw2, hr2⟩ := push_slotF (c := m.core) (mem := m.memory) (v := m.core.read r)
    k hk hsp hrsp hw hr
  exact ex_head (stepC hN hl hrip hfit hdec (exec_push hp)) (cont mem' hw' hb hw2 hr2)

set_option maxRecDepth 100000

/-- A load at an address given by an equation. -/
theorem ld_eq {mem : Memory} {a b : Word} {k : Nat} {v : Word} (h : a = b)
    (hl : loadN mem b k = some v) : loadN mem a k = some v := h ▸ hl

/-- A store at an address given by an equation. -/
theorem st_eq {mem mem' : Memory} {a b : Word} {k : Nat} {v w : Word} (h : a = b) (hv : v = w)
    (hs : storeN mem b k w = some mem') : storeN mem a k v = some mem' := h ▸ hv ▸ hs

set_option maxHeartbeats 4000000 in
/-- **The null test and the prologue** (offsets `0x0`–`0x1d`). -/
theorem free_pro {m : MState} {A sp p : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp)
    (hrdi : m.core.read .rdi = p) (hp : p ≠ 0) (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hcode : ∀ i < 272, ¬ fstk sp (A.toNat + i)) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 30 ∧
      m'.core.read .rsp = sp - 0x38#64 ∧ m'.core.read .rbp = sp - 8#64 ∧
      m'.core.read .r13 = p - 0x10#64 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .r13 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fstk sp) ∧
      m'.memory.Permitted .write (sp.toNat - 96) 96 ∧ m'.memory.Permitted .read (sp.toNat - 96) 96 ∧
      m'.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [m.core.read .r13]) ∧
      m'.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [m.core.read .rbx]) := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hrdi hw hr ⊢
  have cw : ∀ {mem mem' : Memory} {k : Nat}, k < 12 → Loaded mem A freeCode →
      mem.WritesWithin mem' (slot sp k) → Loaded mem' A freeCode := fun hk hl hw =>
    loadedC_ww freeCode_length hl hw (fun i hi h => hcode i hi (slot_fstk hk hsp h))
  refine ex_head (stepC freeCode_length (o := 0) (l := 4) hl hrip (by decide) f0 e_endbr) ?_
  refine ex_head (stepC freeCode_length (o := 4) (l := 3) hl (by simp [hrip, rip_add]) (by decide) f4
    e_testrr) ?_
  refine ex_head (stepC freeCode_length (o := 7) (l := 6) hl (by simp [hrip, rip_add]) (by decide) f7
    (e_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, hrdi]; exact hp))) ?_
  refine ex_pushC freeCode_length (k := 0) hl (by simp [hrip, rip_add]) (by decide) f13 (by decide) hsp
    (by simp [hrsp]) hw hr (fun mem1 hw1 hb1 hw1' hr1' => ?_)
  have hl1 := cw (by decide) hl hw1
  refine ex_head (stepC freeCode_length (o := 14) (l := 3) hl1 (by simp [hrip, rip_add]) (by decide) f14
    e_movrr) ?_
  refine ex_pushC freeCode_length (k := 1) hl1 (by simp [hrip, rip_add]) (by decide) f17 (by decide) hsp
    (by simp [hrsp]) hw1' hr1' (fun mem2 hw2 hb2 hw2' hr2' => ?_)
  have hl2 := cw (by decide) hl1 hw2
  refine ex_head (stepC freeCode_length (o := 19) (l := 4) hl2 (by simp [hrip, rip_add]) (by decide) f19
    e_lea) ?_
  refine ex_pushC freeCode_length (k := 2) hl2 (by simp [hrip, rip_add]) (by decide) f23 (by decide) hsp
    (by simp [hrsp]; bv_omega) hw2' hr2' (fun mem3 hw3 hb3 hw3' hr3' => ?_)
  have hl3 := cw (by decide) hl2 hw3
  refine ex_pushC freeCode_length (k := 3) hl3 (by simp [hrip, rip_add]) (by decide) f25 (by decide) hsp
    (by simp [hrsp]; bv_omega) hw3' hr3' (fun mem4 hw4 hb4 hw4' hr4' => ?_)
  have hl4 := cw (by decide) hl3 hw4
  refine ex_fC freeCode_length hl4 (by simp [hrip, rip_add]) (by decide) f26 e_subrsp (fun f => ?_)
  have e18 : (0x18#8).signExtend 64 = 0x18#64 := by decide
  have ef0 : (0xfffffff0#32).signExtend 64 = 0 - 0x10#64 := by decide
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp [hrsp, e18]; bv_omega
  · simp [hrsp]
  · simp [hrdi, ef0]; bv_omega
  · intro r h1 h2 h3; simp [Silmaril.X86.State.read_write, h1, h2, h3]
  · rfl
  · exact (((hw1.mono fun a h => slot_fstk (by decide) hsp h).trans
      (hw2.mono fun a h => slot_fstk (by decide) hsp h)).trans
      (hw3.mono fun a h => slot_fstk (by decide) hsp h)).trans
      (hw4.mono fun a h => slot_fstk (by decide) hsp h)
  · exact hw4'
  · exact hr4'
  · have := rd_ww hw4 (slot_apartF (k := 0) (j := 3) (by decide) hsp (by decide) (by decide))
      (rd_ww hw3 (slot_apartF (k := 0) (j := 2) (by decide) hsp (by decide) (by decide))
        (rd_ww hw2 (slot_apartF (k := 0) (j := 1) (by decide) hsp (by decide) (by decide)) hb1))
    simpa using this
  · have := rd_ww hw4 (slot_apartF (k := 1) (j := 3) (by decide) hsp (by decide) (by decide))
      (rd_ww hw3 (slot_apartF (k := 1) (j := 2) (by decide) hsp (by decide) (by decide)) hb2)
    simpa using this
  · have := rd_ww hw4 (slot_apartF (k := 2) (j := 3) (by decide) hsp (by decide) (by decide)) hb3
    simpa using this
  · simpa using hb4

/-- **A call as a continuation**: the return address pushed into slot `k` of `fstk`. -/
theorem ex_callC {code : List Byte} {N : Nat} (hN : code.length = N) {A : Word} {P : MState → Prop}
    {m : MState} {sp : Word} {k o l : Nat} {rel : BitVec 32}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o)
    (hfit : o + l ≤ N)
    (hdec : Str9Fs.decode ((code.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.call rel)))), l))
    (hk : k < 12) (hsp : 96 ≤ sp.toNat) (hrsp : m.core.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (cont : ∀ mem', m.memory.WritesWithin mem' (slot sp k) →
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [m.core.rip + BitVec.ofNat 64 l]) →
      mem'.Permitted .write (sp.toNat - 96) 96 → mem'.Permitted .read (sp.toNat - 96) 96 →
      ∃ u, Reaches Str9Fs.step
        ⟨nx (m.core.write .rsp (m.core.read .rsp - 8#64))
          (m.core.rip + BitVec.ofNat 64 l + rel.signExtend 64), mem'⟩ u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  obtain ⟨mem', hp, hw', hb, hw2, hr2⟩ := push_slotF (c := m.core) (mem := m.memory)
    (v := m.core.rip + BitVec.ofNat 64 l) k hk hsp hrsp hw hr
  exact ex_head (stepC hN hl hrip hfit hdec (fx_call hp)) (cont mem' hw' hb hw2 hr2)

set_option maxHeartbeats 4000000 in
/-- Offsets `0x1e`–`0x30`: `errno` saved in `r12d`, the size field read, not `IS_MMAPPED`. -/
theorem free_head1 {m : MState} {A p offE sz ev : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 30) (hrdi : m.core.read .rdi = p)
    (hgotE : loadN m.memory (A + 0x155fc8#64) 8 = some offE)
    (hsz : loadN m.memory (p - 8#64) 8 = some sz)
    (herr : loadN m.memory (m.core.fsBase + offE) 4 = some ev)
    (hmm : sz.setWidth 8 &&& 2#8 = 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 49 ∧
      m'.core.read .rbx = offE ∧ m'.core.read .rax = sz ∧
      m'.core.read .r12 = (ev.setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r12 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdi hgotE hsz herr ⊢
  refine ex_head (stepC freeCode_length (o := 30) (l := 7) hl hrip (by decide) f30
    (e_loadrip (ld_eq (by rw [hrip]; simp [rip_add, BitVec.add_assoc]) hgotE))) ?_
  refine ex_head (stepC freeCode_length (o := 37) (l := 4) hl (by simp [hrip, rip_add]) (by decide) f37
    (e_loadd (ld_eq (by simp [hrdi]; bv_omega) hsz))) ?_
  refine ex_head (stepC freeCode_length (o := 41) (l := 4) hl (by simp [hrip, rip_add]) (by decide) f41
    (e_fsload32 (ld_eq (by simp) herr))) ?_
  refine ex_head (stepC freeCode_length (o := 45) (l := 2) hl (by simp [hrip, rip_add]) (by decide) f45
    e_testA8) ?_
  refine ex_head (stepC freeCode_length (o := 47) (l := 2) hl (by simp [hrip, rip_add]) (by decide) f47
    (e_jcc8 (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot, hmm]))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp
  · simp
  · simp
  · intro r a b c; simp [a, b, c]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x31`–`0x42`: the tcache is non-null; on to `0x43` (`0xade73`). -/
theorem free_head2a {m : MState} {A offT tc : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 49)
    (hgotT : loadN m.memory (A + 0x155f68#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 67 ∧
      (∀ r, r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hgotT htc ⊢
  refine ex_head (stepC freeCode_length (o := 49) (l := 7) hl hrip (by decide) f49
    (e_loadrip (ld_eq (by rw [hrip]; simp [rip_add, BitVec.add_assoc]) hgotT))) ?_
  refine ex_head (stepC freeCode_length (o := 56) (l := 5) hl (by simp [hrip, rip_add]) (by decide) f56
    (e_fscmp0 (ld_eq (by simp) htc))) ?_
  refine ex_head (stepC freeCode_length (o := 61) (l := 6) hl (by simp [hrip, rip_add]) (by decide) f61
    (e_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.isZeroN]; exact htc0))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add, BitVec.add_assoc]
  · intro r a; simp [a]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x43`–`0x4d` (from `0xade73`): `rdi := &main_arena`, `NON_MAIN_ARENA` clear. -/
theorem free_head2b {m : MState} {A sz : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 67) (hrax : m.core.read .rax = sz)
    (hna : sz.setWidth 8 &&& 4#8 = 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 116 ∧
      m'.core.read .rdi = A + 0x156c90#64 ∧
      (∀ r, r ≠ .rdi → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrax ⊢
  refine ex_head (stepC freeCode_length (o := 67) (l := 7) hl hrip (by decide) f67
    e_learip) ?_
  refine ex_head (stepC freeCode_length (o := 74) (l := 2) hl (by simp [hrip, rip_add]) (by decide) f74
    e_testA8) ?_
  refine ex_head (stepC freeCode_length (o := 76) (l := 2) hl (by simp [hrip, rip_add]) (by decide) f76
    (e_jcc8 (b := true) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, hrax, hna]))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add, BitVec.add_assoc]
  · simp [hrip, rip_add, BitVec.add_assoc]
  · intro r a; simp [a]
  · rfl
  · rfl

/-- Offsets `0x31`–`0x4d`: the tcache is non-null, `rdi := &main_arena`, `NON_MAIN_ARENA`
clear (`free_head2a`, `free_head2b`). -/
theorem free_head2 {m : MState} {A sz offT tc : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 49) (hrax : m.core.read .rax = sz)
    (hna : sz.setWidth 8 &&& 4#8 = 0)
    (hgotT : loadN m.memory (A + 0x155f68#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 116 ∧
      m'.core.read .rdi = A + 0x156c90#64 ∧
      (∀ r, r ≠ .rdx → r ≠ .rdi → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨m1, r1, rip1, fr1, fs1, mem1⟩ := free_head2a hl hrip hgotT htc htc0
  have hl1 : Loaded m1.memory A freeCode := by rw [mem1]; exact hl
  obtain ⟨m2, r2, rip2, rdi2, fr2, fs2, mem2⟩ :=
    free_head2b hl1 rip1 (by rw [fr1 _ (by decide)]; exact hrax) hna
  exact ⟨m2, r1.trans r2, rip2, rdi2, fun r a b => by rw [fr2 r b, fr1 r a],
    by rw [fs2, fs1], by rw [mem2, mem1]⟩

set_option maxHeartbeats 4000000 in
/-- Offsets `0x74`–`0x79`: `_int_free (&main_arena, p - 16, 0)`, the return address in
slot 7. -/
theorem free_head3 {m : MState} {A sp : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 116) (hrsp : m.core.read .rsp = sp - 0x38#64)
    (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A - 0x2be0#64 ∧
      m'.core.read .rsp = sp - 0x40#64 ∧ m'.core.read .rsi = m.core.read .r13 ∧ m'.core.read .rdx = 0 ∧
      (∀ r, r ≠ .rdx → r ≠ .rsi → r ≠ .rsp → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (slot sp 7) ∧
      m'.memory.Permitted .write (sp.toNat - 96) 96 ∧ m'.memory.Permitted .read (sp.toNat - 96) 96 ∧
      m'.memory.readBytes (sp.toNat - 64) 8 = some (encodeWords [A + 126#64]) := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hw hr ⊢
  refine ex_head (stepC freeCode_length (o := 116) (l := 3) hl hrip (by decide) f116 e_movrr) ?_
  refine ex_fC freeCode_length hl (by simp [hrip, rip_add]) (by decide) f119 e_xor32 (fun f => ?_)
  refine ex_callC freeCode_length (k := 7) hl (by simp [hrip, rip_add]) (by decide) f121 (by decide) hsp
    (by simp [hrsp]) hw hr (fun mem1 hw1 hb1 hw1' hr1' => ?_)
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add, BitVec.add_assoc]; bv_omega
  · exact (congrArg (· - 8#64) hrsp).trans (by bv_omega)
  · rfl
  · rfl
  · intro r a b c
    dsimp only
    rw [nx_read, Silmaril.X86.State.read_write_other _ _ _ _ c, nxf_read,
      Silmaril.X86.State.read_write_other _ _ _ _ a, nx_read, Silmaril.X86.State.read_write_other _ _ _ _ b]
  · rfl
  · exact hw1
  · exact hw1'
  · exact hr1'
  · simpa [hrip, rip_add] using hb1

/-- **The checks and the call** (offsets `0x1e`–`0x79`): `errno` saved in `r12d`, the size
field read (neither `IS_MMAPPED` nor `NON_MAIN_ARENA`), the tcache non-null, then
`_int_free (&main_arena, p - 16, 0)` with the return address in slot 7. -/
theorem free_head {m : MState} {A sp p offE sz ev offT tc : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 30) (hrsp : m.core.read .rsp = sp - 0x38#64)
    (hrdi : m.core.read .rdi = p) (hr13 : m.core.read .r13 = p - 0x10#64) (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hgotE : loadN m.memory (A + 0x155fc8#64) 8 = some offE)
    (hsz : loadN m.memory (p - 8#64) 8 = some sz)
    (herr : loadN m.memory (m.core.fsBase + offE) 4 = some ev)
    (hmm : sz.setWidth 8 &&& 2#8 = 0) (hna : sz.setWidth 8 &&& 4#8 = 0)
    (hgotT : loadN m.memory (A + 0x155f68#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A - 0x2be0#64 ∧
      m'.core.read .rsp = sp - 0x40#64 ∧ m'.core.read .rdi = A + 0x156c90#64 ∧
      m'.core.read .rsi = p - 0x10#64 ∧ m'.core.read .rdx = 0 ∧ m'.core.read .rbx = offE ∧
      m'.core.read .r12 = (ev.setWidth 32).setWidth 64 ∧ m'.core.read .r13 = p - 0x10#64 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → r ≠ .r12 → r ≠ .rsp →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (slot sp 7) ∧
      m'.memory.Permitted .write (sp.toNat - 96) 96 ∧ m'.memory.Permitted .read (sp.toNat - 96) 96 ∧
      m'.memory.readBytes (sp.toNat - 64) 8 = some (encodeWords [A + 126#64]) := by
  obtain ⟨m1, r1, rip1, rbx1, rax1, r12_1, fr1, fs1, mem1⟩ :=
    free_head1 hl hrip hrdi hgotE hsz herr hmm
  rw [← mem1] at hl hgotT
  obtain ⟨m2, r2, rip2, rdi2, fr2, fs2, mem2⟩ :=
    free_head2 hl rip1 rax1 hna hgotT (by rw [fs1, mem1]; exact htc) htc0
  rw [← mem2] at hl
  obtain ⟨m3, r3, rip3, rsp3, rsi3, rdx3, fr3, fs3, ww3, pw3, pr3, rb3⟩ :=
    free_head3 hl rip2 (by rw [fr2 _ (by decide) (by decide), fr1 _ (by decide) (by decide) (by decide), hrsp])
      hsp (by rw [mem2, mem1]; exact hw) (by rw [mem2, mem1]; exact hr)
  refine ⟨m3, (r1.trans r2).trans r3, rip3, rsp3, ?_, ?_, rdx3, ?_, ?_, ?_, ?_, ?_, ?_, pw3, pr3, rb3⟩
  · rw [fr3 _ (by decide) (by decide) (by decide), rdi2]
  · rw [rsi3, fr2 _ (by decide) (by decide), fr1 _ (by decide) (by decide) (by decide), hr13]
  · rw [fr3 _ (by decide) (by decide) (by decide), fr2 _ (by decide) (by decide), rbx1]
  · rw [fr3 _ (by decide) (by decide) (by decide), fr2 _ (by decide) (by decide), r12_1]
  · rw [fr3 _ (by decide) (by decide) (by decide), fr2 _ (by decide) (by decide),
      fr1 _ (by decide) (by decide) (by decide), hr13]
  · intro r a b c d e f g
    rw [fr3 _ c e g, fr2 _ c d, fr1 _ a b f]
  · rw [fs3, fs2, fs1]
  · rw [mem2, mem1] at ww3; exact ww3

set_option maxRecDepth 100000

/-! The carry and zero flags of a subtraction, without unfolding the parity. -/

theorem cf_sub (x y : Word) : (subFlagsN x y).carry = some (decide (x.toNat < y.toNat)) := by
  simp only [subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult]
theorem zf_sub (x y : Word) : (subFlagsN x y).zero = some (decide (x = y)) := by
  simp only [subFlagsN, Silmaril.X86.Ext.isZeroN, Option.some.injEq]
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false]
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; exact h (by bv_omega)

set_option maxHeartbeats 4000000 in
/-- **`_int_free`'s prologue** (offsets `0x0`–`0xf`): slots 8–11 below the entry `sp` of
`__libc_free`. -/
theorem int_pro {m : MState} {B sp : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp - 0x40#64)
    (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hcode : ∀ i < 897, ¬ fstk sp (B.toNat + i)) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 16 ∧
      m'.core.read .rsp = sp - 0x88#64 ∧
      m'.core.read .r12 = ((m.core.read .rdx).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .r12 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fun a => sp.toNat - 96 ≤ a ∧ a < sp.toNat - 64) ∧
      m'.memory.readBytes (sp.toNat - 72) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 80) 8 = some (encodeWords [m.core.read .r13]) ∧
      m'.memory.readBytes (sp.toNat - 88) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 96) 8 = some (encodeWords [m.core.read .rbx]) := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hw hr ⊢
  have cw : ∀ {mem mem' : Memory} {k : Nat}, k < 12 → Loaded mem B intFreeCode →
      mem.WritesWithin mem' (slot sp k) → Loaded mem' B intFreeCode := fun hk hl hw =>
    loadedC_ww intFreeCode_length hl hw (fun i hi h => hcode i hi (slot_fstk hk hsp h))
  refine ex_pushC intFreeCode_length (k := 8) hl hrip (by decide) i0 (by decide) hsp
    (by simp [hrsp]) hw hr (fun mem1 hw1 hb1 hw1' hr1' => ?_)
  have hl1 := cw (by decide) hl hw1
  refine ex_head (stepC intFreeCode_length (o := 1) (l := 3) hl1 (by simp [hrip, rip_add]) (by decide) i1
    e_movrr) ?_
  refine ex_pushC intFreeCode_length (k := 9) hl1 (by simp [hrip, rip_add]) (by decide) i4 (by decide) hsp
    (by simp [hrsp]; bv_omega) hw1' hr1' (fun mem2 hw2 hb2 hw2' hr2' => ?_)
  have hl2 := cw (by decide) hl1 hw2
  refine ex_pushC intFreeCode_length (k := 10) hl2 (by simp [hrip, rip_add]) (by decide) i6 (by decide) hsp
    (by simp [hrsp]; bv_omega) hw2' hr2' (fun mem3 hw3 hb3 hw3' hr3' => ?_)
  have hl3 := cw (by decide) hl2 hw3
  refine ex_head (stepC intFreeCode_length (o := 8) (l := 3) hl3 (by simp [hrip, rip_add]) (by decide) i8
    e_mov32) ?_
  refine ex_pushC intFreeCode_length (k := 11) hl3 (by simp [hrip, rip_add]) (by decide) i11 (by decide) hsp
    (by simp [hrsp]; bv_omega) hw3' hr3' (fun mem4 hw4 hb4 hw4' hr4' => ?_)
  have hl4 := cw (by decide) hl3 hw4
  refine ex_fC intFreeCode_length hl4 (by simp [hrip, rip_add]) (by decide) i12 e_subrsp (fun f => ?_)
  have e28 : (0x28#8).signExtend 64 = 0x28#64 := by decide
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp [hrsp, e28]; bv_omega
  · simp
  · intro r h1 h2 h3; simp [Silmaril.X86.State.read_write, h1, h2, h3]
  · rfl
  · exact (((hw1.mono fun a h => by unfold slot at h; omega).trans
      (hw2.mono fun a h => by unfold slot at h; omega)).trans
      (hw3.mono fun a h => by unfold slot at h; omega)).trans
      (hw4.mono fun a h => by unfold slot at h; omega)
  · have := rd_ww hw4 (slot_apartF (k := 8) (j := 11) (by decide) hsp (by decide) (by decide))
      (rd_ww hw3 (slot_apartF (k := 8) (j := 10) (by decide) hsp (by decide) (by decide))
        (rd_ww hw2 (slot_apartF (k := 8) (j := 9) (by decide) hsp (by decide) (by decide)) hb1))
    simpa using this
  · have := rd_ww hw4 (slot_apartF (k := 9) (j := 11) (by decide) hsp (by decide) (by decide))
      (rd_ww hw3 (slot_apartF (k := 9) (j := 10) (by decide) hsp (by decide) (by decide)) hb2)
    simpa using this
  · have := rd_ww hw4 (slot_apartF (k := 10) (j := 11) (by decide) hsp (by decide) (by decide)) hb3
    simpa using this
  · simpa using hb4

/-- The chunk size `sz & ~7` of a size field. -/
def csize (sz : Word) : Word := sz &&& 0xfffffffffffffff8#64

set_option maxHeartbeats 4000000 in
/-- Offsets `0x10`–`0x29`: the size field, `size := sz & ~7`, `q ≤ -size`. -/
theorem int_chk1a {m : MState} {B q sz : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 16) (hrsi : m.core.read .rsi = q)
    (hsz : loadN m.memory (q + 8#64) 8 = some sz)
    (hq : q.toNat ≤ (0#64 - csize sz).toNat) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 42 ∧
      m'.core.read .rcx = sz ∧ m'.core.read .rdx = csize sz ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsi hsz ⊢
  have ef8 : (0xf8#8).signExtend 64 = 0xfffffffffffffff8#64 := by decide
  refine ex_head (stepC intFreeCode_length (o := 16) (l := 4) hl hrip (by decide) i16
    (e_loadd (ld_eq (by simp [hrsi]) hsz))) ?_
  refine ex_head (stepC intFreeCode_length (o := 20) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i20
    e_movrr) ?_
  refine ex_fC intFreeCode_length hl (by simp [hrip, rip_add]) (by decide) i23
    (e_aluI8r (op := .and) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC intFreeCode_length (o := 27) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i27
    e_movrr) ?_
  refine ex_fC intFreeCode_length hl (by simp [hrip, rip_add]) (by decide) i30 e_neg (fun f2 => ?_)
  refine ex_head (stepC intFreeCode_length (o := 33) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i33
    e_cmprr) ?_
  refine ex_head (stepC intFreeCode_length (o := 36) (l := 6) hl (by simp [hrip, rip_add]) (by decide) i36
    (e_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult,
        Silmaril.X86.Ext.AluOp.resultN, ef8, hrsi]
      simpa [csize] using hq))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp
  · simp [Silmaril.X86.Ext.AluOp.resultN, ef8, csize]
  · intro r a b c; simp [a, b, c]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x2a`–`0x46`: `q` 16-aligned, `size ≥ MINSIZE`, `size` 16-aligned (bit 3 of the
size field clear). -/
theorem int_chk1b {m : MState} {B q sz : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 42) (hrsi : m.core.read .rsi = q)
    (hrcx : m.core.read .rcx = sz) (hrdx : m.core.read .rdx = csize sz)
    (hqa : q.setWidth 8 &&& 0xf#8 = 0) (hmin : 0x1f < (csize sz).toNat)
    (h8 : sz.setWidth 32 &&& 8#32 = 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 71 ∧
      m'.core.read .rcx = 0 ∧
      (∀ r, r ≠ .rcx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsi hrcx hrdx ⊢
  have e1f : (0x1f#8).signExtend 64 = 0x1f#64 := by decide
  have e8 : (0x08#8).signExtend 32 = 8#32 := by decide
  refine ex_head (stepC intFreeCode_length (o := 42) (l := 4) hl hrip (by decide) i42 e_testI8r) ?_
  refine ex_head (stepC intFreeCode_length (o := 46) (l := 6) hl (by simp [hrip, rip_add]) (by decide) i46
    (e_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot,
        hrsi, hqa]))) ?_
  refine ex_head (stepC intFreeCode_length (o := 52) (l := 4) hl (by simp [hrip, rip_add]) (by decide) i52
    e_cmpI8r) ?_
  refine ex_head (stepC intFreeCode_length (o := 56) (l := 6) hl (by simp [hrip, rip_add]) (by decide) i56
    (e_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult,
        e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN, hrdx]
      have h1 : ¬ ((csize sz).toNat < 31) := by omega
      have h2 : (csize sz - 31#64 == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
      simp [h1, h2]))) ?_
  refine ex_head (stepC intFreeCode_length (o := 62) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i62
    e_andI8r32) ?_
  refine ex_head (stepC intFreeCode_length (o := 65) (l := 6) hl (by simp [hrip, rip_add]) (by decide) i65
    (e_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot,
        hrcx, e8, h8]))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · have := congrArg (BitVec.setWidth 64) h8
    simpa [e8, hrcx] using this
  · intro r a; simp [a]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x47`–`0x59`: `rbx := av`, the tcache pointer from TLS, non-null. -/
theorem int_chk2a {m : MState} {B offT tc : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 71)
    (hgotT : loadN m.memory (B + 0x158b48#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 90 ∧
      m'.core.read .rbx = m.core.read .rdi ∧ m'.core.read .rdi = offT ∧ m'.core.read .r8 = tc ∧
      (∀ r, r ≠ .rbx → r ≠ .rdi → r ≠ .r8 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hgotT htc ⊢
  refine ex_head (stepC intFreeCode_length (o := 71) (l := 3) hl hrip (by decide) i71 e_movrr) ?_
  refine ex_head (stepC intFreeCode_length (o := 74) (l := 7) hl (by simp [hrip, rip_add]) (by decide) i74
    (e_loadrip (ld_eq (by simp [hrip, rip_add, BitVec.add_assoc]) hgotT))) ?_
  refine ex_head (stepC intFreeCode_length (o := 81) (l := 4) hl (by simp [hrip, rip_add]) (by decide) i81
    (e_fsload (ld_eq (by simp) htc))) ?_
  refine ex_head (stepC intFreeCode_length (o := 85) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i85
    e_testrr) ?_
  refine ex_head (stepC intFreeCode_length (o := 88) (l := 2) hl (by simp [hrip, rip_add]) (by decide) i88
    (e_jcc8 (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]; exact htc0))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp
  · simp
  · simp
  · intro r a b c; simp [a, b, c]
  · rfl
  · rfl

/-- The tcache index of a chunk size (`csize2tidx`). -/
def ftidx (size : Word) : Word := (size - 0x11#64) >>> 4

set_option maxHeartbeats 4000000 in
/-- Offsets `0x5a`–`0x6a`: `tc_idx := (size - 17) >> 4 < mp_.tcache_bins`. -/
theorem int_chk2b {m : MState} {B size bins : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 90) (hrdx : m.core.read .rdx = size)
    (hbins : loadN m.memory (B + 0x158f98#64) 8 = some bins)
    (hidx : (ftidx size).toNat < bins.toNat) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 107 ∧
      m'.core.read .rax = ftidx size ∧
      (∀ r, r ≠ .rax → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdx hbins ⊢
  have eef : ∀ x : Word, x + (0xffffffef#32).signExtend 64 = x - 0x11#64 := by
    intro x; rw [show (0xffffffef#32).signExtend 64 = 0 - 0x11#64 by decide]; bv_omega
  refine ex_head (stepC intFreeCode_length (o := 90) (l := 4) hl hrip (by decide) i90 e_lea) ?_
  refine ex_fC intFreeCode_length hl (by simp [hrip, rip_add]) (by decide) i94 e_shr (fun f1 => ?_)
  refine ex_head (stepC intFreeCode_length (o := 98) (l := 7) hl (by simp [hrip, rip_add]) (by decide) i98
    (e_cmprip (ld_eq (by simp [hrip, rip_add, BitVec.add_assoc]) hbins))) ?_
  refine ex_head (stepC intFreeCode_length (o := 105) (l := 2) hl (by simp [hrip, rip_add]) (by decide) i105
    (e_jcc8 (b := false) (by
      simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, cf_sub, Silmaril.X86.Ext.kNot, Option.map_some,
        nxf_read, nx_read, Silmaril.X86.State.read_write_same, hrdx, eef]
      have : ((size - 0x11#64) >>> (BitVec.toNat 4#8 % 64)).toNat < bins.toNat := hidx
      simpa using this))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp only [nxf_read, nx_read, Silmaril.X86.State.read_write_same, hrdx, ftidx]; rw [eef]; rfl
  · intro r a; simp [a]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x6b`–`0x86`: `mp_.tcache_count`, `tcache_key`, `e := q + 16`, and the
double-free test `e->key ≠ tcache_key`. -/
theorem int_chk3a {m : MState} {B q cmax key ekey : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 107) (hrsi : m.core.read .rsi = q)
    (hcmax : loadN m.memory (B + 0x158fa8#64) 8 = some cmax)
    (hkey : loadN m.memory (B + 0x15ff28#64) 8 = some key)
    (hekey : loadN m.memory (q + 0x18#64) 8 = some ekey) (hne : ekey ≠ key) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 135 ∧
      m'.core.read .r9 = cmax ∧ m'.core.read .r11 = key ∧ m'.core.read .r10 = q + 0x10#64 ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsi hcmax hkey hekey ⊢
  refine ex_head (stepC intFreeCode_length (o := 107) (l := 7) hl hrip (by decide) i107
    (e_loadrip (ld_eq (by simp [hrip, rip_add, BitVec.add_assoc]) hcmax))) ?_
  refine ex_head (stepC intFreeCode_length (o := 114) (l := 7) hl (by simp [hrip, rip_add]) (by decide) i114
    (e_loadrip (ld_eq (by simp [hrip, rip_add, BitVec.add_assoc]) hkey))) ?_
  refine ex_head (stepC intFreeCode_length (o := 121) (l := 4) hl (by simp [hrip, rip_add]) (by decide) i121
    e_lea) ?_
  refine ex_head (stepC intFreeCode_length (o := 125) (l := 4) hl (by simp [hrip, rip_add]) (by decide) i125
    (e_cmpmr (ld_eq (by simp [hrsi]) hekey))) ?_
  refine ex_head (stepC intFreeCode_length (o := 129) (l := 6) hl (by simp [hrip, rip_add]) (by decide) i129
    (e_jcc (b := false) (by
      simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, zf_sub, nxf_read, nx_read,
        Silmaril.X86.State.read_write_same]
      simp [hne]))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp
  · simp
  · simp [hrsi]
  · intro r a b c; simp [a, b, c]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x87`–`0x97`: `counts[tc_idx] < mp_.tcache_count`; on to `tcache_put`. -/
theorem int_chk3b {m : MState} {B tc idx cmax cnt : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 135) (hr8 : m.core.read .r8 = tc)
    (hrax : m.core.read .rax = idx) (hr9 : m.core.read .r9 = cmax)
    (hcnt : loadN m.memory (tc + (idx <<< 1)) 2 = some cnt)
    (hlt : (cnt.setWidth 16).toNat < cmax.toNat) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 472 ∧
      m'.core.read .rcx = ((cnt.setWidth 16).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rcx → r ≠ .rdi → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hr8 hrax hr9 hcnt ⊢
  refine ex_head (stepC intFreeCode_length (o := 135) (l := 5) hl hrip (by decide) i135
    (e_movzw (ld_eq (by simp [hr8, hrax]) hcnt))) ?_
  refine ex_head (stepC intFreeCode_length (o := 140) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i140
    e_movrr) ?_
  refine ex_head (stepC intFreeCode_length (o := 143) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i143
    e_cmprr) ?_
  refine ex_head (stepC intFreeCode_length (o := 146) (l := 6) hl (by simp [hrip, rip_add]) (by decide) i146
    (e_jcc (b := true) (by
      simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, cf_sub, nxf_read, nx_read,
        Silmaril.X86.State.read_write_same, Silmaril.X86.State.read_write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, hr9]
      have h2 := hlt; simp at h2
      simp; omega))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add, BitVec.add_assoc]
  · simp
  · intro r a b; simp [a, b]
  · rfl
  · rfl

end Silmaril.Libc.Ptmalloc.X86sim.V239
