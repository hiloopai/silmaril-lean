module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreeScan

/-!
# ptmalloc x86sim, glibc 2.39: `free` up to `tcache_put`, and its epilogues

`free_front`: from `__libc_free`'s entry to `_int_free`'s inlined `tcache_put` (offset 472),
either branch of the `e->key` test. `int_ret`, `free_ret`: the two epilogues (`_int_free`'s at
offset 301, `__libc_free`'s at offset 126, which restores `errno`).
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
/-- A read inside `[lo, hi)` survives a store apart from it. -/
theorem rd_store {m m' : Memory} {a : Word} {k : Nat} {w : Word} {lo hi x : Nat} {bs : List Byte}
    (hs : storeN m a k w = some m') (hap : Apart a.toNat k lo hi) (hx : lo ≤ x) (hx2 : x + 8 ≤ hi)
    (h : m.readBytes x 8 = some bs) : m'.readBytes x 8 = some bs := by
  have wo := Silmaril.X86.Ext.storeN_writesOnly hs
  rw [Memory.writesOnly_iff_writesWithin] at wo
  refine rd_ww wo (fun i hi ⟨h1, h2⟩ => ?_) h
  have : a.toNat ≤ x + i ∧ x + i < a.toNat + k := ⟨h1, h2⟩
  obtain ⟨j, hj, hj'⟩ : ∃ j < k, a.toNat + j = x + i := ⟨x + i - a.toNat, by omega, by omega⟩
  exact hap j hj ⟨by omega, by omega⟩

/-- A read at an address given by an equation. -/
theorem rb_eq {mem : Memory} {a b k : Nat} {bs : List Byte} (h : a = b)
    (hb : mem.readBytes b k = some bs) : mem.readBytes a k = some bs := h ▸ hb

/-- A write permission survives a store. -/
theorem pw_store {m m' : Memory} {a : Word} {k : Nat} {w : Word} {x n : Nat}
    (hs : storeN m a k w = some m') (h : m.Permitted .write x n) : m'.Permitted .write x n := by
  have e := (Silmaril.X86.Ext.storeN_writesOnly hs).1
  simpa [Memory.Permitted, Memory.checkSpan, Memory.permits, e] using h

set_option maxHeartbeats 4000000 in
/-- **`_int_free`'s epilogue** (offsets `0x12d`–`0x137`): slots 11–8 restored, return
through slot 7. -/
theorem int_ret {m : MState} {B sp b0 b1 b2 b3 ret : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 301) (hrsp : m.core.read .rsp = sp - 0x88#64)
    (hsp : 96 ≤ sp.toNat)
    (hs3 : m.memory.readBytes (sp.toNat - 96) 8 = some (encodeWords [b3]))
    (hs2 : m.memory.readBytes (sp.toNat - 88) 8 = some (encodeWords [b2]))
    (hs1 : m.memory.readBytes (sp.toNat - 80) 8 = some (encodeWords [b1]))
    (hs0 : m.memory.readBytes (sp.toNat - 72) 8 = some (encodeWords [b0]))
    (hsr : m.memory.readBytes (sp.toNat - 64) 8 = some (encodeWords [ret])) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = ret ∧ m'.core.read .rsp = sp - 0x38#64 ∧
      m'.core.read .rbx = b3 ∧ m'.core.read .r12 = b2 ∧ m'.core.read .r13 = b1 ∧
      m'.core.read .rbp = b0 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .rbp → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hs3 hs2 hs1 hs0 hsr ⊢
  have e28 : (0x28#8).signExtend 64 = 0x28#64 := by decide
  refine ex_fC intFreeCode_length hl hrip (by decide) i301 (e_aluI8r (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC intFreeCode_length (o := 305) (l := 1) hl (by simp [hrip, rip_add]) (by decide) i305
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e28, hrsp]; bv_omega) hs3))) ?_
  refine ex_head (stepC intFreeCode_length (o := 306) (l := 2) hl (by simp [hrip, rip_add]) (by decide) i306
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e28, hrsp]; bv_omega) hs2))) ?_
  refine ex_head (stepC intFreeCode_length (o := 308) (l := 2) hl (by simp [hrip, rip_add]) (by decide) i308
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e28, hrsp]; bv_omega) hs1))) ?_
  refine ex_head (stepC intFreeCode_length (o := 310) (l := 1) hl (by simp [hrip, rip_add]) (by decide) i310
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e28, hrsp]; bv_omega) hs0))) ?_
  refine ex_head (stepC intFreeCode_length (o := 311) (l := 1) hl (by simp [hrip, rip_add]) (by decide) i311
    (e_ret (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e28, hrsp]; bv_omega) hsr))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [Silmaril.X86.Ext.AluOp.resultN, e28, hrsp]; bv_omega
  · simp
  · simp
  · simp
  · simp
  · intro r a b c d e; simp [a, b, c, d, e]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- **`__libc_free`'s return** (offsets `0x7e`–`0x8c`): `errno := r12d`, slots 3–0 restored,
return through the entry `sp`. -/
theorem free_ret {m : MState} {A sp b0 b1 b2 b3 ret : Word} (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 126) (hrsp : m.core.read .rsp = sp - 0x38#64)
    (hsp : 96 ≤ sp.toNat) (hsp2 : sp.toNat + 8 < 2 ^ 64)
    (hw : m.memory.Permitted .write (m.core.fsBase + m.core.read .rbx).toNat 4)
    (hap : Apart (m.core.fsBase + m.core.read .rbx).toNat 4 (sp.toNat - 32) (sp.toNat + 8))
    (hc : Apart (m.core.fsBase + m.core.read .rbx).toNat 4 A.toNat (A.toNat + 272))
    (hs3 : m.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [b3]))
    (hs2 : m.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [b2]))
    (hs1 : m.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [b1]))
    (hs0 : m.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [b0]))
    (hsr : m.memory.readBytes sp.toNat 8 = some (encodeWords [ret])) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = ret ∧ m'.core.read .rsp = sp + 8#64 ∧
      m'.core.read .rbx = b3 ∧ m'.core.read .r12 = b2 ∧ m'.core.read .r13 = b1 ∧
      m'.core.read .rbp = b0 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .rbp → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      storeN m.memory (m.core.fsBase + m.core.read .rbx) 4
        (((m.core.read .r12).setWidth 32).setWidth 64) = some m'.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hw hap hc hs3 hs2 hs1 hs0 hsr ⊢
  obtain ⟨mem1, h1, -⟩ := Silmaril.X86.Ext.storeN_isSome
    (v := ((c0.read .r12).setWidth 32).setWidth 64) hw
  have hl1 := loadedC_store freeCode_length hl h1 hc
  have rd : ∀ {x : Nat} {bs : List Byte}, sp.toNat - 32 ≤ x → x + 8 ≤ sp.toNat + 8 →
      mem0.readBytes x 8 = some bs → mem1.readBytes x 8 = some bs := fun hx hx2 h =>
    rd_store h1 hap hx hx2 h
  have e18 : (0x18#8).signExtend 64 = 0x18#64 := by decide
  refine ex_head (stepC freeCode_length (o := 126) (l := 4) hl hrip (by decide) f126
    (e_fsstore32 (mem' := mem1) h1)) ?_
  refine ex_fC freeCode_length hl1 (by simp [hrip, rip_add]) (by decide) f130
    (e_aluI8r (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC freeCode_length (o := 134) (l := 1) hl1 (by simp [hrip, rip_add]) (by decide) f134
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega)
      (rd (by omega) (by omega) hs3)))) ?_
  refine ex_head (stepC freeCode_length (o := 135) (l := 2) hl1 (by simp [hrip, rip_add]) (by decide) f135
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega)
      (rd (by omega) (by omega) hs2)))) ?_
  refine ex_head (stepC freeCode_length (o := 137) (l := 2) hl1 (by simp [hrip, rip_add]) (by decide) f137
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega)
      (rd (by omega) (by omega) hs1)))) ?_
  refine ex_head (stepC freeCode_length (o := 139) (l := 1) hl1 (by simp [hrip, rip_add]) (by decide) f139
    (e_pop (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega)
      (rd (by omega) (by omega) hs0)))) ?_
  refine ex_head (stepC freeCode_length (o := 140) (l := 1) hl1 (by simp [hrip, rip_add]) (by decide) f140
    (e_ret (rb_eq (by simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega)
      (rd (by omega) (by omega) hsr)))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h1⟩
  · rfl
  · simp [Silmaril.X86.Ext.AluOp.resultN, e18, hrsp]; bv_omega
  · simp
  · simp
  · simp
  · simp
  · intro r a b c d e; simp [a, b, c, d, e]
  · rfl


theorem apart_mono {a k lo hi lo' hi' : Nat} (h : Apart a k lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    Apart a k lo' hi' := fun i hi ⟨x, y⟩ => h i hi ⟨by omega, by omega⟩

/-- `_int_free`'s address from `__libc_free`'s. -/
abbrev intA (A : Word) : Word := A - 0x2be0#64

/-- Membership in a literal list of address/size pairs, without normalising the addresses. -/
macro "mem_tac" : tactic => `(tactic| simp only [List.mem_cons, Prod.mk.injEq, and_true, true_or,
  or_true, eq_self_iff_true, and_self])

theorem intA_add (A : Word) (c d : Word) (h : 0x2be0#64 + d = c) : intA A + c = A + d := by
  rw [← h]; bv_omega

set_option maxHeartbeats 8000000 in
/-- **From `free`'s entry to `0xade73`** (`free_pro`, `free_head1`, `free_head2a`): the frame
pushed, `errno` saved in `r12`, the size field in `rax`, a non-null tcache. -/
theorem free_pre {m : MState} {A sp p offE sz ev offT tc : Word}
    (hl : Loaded m.memory A freeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp)
    (hrdi : m.core.read .rdi = p) (hp : p ≠ 0) (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hcF : ∀ i < 272, ¬ fstk sp (A.toNat + i))
    (hgotE : loadN m.memory (A + 0x155fc8#64) 8 = some offE)
    (hsz : loadN m.memory (p - 8#64) 8 = some sz)
    (herr : loadN m.memory (m.core.fsBase + offE) 4 = some ev)
    (hmm : sz.setWidth 8 &&& 2#8 = 0)
    (hgotT : loadN m.memory (A + 0x155f68#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0)
    (aE : Apart (A + 0x155fc8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aS : Apart (p - 8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aR : Apart (m.core.fsBase + offE).toNat 4 (sp.toNat - 96) sp.toNat)
    (aT : Apart (A + 0x155f68#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aC : Apart (m.core.fsBase + offT).toNat 8 (sp.toNat - 96) sp.toNat) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 67 ∧
      m'.core.read .rsp = sp - 0x38#64 ∧ m'.core.read .rbp = sp - 8#64 ∧
      m'.core.read .rbx = offE ∧ m'.core.read .rax = sz ∧
      m'.core.read .r12 = (ev.setWidth 32).setWidth 64 ∧ m'.core.read .r13 = p - 0x10#64 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .r13 → r ≠ .rax → r ≠ .rbx → r ≠ .r12 → r ≠ .rdx →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m.memory.WritesWithin m'.memory (fstk sp) ∧
      m'.memory.Permitted .write (sp.toNat - 96) 96 ∧ m'.memory.Permitted .read (sp.toNat - 96) 96 ∧
      m'.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [m.core.read .r13]) ∧
      m'.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [m.core.read .rbx]) := by
  have sa : ∀ {a k}, Apart a k (sp.toNat - 96) sp.toNat → ∀ i < k, ¬ fstk sp (a + i) :=
    fun h i hi hs => h i hi hs
  obtain ⟨m1, r1, rip1, rsp1, rbp1, r13_1, fr1, fs1, ww1, pw1, pr1, s0, s1, s2, s3⟩ :=
    free_pro hl hrip hrsp hrdi hp hsp hw hr hcF
  have hl1 := loadedC_ww freeCode_length hl ww1 hcF
  have rdi1 : m1.core.read .rdi = p := by rw [fr1 _ (by decide) (by decide) (by decide)]; exact hrdi
  obtain ⟨m2, r2, rip2, rbx2, rax2, r12_2, fr2, fs2, mem2⟩ := free_head1 (m := m1) hl1 rip1 rdi1
    (ld_ww ww1 (sa aE) hgotE) (ld_ww ww1 (sa aS) hsz) (by rw [fs1]; exact ld_ww ww1 (sa aR) herr) hmm
  have hl2 : Loaded m2.memory A freeCode := by rw [mem2]; exact hl1
  have ldT : loadN m2.memory (A + 0x155f68#64) 8 = some offT := by
    rw [mem2]; exact ld_ww ww1 (sa aT) hgotT
  have ldC : loadN m2.memory (m2.core.fsBase + offT) 8 = some tc := by
    rw [mem2, fs2, fs1]; exact ld_ww ww1 (sa aC) htc
  obtain ⟨m3, r3, rip3, fr3, fs3, mem3⟩ := free_head2a hl2 rip2 ldT ldC htc0
  have mem31 : m3.memory = m1.memory := by rw [mem3, mem2]
  refine ⟨m3, r1.trans (r2.trans r3), rip3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [fs3, fs2, fs1],
    by rw [mem31]; exact ww1, by rw [mem31]; exact pw1, by rw [mem31]; exact pr1,
    by rw [mem31]; exact s0, by rw [mem31]; exact s1, by rw [mem31]; exact s2,
    by rw [mem31]; exact s3⟩
  · rw [fr3 _ (by decide), fr2 _ (by decide) (by decide) (by decide)]; exact rsp1
  · rw [fr3 _ (by decide), fr2 _ (by decide) (by decide) (by decide)]; exact rbp1
  · rw [fr3 _ (by decide)]; exact rbx2
  · rw [fr3 _ (by decide)]; exact rax2
  · rw [fr3 _ (by decide)]; exact r12_2
  · rw [fr3 _ (by decide), fr2 _ (by decide) (by decide) (by decide)]; exact r13_1
  · intro r a b c d e f g
    rw [fr3 r g, fr2 r d e f, fr1 r a b c]

set_option maxHeartbeats 8000000 in
/-- **From `0xade73` to `_int_free + 0x47`** (`free_head2b`, `free_head3`, `int_pro`,
`int_chk1a`, `int_chk1b`): the call `_int_free (&main_arena, p - 16, 0)` and its first checks,
writing only slots 7–11. `rbx` and `r12` are saved in slots 11 and 10 whatever they hold. -/
theorem free_mid71 {m : MState} {A sp p sz : Word}
    (hl : Loaded m.memory A freeCode) (hlI : Loaded m.memory (intA A) intFreeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 67) (hrsp : m.core.read .rsp = sp - 0x38#64)
    (hrbp : m.core.read .rbp = sp - 8#64) (hrax : m.core.read .rax = sz)
    (hr13 : m.core.read .r13 = p - 0x10#64) (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hcI : ∀ i < 897, ¬ fstk sp ((intA A).toNat + i))
    (hsz : loadN m.memory (p - 8#64) 8 = some sz) (aS : Apart (p - 8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (hna : sz.setWidth 8 &&& 4#8 = 0)
    (hq : (p - 0x10#64).toNat ≤ (0#64 - csize sz).toNat)
    (hqa : (p - 0x10#64).setWidth 8 &&& 0xf#8 = 0) (hmin : 0x1f < (csize sz).toNat)
    (h8 : sz.setWidth 32 &&& 8#32 = 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = intA A + BitVec.ofNat 64 71 ∧
      m'.core.read .rsp = sp - 0x88#64 ∧ m'.core.read .rsi = p - 0x10#64 ∧
      m'.core.read .rdi = A + 0x156c90#64 ∧ m'.core.read .rdx = csize sz ∧ m'.core.read .rcx = 0 ∧
      m'.core.read .r12 = 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → r ≠ .r12 → r ≠ .rbp → r ≠ .rsp →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fun a => sp.toNat - 96 ≤ a ∧ a < sp.toNat - 56) ∧
      m'.memory.readBytes (sp.toNat - 64) 8 = some (encodeWords [A + 126#64]) ∧
      m'.memory.readBytes (sp.toNat - 72) 8 = some (encodeWords [sp - 8#64]) ∧
      m'.memory.readBytes (sp.toNat - 80) 8 = some (encodeWords [p - 0x10#64]) ∧
      m'.memory.readBytes (sp.toNat - 88) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 96) 8 = some (encodeWords [m.core.read .rbx]) := by
  obtain ⟨m1, r1, rip1, rdi1, fr1, fs1, mem1⟩ := free_head2b hl hrip hrax hna
  have hl1 : Loaded m1.memory A freeCode := by rw [mem1]; exact hl
  obtain ⟨m2, r2, rip2, rsp2, rsi2, rdx2, fr2, fs2, ww2, pw2, pr2, s7⟩ :=
    free_head3 hl1 rip1 (by rw [fr1 _ (by decide)]; exact hrsp) hsp
      (by rw [mem1]; exact hw) (by rw [mem1]; exact hr)
  have ww02 : m.memory.WritesWithin m2.memory (slot sp 7) := by rw [← mem1]; exact ww2
  have hlI2 : Loaded m2.memory (intA A) intFreeCode :=
    loadedC_ww intFreeCode_length hlI ww02 (fun i hi h => hcI i hi (slot_fstk (by decide) hsp h))
  obtain ⟨mC, rC, ripC, rspC, r12C, frC, fsC, wwC, s8, s9, s10, s11⟩ :=
    int_pro (B := intA A) (sp := sp) hlI2 (by rw [rip2]; simp) rsp2 hsp pw2 pr2 hcI
  have W : ∀ a, (slot sp 7 a ∨ (sp.toNat - 96 ≤ a ∧ a < sp.toNat - 64)) →
      sp.toNat - 96 ≤ a ∧ a < sp.toNat - 56 := fun a h => by
    rcases h with h | h
    · unfold slot at h; omega
    · omega
  have ww0C : m.memory.WritesWithin mC.memory (fun a => sp.toNat - 96 ≤ a ∧ a < sp.toNat - 56) :=
    ((ww02.mono fun a h => Or.inl h).trans (wwC.mono fun a h => Or.inr h)).mono W
  have hlIC := loadedC_ww intFreeCode_length hlI ww0C (fun i hi h => hcI i hi ⟨h.1, by omega⟩)
  have e2 : ∀ r, r ≠ .rdx → r ≠ .rsi → r ≠ .rsp → r ≠ .rdi → m2.core.read r = m.core.read r :=
    fun r a b c d => by rw [fr2 r a b c, fr1 r d]
  have rbp2 : m2.core.read .rbp = sp - 8#64 := by
    rw [fr2 _ (by decide) (by decide) (by decide), fr1 _ (by decide), hrbp]
  have r13_2 : m2.core.read .r13 = p - 0x10#64 := by
    rw [fr2 _ (by decide) (by decide) (by decide), fr1 _ (by decide), hr13]
  have r12_2 : m2.core.read .r12 = m.core.read .r12 := e2 _ (by decide) (by decide) (by decide) (by decide)
  have rbx2 : m2.core.read .rbx = m.core.read .rbx := e2 _ (by decide) (by decide) (by decide) (by decide)
  have rsiC : mC.core.read .rsi = p - 0x10#64 := by
    rw [frC _ (by decide) (by decide) (by decide), rsi2, fr1 _ (by decide), hr13]
  have fsC' : mC.core.fsBase = m.core.fsBase := by rw [fsC, fs2, fs1]
  have ldS : loadN mC.memory (p - 0x10#64 + 8#64) 8 = some sz :=
    ld_eq (by bv_omega) (ld_ww ww0C (fun i hi h => aS i hi ⟨h.1, by omega⟩) hsz)
  obtain ⟨mD, rD, ripD, rcxD, rdxD, frD, fsD, memD⟩ := int_chk1a hlIC ripC rsiC ldS hq
  have hlID : Loaded mD.memory (intA A) intFreeCode := by rw [memD]; exact hlIC
  obtain ⟨mE, rE, ripE, rcxE, frE, fsE, memE⟩ :=
    int_chk1b hlID ripD (by rw [frD _ (by decide) (by decide) (by decide), rsiC]) rcxD rdxD hqa hmin h8
  have memEC : mE.memory = mC.memory := by rw [memE, memD]
  have eE : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → mE.core.read r = mC.core.read r :=
    fun r a b c => by rw [frE r b, frD r a b c]
  refine ⟨mE, (((r1.trans r2).trans rC).trans rD).trans rE, ripE, ?_, ?_, ?_, ?_, rcxE, ?_, ?_,
    by rw [fsE, fsD, fsC'], by rw [memEC]; exact ww0C, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eE _ (by decide) (by decide) (by decide)]; exact rspC
  · rw [eE _ (by decide) (by decide) (by decide)]; exact rsiC
  · rw [eE _ (by decide) (by decide) (by decide), frC _ (by decide) (by decide) (by decide),
      fr2 _ (by decide) (by decide) (by decide)]; exact rdi1
  · rw [frE _ (by decide)]; exact rdxD
  · rw [eE _ (by decide) (by decide) (by decide), r12C, rdx2]; rfl
  · intro r a b c d e f g h
    rw [eE r a b c, frC r h g f, e2 r c e h d]
  · rw [memEC]; exact rd_ww wwC (fun i hi hh => by omega) s7
  · rw [memEC]; rw [rbp2] at s8; exact s8
  · rw [memEC]; rw [r13_2] at s9; exact s9
  · rw [memEC]; rw [r12_2] at s10; exact s10
  · rw [memEC]; rw [rbx2] at s11; exact s11

set_option maxHeartbeats 8000000 in
/-- **From `0xade73` to `_int_free`'s tcache count test** (`+0x87`), either branch of the key
test: `free_mid71`, the non-null tcache, the bin index, `int_chk3`. -/
theorem free_mid135 {m : MState} {A sp p sz offT tc bins cmax key ekey h : Word}
    (hl : Loaded m.memory A freeCode) (hlI : Loaded m.memory (intA A) intFreeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 67) (hrsp : m.core.read .rsp = sp - 0x38#64)
    (hrbp : m.core.read .rbp = sp - 8#64) (hrax : m.core.read .rax = sz)
    (hr13 : m.core.read .r13 = p - 0x10#64) (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hcI : ∀ i < 897, ¬ fstk sp ((intA A).toNat + i))
    (hsz : loadN m.memory (p - 8#64) 8 = some sz)
    (hna : sz.setWidth 8 &&& 4#8 = 0)
    (hq : (p - 0x10#64).toNat ≤ (0#64 - csize sz).toNat)
    (hqa : (p - 0x10#64).setWidth 8 &&& 0xf#8 = 0) (hmin : 0x1f < (csize sz).toNat)
    (h8 : sz.setWidth 32 &&& 8#32 = 0)
    (hgotT : loadN m.memory (A + 0x155f68#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + 0x1563b8#64) 8 = some bins)
    (hidx : (ftidx (csize sz)).toNat < bins.toNat)
    (hcmax : loadN m.memory (A + 0x1563c8#64) 8 = some cmax)
    (hkey : loadN m.memory (A + 0x15d348#64) 8 = some key)
    (hekey : loadN m.memory (p + 8#64) 8 = some ekey)
    (hk : ekey ≠ key ∨ ∃ L, TcWalk m.memory h p cmax L ∧
      ∀ j < L.length, Apart (L.getD j 0).toNat 8 (sp.toNat - 96) sp.toNat)
    (hent : loadN m.memory (tc + (ftidx (csize sz) <<< 3) + 0x80#64) 8 = some h)
    (aS : Apart (p - 8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aT : Apart (A + 0x155f68#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aC : Apart (m.core.fsBase + offT).toNat 8 (sp.toNat - 96) sp.toNat)
    (aB : Apart (A + 0x1563b8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aM : Apart (A + 0x1563c8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aK : Apart (A + 0x15d348#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (aE : Apart (p + 8#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (hapE : Apart (tc + (ftidx (csize sz) <<< 3) + 0x80#64).toNat 8 (sp.toNat - 96) sp.toNat) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = intA A + BitVec.ofNat 64 135 ∧
      m'.core.read .rsp = sp - 0x88#64 ∧ m'.core.read .rsi = p - 0x10#64 ∧
      m'.core.read .r10 = p - 0x10#64 + 0x10#64 ∧ m'.core.read .r8 = tc ∧
      m'.core.read .rax = ftidx (csize sz) ∧ m'.core.read .r9 = cmax ∧
      m'.core.read .rbx = A + 0x156c90#64 ∧ m'.core.read .rdx = csize sz ∧ m'.core.read .r12 = 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 →
        r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ .r13 → r ≠ .rbp → r ≠ .rsp →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fun a => sp.toNat - 96 ≤ a ∧ a < sp.toNat - 56) ∧
      m'.memory.readBytes (sp.toNat - 64) 8 = some (encodeWords [A + 126#64]) ∧
      m'.memory.readBytes (sp.toNat - 72) 8 = some (encodeWords [sp - 8#64]) ∧
      m'.memory.readBytes (sp.toNat - 80) 8 = some (encodeWords [p - 0x10#64]) ∧
      m'.memory.readBytes (sp.toNat - 88) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 96) 8 = some (encodeWords [m.core.read .rbx]) := by
  obtain ⟨mE, rE, ripE, rspE, rsiE, rdiE, rdxE, rcxE, r12E, frE, fsE, wwE, s7, s8, s9, s10, s11⟩ :=
    free_mid71 hl hlI hrip hrsp hrbp hrax hr13 hsp hw hr hcI hsz aS hna hq hqa hmin h8
  have sa : ∀ {a k}, Apart a k (sp.toNat - 96) sp.toNat →
      ∀ i < k, ¬ (sp.toNat - 96 ≤ a + i ∧ a + i < sp.toNat - 56) :=
    fun h i hi hs => h i hi ⟨hs.1, by omega⟩
  have hlIE := loadedC_ww intFreeCode_length hlI wwE (fun i hi h => hcI i hi ⟨h.1, by omega⟩)
  obtain ⟨mF, rF, ripF, rbxF, rdiF, r8F, frF, fsF, memF⟩ :=
    int_chk2a (offT := offT) (tc := tc) hlIE ripE
      (by rw [intA_add A 0x158b48#64 0x155f68#64 (by decide)]; exact ld_ww wwE (sa aT) hgotT)
      (by rw [fsE]; exact ld_ww wwE (sa aC) htc) htc0
  have hlIF : Loaded mF.memory (intA A) intFreeCode := by rw [memF]; exact hlIE
  obtain ⟨mG, rG, ripG, raxG, frG, fsG, memG⟩ :=
    int_chk2b hlIF ripF (by rw [frF _ (by decide) (by decide) (by decide), rdxE])
      (by rw [memF, intA_add A 0x158f98#64 0x1563b8#64 (by decide)]; exact ld_ww wwE (sa aB) hbins) hidx
  have hlIG : Loaded mG.memory (intA A) intFreeCode := by rw [memG]; exact hlIF
  have rsiG : mG.core.read .rsi = p - 0x10#64 := by
    rw [frG _ (by decide), frF _ (by decide) (by decide) (by decide), rsiE]
  have e10 : p - 0x10#64 + 0x10#64 = p := by bv_omega
  have memGE : mG.memory = mE.memory := by rw [memG, memF]
  obtain ⟨mH, rH, ripH, r8H, r9H, r10H, frH, fsH, memH⟩ :=
    int_chk3 (offT := offT) (tc := tc) (idx := ftidx (csize sz)) (h := h) hlIG ripG rsiG
      (by rw [frG _ (by decide), rdiF]) (by rw [frG _ (by decide), r8F]) raxG
      (by rw [frG _ (by decide), frF _ (by decide) (by decide) (by decide), rcxE])
      (by rw [fsG, fsF, fsE, memGE]; exact ld_ww wwE (sa aC) htc)
      (by rw [memGE, intA_add A 0x158fa8#64 0x1563c8#64 (by decide)]; exact ld_ww wwE (sa aM) hcmax)
      (by rw [memGE, intA_add A 0x15ff28#64 0x15d348#64 (by decide)]; exact ld_ww wwE (sa aK) hkey)
      (by rw [memGE]; exact ld_eq (by bv_omega) (ld_ww wwE (sa aE) hekey))
      (by rw [memGE]; exact ld_ww wwE (sa hapE) hent)
      (hk.imp id fun ⟨L, hW, hap⟩ => ⟨L, by
        rw [memGE, e10]
        exact tcWalk_ww hW wwE fun j hj i hi => sa (hap j hj) i hi⟩)
  have memHE : mH.memory = mE.memory := by rw [memH, memGE]
  have d7 : ∀ r : Reg, r = .rbx ∨ r = .rdx ∨ r = .r12 ∨ r = .rax ∨ r = .rsp ∨ r = .rsi →
      r ≠ .rcx ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r13 := by
    intro r h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have frH' : ∀ r : Reg, r = .rbx ∨ r = .rdx ∨ r = .r12 ∨ r = .rax ∨ r = .rsp ∨ r = .rsi →
      mH.core.read r = mG.core.read r := fun r h => by
    obtain ⟨a, b, c, d, e, f, g⟩ := d7 r h; exact frH r a b c d e f g
  refine ⟨mH, (((rE.trans rF).trans rG).trans rH), ripH, ?_, ?_, r10H, r8H, ?_, r9H, ?_, ?_, ?_,
    ?_, by rw [fsH, fsG, fsF, fsE], by rw [memHE]; exact wwE, by rw [memHE]; exact s7,
    by rw [memHE]; exact s8, by rw [memHE]; exact s9, by rw [memHE]; exact s10,
    by rw [memHE]; exact s11⟩
  · rw [frH' _ (by simp), frG _ (by decide), frF _ (by decide) (by decide) (by decide), rspE]
  · rw [frH' _ (by simp), rsiG]
  · rw [frH' _ (by simp), raxG]
  · rw [frH' _ (by simp), frG _ (by decide), rbxF, rdiE]
  · rw [frH' _ (by simp), frG _ (by decide), frF _ (by decide) (by decide) (by decide), rdxE]
  · rw [frH' _ (by simp), frG _ (by decide), frF _ (by decide) (by decide) (by decide), r12E]
  · intro r a b c d e f g h i j k l n o
    rw [frH _ c e g h i j l, frG _ a, frF _ b e g, frE _ a c d e f k n o]

set_option maxHeartbeats 8000000 in
/-- **From `free`'s entry to `tcache_put`.** -/
theorem free_front {m : MState} {A sp p offE sz ev offT tc bins cmax key ekey cnt h : Word}
    (hl : Loaded m.memory A freeCode) (hlI : Loaded m.memory (intA A) intFreeCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp)
    (hrdi : m.core.read .rdi = p) (hp : p ≠ 0) (hsp : 96 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 96) 96) (hr : m.memory.Permitted .read (sp.toNat - 96) 96)
    (hcF : ∀ i < 272, ¬ fstk sp (A.toNat + i)) (hcI : ∀ i < 897, ¬ fstk sp ((intA A).toNat + i))
    (hgotE : loadN m.memory (A + 0x155fc8#64) 8 = some offE)
    (hsz : loadN m.memory (p - 8#64) 8 = some sz)
    (herr : loadN m.memory (m.core.fsBase + offE) 4 = some ev)
    (hmm : sz.setWidth 8 &&& 2#8 = 0) (hna : sz.setWidth 8 &&& 4#8 = 0)
    (hgotT : loadN m.memory (A + 0x155f68#64) 8 = some offT)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc) (htc0 : tc ≠ 0)
    (hq : (p - 0x10#64).toNat ≤ (0#64 - csize sz).toNat)
    (hqa : (p - 0x10#64).setWidth 8 &&& 0xf#8 = 0) (hmin : 0x1f < (csize sz).toNat)
    (h8 : sz.setWidth 32 &&& 8#32 = 0)
    (hbins : loadN m.memory (A + 0x1563b8#64) 8 = some bins)
    (hidx : (ftidx (csize sz)).toNat < bins.toNat)
    (hcmax : loadN m.memory (A + 0x1563c8#64) 8 = some cmax)
    (hkey : loadN m.memory (A + 0x15d348#64) 8 = some key)
    (hekey : loadN m.memory (p + 8#64) 8 = some ekey)
    (hk : ekey ≠ key ∨ ∃ L, TcWalk m.memory h p cmax L ∧
      ∀ j < L.length, Apart (L.getD j 0).toNat 8 (sp.toNat - 96) sp.toNat)
    (hcnt : loadN m.memory (tc + (ftidx (csize sz) <<< 1)) 2 = some cnt)
    (hlt : (cnt.setWidth 16).toNat < cmax.toNat)
    (hent : loadN m.memory (tc + (ftidx (csize sz) <<< 3) + 0x80#64) 8 = some h)
    (hapE : Apart (tc + (ftidx (csize sz) <<< 3) + 0x80#64).toNat 8 (sp.toNat - 96) sp.toNat)
    (hapL : ∀ a k, (a, k) ∈ [((A + 0x155fc8#64).toNat, 8), ((p - 8#64).toNat, 8),
      ((m.core.fsBase + offE).toNat, 4), ((A + 0x155f68#64).toNat, 8),
      ((m.core.fsBase + offT).toNat, 8), ((A + 0x1563b8#64).toNat, 8),
      ((A + 0x1563c8#64).toNat, 8), ((A + 0x15d348#64).toNat, 8), ((p + 8#64).toNat, 8),
      ((tc + (ftidx (csize sz) <<< 1)).toNat, 2)] → Apart a k (sp.toNat - 96) sp.toNat) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = intA A + BitVec.ofNat 64 472 ∧
      m'.core.read .rsp = sp - 0x88#64 ∧ m'.core.read .rsi = p - 0x10#64 ∧
      m'.core.read .r10 = p - 0x10#64 + 0x10#64 ∧ m'.core.read .r8 = tc ∧
      m'.core.read .rax = ftidx (csize sz) ∧
      m'.core.read .rcx = ((cnt.setWidth 16).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 →
        r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → r ≠ .r13 → r ≠ .rbp → r ≠ .rsp →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fstk sp) ∧
      m'.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [m.core.read .r13]) ∧
      m'.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [m.core.read .rbx]) ∧
      m'.memory.readBytes (sp.toNat - 64) 8 = some (encodeWords [A + 126#64]) ∧
      m'.memory.readBytes (sp.toNat - 72) 8 = some (encodeWords [sp - 8#64]) ∧
      m'.memory.readBytes (sp.toNat - 80) 8 = some (encodeWords [p - 0x10#64]) ∧
      m'.memory.readBytes (sp.toNat - 88) 8 = some (encodeWords [(ev.setWidth 32).setWidth 64]) ∧
      m'.memory.readBytes (sp.toNat - 96) 8 = some (encodeWords [offE]) := by
  have sa : ∀ {a k}, Apart a k (sp.toNat - 96) sp.toNat → ∀ i < k, ¬ fstk sp (a + i) :=
    fun h i hi hs => h i hi hs
  obtain ⟨mA, rA, ripA, rspA, rbpA, rbxA, raxA, r12A, r13A, frA, fsA, wwA, pwA, prA, s0, s1, s2, s3⟩ :=
    free_pre hl hrip hrsp hrdi hp hsp hw hr hcF hgotE hsz herr hmm hgotT htc htc0
      (hapL _ _ (by mem_tac)) (hapL _ _ (by mem_tac)) (hapL _ _ (by mem_tac)) (hapL _ _ (by mem_tac))
      (hapL _ _ (by mem_tac))
  have ldA : ∀ {a : Word} {k : Nat} {x : Word}, Apart a.toNat k (sp.toNat - 96) sp.toNat →
      loadN m.memory a k = some x → loadN mA.memory a k = some x := fun h hx => ld_ww wwA (sa h) hx
  have aC : Apart (mA.core.fsBase + offT).toNat 8 (sp.toNat - 96) sp.toNat := by
    rw [fsA]; exact hapL _ _ (by mem_tac)
  obtain ⟨mH, rH, ripH, rspH, rsiH, r10H, r8H, raxH, r9H, rbxH, rdxH, r12H, frH, fsH, wwH, s7, s8, s9,
    s10, s11⟩ := free_mid135 (loadedC_ww freeCode_length hl wwA hcF)
      (loadedC_ww intFreeCode_length hlI wwA hcI) ripA rspA rbpA raxA r13A hsp pwA prA hcI
      (ldA (hapL _ _ (by mem_tac)) hsz) hna hq hqa hmin h8 (ldA (hapL _ _ (by mem_tac)) hgotT)
      (by rw [fsA]; exact ldA (hapL _ _ (by mem_tac)) htc) htc0 (ldA (hapL _ _ (by mem_tac)) hbins) hidx
      (ldA (hapL _ _ (by mem_tac)) hcmax) (ldA (hapL _ _ (by mem_tac)) hkey)
      (ldA (hapL _ _ (by mem_tac)) hekey)
      (hk.imp id fun ⟨L, hW, hap⟩ => ⟨L, tcWalk_ww hW wwA (fun j hj i hi => sa (hap j hj) i hi), hap⟩)
      (ldA hapE hent) (hapL _ _ (by mem_tac)) (hapL _ _ (by mem_tac)) aC (hapL _ _ (by mem_tac))
      (hapL _ _ (by mem_tac)) (hapL _ _ (by mem_tac)) (hapL _ _ (by mem_tac)) hapE
  have wwAH : m.memory.WritesWithin mH.memory (fstk sp) := wwA.trans (wwH.mono fun a h => ⟨h.1, by omega⟩)
  have hlIH := loadedC_ww intFreeCode_length hlI wwAH hcI
  obtain ⟨mI, rI, ripI, rcxI, frI, fsI, memI⟩ :=
    int_chk3b (tc := tc) (idx := ftidx (csize sz)) hlIH ripH r8H raxH r9H
      (ld_ww wwAH (sa (hapL _ _ (by mem_tac))) hcnt) hlt
  have keep03 : ∀ {x : Nat} {bs : List Byte}, sp.toNat - 32 ≤ x → x + 8 ≤ sp.toNat →
      mA.memory.readBytes x 8 = some bs → mI.memory.readBytes x 8 = some bs := by
    intro x bs h1 h2 h
    rw [memI]; exact rd_ww wwH (fun i hi hh => by omega) h
  refine ⟨mI, rA.trans (rH.trans rI), ripI, ?_, ?_, ?_, ?_, ?_, rcxI, ?_, by rw [fsI, fsH, fsA],
    by rw [memI]; exact wwAH, keep03 (by omega) (by omega) s0, keep03 (by omega) (by omega) s1,
    keep03 (by omega) (by omega) s2, keep03 (by omega) (by omega) s3, by rw [memI]; exact s7,
    by rw [memI]; exact s8, by rw [memI]; exact s9, ?_, ?_⟩
  · rw [frI _ (by decide) (by decide)]; exact rspH
  · rw [frI _ (by decide) (by decide)]; exact rsiH
  · rw [frI _ (by decide) (by decide)]; exact r10H
  · rw [frI _ (by decide) (by decide)]; exact r8H
  · rw [frI _ (by decide) (by decide)]; exact raxH
  · intro r a b c d e f g h i j k l n o
    rw [frI _ c e, frH _ a b c d e f g h i j k l n o, frA _ o n l a b k d]
  · rw [memI]; rw [r12A] at s10; exact s10
  · rw [memI]; rw [rbxA] at s11; exact s11

end Silmaril.Libc.Ptmalloc.X86sim.V239
