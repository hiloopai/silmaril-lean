module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreeRun

/-!
# ptmalloc x86sim, glibc 2.39: `_int_free`'s double-free scan (`e->key == tcache_key`)

`TcWalk mem h e cmax L`: the bin from the head `h` is the list `L` of nonzero, 16-aligned
entries, none equal to `e`, at most `cmax`, each holding `PROTECT_PTR` of its successor.
`int_chk3`: offsets `0x6b` to the count test at `0x87` on either branch of the key test.
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

section
variable {c : State} {mem : Memory} {l : Nat}

theorem e_nop {n : Fin 15} : Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.nop n))))) c mem l =
    .ok (nx c (c.rip + BitVec.ofNat 64 l)) mem := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]; rfl

theorem e_xorrr {d s : Reg} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .q .xor (.reg d) s))))) c mem l =
      .ok (nxf (c.write d (c.read d ^^^ c.read s)) (c.rip + BitVec.ofNat 64 l) f) mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 64) .xor (c.read d) (c.read s), ?_⟩
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write,
    Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.AluOp.resultN]
  rfl

end
set_option maxRecDepth 100000

/-- **The tcache bin walked by the double-free test**: from the head `h`, the entries `L`
(payload addresses), each nonzero, 16-aligned and not `e`, at most `cmax`, each holding
`PROTECT_PTR` of the next (null after the last). -/
def TcWalk (mem : Memory) (h e cmax : Word) (L : List Word) : Prop :=
  L.headD 0 = h ∧ L.length ≤ cmax.toNat ∧ ∀ j < L.length,
    L.getD j 0 ≠ 0 ∧ (L.getD j 0).setWidth 8 &&& 0xf#8 = 0 ∧ L.getD j 0 ≠ e ∧
    loadN mem (L.getD j 0) 8 = some ((L.getD j 0 >>> 12) ^^^ L.getD (j + 1) 0)

theorem xor_cancel_left (a b : Word) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem eq_xor_iff (a b : Word) : a = a ^^^ b ↔ b = 0 := by
  constructor
  · intro h
    have := congrArg (a ^^^ ·) h
    simp only [BitVec.xor_self, xor_cancel_left] at this
    exact this.symm
  · intro h; subst h; simp

/-! ## Jumps with an abstract successor

After a jump the successor state is handed on abstractly (its `rip`, registers, FS base and
memory as facts), so the terms of the later steps do not grow with the earlier ones. -/

section jumps
variable {code : List Byte} {N : Nat} {A : Word} {P : MState → Prop} {m : MState} {o l tgt : Nat}

/-- A `jcc rel32` step. -/
theorem ex_jccA (hN : code.length = N) {cond : Silmaril.X86.Ext.Cond} {rel : BitVec 32} {b : Bool}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o) (hfit : o + l ≤ N)
    (hdec : Str9Fs.decode ((code.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.jcc cond rel)))), l))
    (hb : cond.eval m.core.flags = some b)
    (ht : (if b then A + BitVec.ofNat 64 o + BitVec.ofNat 64 l + rel.signExtend 64
      else A + BitVec.ofNat 64 o + BitVec.ofNat 64 l) = A + BitVec.ofNat 64 tgt)
    (cont : ∀ t : MState, t.core.rip = A + BitVec.ofNat 64 tgt → (∀ r, t.core.read r = m.core.read r) →
      t.core.fsBase = m.core.fsBase → t.memory = m.memory → ∃ u, Reaches Str9Fs.step t u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u :=
  ex_head (stepC hN hl hrip hfit hdec (e_jcc hb))
    (cont _ (by simp only [nx_rip]; rw [hrip]; exact ht) (fun _ => rfl) rfl rfl)

/-- A `jcc rel8` step. -/
theorem ex_jcc8A (hN : code.length = N) {cond : Silmaril.X86.Ext.Cond} {rel : BitVec 8} {b : Bool}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o) (hfit : o + l ≤ N)
    (hdec : Str9Fs.decode ((code.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.jcc8 cond rel)))), l))
    (hb : cond.eval m.core.flags = some b)
    (ht : (if b then A + BitVec.ofNat 64 o + BitVec.ofNat 64 l + rel.signExtend 64
      else A + BitVec.ofNat 64 o + BitVec.ofNat 64 l) = A + BitVec.ofNat 64 tgt)
    (cont : ∀ t : MState, t.core.rip = A + BitVec.ofNat 64 tgt → (∀ r, t.core.read r = m.core.read r) →
      t.core.fsBase = m.core.fsBase → t.memory = m.memory → ∃ u, Reaches Str9Fs.step t u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u :=
  ex_head (stepC hN hl hrip hfit hdec (e_jcc8 hb))
    (cont _ (by simp only [nx_rip]; rw [hrip]; exact ht) (fun _ => rfl) rfl rfl)

/-- A `jmp rel32` step. -/
theorem ex_jmpA (hN : code.length = N) {rel : BitVec 32}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o) (hfit : o + l ≤ N)
    (hdec : Str9Fs.decode ((code.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.jmp rel)))), l))
    (ht : A + BitVec.ofNat 64 o + BitVec.ofNat 64 l + rel.signExtend 64 = A + BitVec.ofNat 64 tgt)
    (cont : ∀ t : MState, t.core.rip = A + BitVec.ofNat 64 tgt → (∀ r, t.core.read r = m.core.read r) →
      t.core.fsBase = m.core.fsBase → t.memory = m.memory → ∃ u, Reaches Str9Fs.step t u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u :=
  ex_head (stepC hN hl hrip hfit hdec e_jmp)
    (cont _ (by simp only [nx_rip]; rw [hrip]; exact ht) (fun _ => rfl) rfl rfl)

end jumps

/-- The end of a run: the state itself, from facts. -/
theorem ex_done {P : MState → Prop} {t : MState} (h : P t) : ∃ u, Reaches Str9Fs.step t u ∧ P u :=
  ⟨t, Reaches.refl _ _, h⟩

set_option maxHeartbeats 4000000 in
/-- Offsets `0x6b`–`0x86` with `e->key = tcache_key`: on to the walk at `0x330`. -/
theorem int_chk3a_eq {m : MState} {B q cmax key : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 107) (hrsi : m.core.read .rsi = q)
    (hcmax : loadN m.memory (B + 0x158fa8#64) 8 = some cmax)
    (hkey : loadN m.memory (B + 0x15ff28#64) 8 = some key)
    (hekey : loadN m.memory (q + 0x18#64) 8 = some key) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 816 ∧
      m'.core.read .r10 = q + 0x10#64 ∧
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
    (e_jcc (b := true) (by
      simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, zf_sub, nxf_read, nx_read,
        Silmaril.X86.State.read_write_same]
      simp))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add, BitVec.add_assoc]
  · simp [hrsi]
  · intro r a b c; simp [a, b, c]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x330`–`0x343`: `r8 := tcache`, `r9 := mp_.tcache_count`,
`rdi := tcache->entries[tc_idx]`. -/
theorem int_walk0a {m : MState} {B offT tc idx cmax h : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 816) (hrdi : m.core.read .rdi = offT)
    (hrax : m.core.read .rax = idx)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc)
    (hcmax : loadN m.memory (B + 0x158fa8#64) 8 = some cmax)
    (hent : loadN m.memory (tc + (idx <<< 3) + 0x80#64) 8 = some h) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 836 ∧
      m'.core.read .rdi = h ∧ m'.core.read .r8 = tc ∧ m'.core.read .r9 = cmax ∧
      (∀ r, r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdi hrax htc hcmax hent ⊢
  have e80 : (0x00000080#32).signExtend 64 = 0x80#64 := by decide
  refine ex_head (stepC intFreeCode_length (o := 816) (l := 1) hl hrip (by decide) i816 e_nop) ?_
  refine ex_head (stepC intFreeCode_length (o := 817) (l := 4) hl (by simp [hrip, rip_add]) (by decide) i817
    (e_fsload (ld_eq (by simp [hrdi]) htc))) ?_
  refine ex_head (stepC intFreeCode_length (o := 821) (l := 7) hl (by simp [hrip, rip_add]) (by decide) i821
    (e_loadrip (ld_eq (by simp [hrip, rip_add, BitVec.add_assoc]) hcmax))) ?_
  refine ex_head (stepC intFreeCode_length (o := 828) (l := 8) hl (by simp [hrip, rip_add]) (by decide) i828
    (e_loadidx8d (ld_eq (by simp [hrax, e80]) hent))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp
  · simp
  · simp
  · intro r a b c; simp [a, b, c]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- Offsets `0x344`–`0x34d`: an empty bin jumps back to `0x87`, a nonempty one to the loop
test at `0x376`. -/
theorem int_walk0b {m : MState} {B h : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 836) (hrdi : m.core.read .rdi = h) :
    ∃ m', Reaches Str9Fs.step m m' ∧
      ((h = 0 ∧ m'.core.rip = B + BitVec.ofNat 64 135) ∨ (h ≠ 0 ∧ m'.core.rip = B + BitVec.ofNat 64 886)) ∧
      (∀ r, m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdi ⊢
  refine ex_head (stepC intFreeCode_length (o := 836) (l := 3) hl hrip (by decide) i836
    e_testrr) ?_
  by_cases hh : h = 0
  · refine ex_jcc8A intFreeCode_length (o := 839) (l := 2) (tgt := 841) (b := false) hl
      (by simp [hrip, rip_add]) (by decide) i839 (by
        simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot,
          hrdi, hh]) (by simp [rip_add]) (fun t1 rip1 reg1 fs1 mem1 => ?_)
    refine ex_jmpA intFreeCode_length (o := 841) (l := 5) (tgt := 135) (by rw [mem1]; exact hl) rip1
      (by decide) i841 (by simp [BitVec.add_assoc]) (fun t2 rip2 reg2 fs2 mem2 => ?_)
    exact ex_done ⟨Or.inl ⟨hh, rip2⟩, fun r => by rw [reg2, reg1]; rfl, by rw [fs2, fs1]; rfl,
      by rw [mem2, mem1]⟩
  · refine ex_jcc8A intFreeCode_length (o := 839) (l := 2) (tgt := 886) (b := true) hl
      (by simp [hrip, rip_add]) (by decide) i839 (by
        have hh' : ¬ h = 0#64 := hh
        simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot,
          hrdi, hh']) (by simp [BitVec.add_assoc]) (fun t1 rip1 reg1 fs1 mem1 => ?_)
    exact ex_done ⟨Or.inr ⟨hh, rip1⟩, fun r => by rw [reg1]; rfl, by rw [fs1]; rfl, mem1⟩

/-- Offsets `0x330`–`0x34d`, composed. -/
theorem int_walk0 {m : MState} {B offT tc idx cmax h : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 816) (hrdi : m.core.read .rdi = offT)
    (hrax : m.core.read .rax = idx)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc)
    (hcmax : loadN m.memory (B + 0x158fa8#64) 8 = some cmax)
    (hent : loadN m.memory (tc + (idx <<< 3) + 0x80#64) 8 = some h) :
    ∃ m', Reaches Str9Fs.step m m' ∧
      ((h = 0 ∧ m'.core.rip = B + BitVec.ofNat 64 135) ∨ (h ≠ 0 ∧ m'.core.rip = B + BitVec.ofNat 64 886)) ∧
      m'.core.read .rdi = h ∧ m'.core.read .r8 = tc ∧ m'.core.read .r9 = cmax ∧
      (∀ r, r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨m1, r1, rip1, rdi1, r81, r91, fr1, fs1, mem1⟩ := int_walk0a hl hrip hrdi hrax htc hcmax hent
  obtain ⟨m2, r2, rip2, fr2, fs2, mem2⟩ := int_walk0b (by rw [mem1]; exact hl) rip1 rdi1
  exact ⟨m2, r1.trans r2, rip2, by rw [fr2, rdi1], by rw [fr2, r81], by rw [fr2, r91],
    fun r a b c => by rw [fr2, fr1 r a b c], by rw [fs2, fs1], by rw [mem2, mem1]⟩

/-! ## One turn of the walk, in four pieces -/

set_option maxHeartbeats 4000000 in
/-- Offsets `0x376`–`0x37f`: `cnt ≠ mp_.tcache_count`, `tmp` aligned; on to `0x350`. -/
theorem int_walk_s1 {m : MState} {B x cmax : Word} {j : Nat} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 886)
    (hrdi : m.core.read .rdi = x) (hrcx : m.core.read .rcx = BitVec.ofNat 64 j)
    (hr9 : m.core.read .r9 = cmax) (hj : j < cmax.toNat) (hal : x.setWidth 8 &&& 0xf#8 = 0) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 848 ∧
      (∀ r, m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdi hrcx hr9 ⊢
  have hjne : BitVec.ofNat 64 j ≠ cmax := by
    intro h; subst h; simp only [BitVec.toNat_ofNat] at hj; omega
  refine ex_head (stepC intFreeCode_length (o := 886) (l := 3) hl hrip (by decide) i886
    e_cmprr) ?_
  refine ex_jcc8A intFreeCode_length (o := 889) (l := 2) (tgt := 891) (b := false) hl
    (by simp [hrip, rip_add]) (by decide) i889 (by
      simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, zf_sub, nxf_read, nx_read]
      simp [hrcx, hr9, hjne]) (by simp [rip_add]) (fun t1 rip1 reg1 fs1 mem1 => ?_)
  have hl1 : Loaded t1.memory B intFreeCode := by rw [mem1]; exact hl
  have rdi1 : t1.core.read .rdi = x := by rw [reg1]; exact hrdi
  obtain ⟨c1, m1⟩ := t1
  simp only at hl1 rip1 rdi1 reg1 fs1 mem1 ⊢
  refine ex_head (stepC intFreeCode_length (o := 891) (l := 4) hl1 rip1 (by decide) i891
    e_testI8r) ?_
  refine ex_jcc8A intFreeCode_length (o := 895) (l := 2) (tgt := 848) (b := true) hl1
    (by simp [rip1, rip_add]) (by decide) i895 (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN, rdi1, hal])
    (by simp [BitVec.add_assoc]) (fun t2 rip2 reg2 fs2 mem2 => ?_)
  exact ex_done ⟨rip2, fun r => by rw [reg2]; exact reg1 r, by rw [fs2]; exact fs1, by rw [mem2]; exact mem1⟩

set_option maxHeartbeats 4000000 in
/-- Offsets `0x350`–`0x35e`: `tmp ≠ e`; `r13 := tmp`, `r11 := tmp->next`. -/
theorem int_walk_s2 {m : MState} {B x e v : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 848)
    (hrdi : m.core.read .rdi = x) (hr10 : m.core.read .r10 = e) (hxe : x ≠ e)
    (hld : loadN m.memory x 8 = some v) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 863 ∧
      m'.core.read .r13 = x ∧ m'.core.read .r11 = v ∧
      (∀ r, r ≠ .r11 → r ≠ .r13 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdi hr10 hld ⊢
  have e0 : (0x00000000#32).signExtend 64 = 0#64 := by decide
  refine ex_head (stepC intFreeCode_length (o := 848) (l := 3) hl hrip (by decide) i848 e_cmprr) ?_
  refine ex_jccA intFreeCode_length (o := 851) (l := 6) (tgt := 857) (b := false) hl
    (by simp [hrip, rip_add]) (by decide) i851 (by
      simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, zf_sub, nxf_read, nx_read]
      simp [hrdi, hr10, hxe]) (by simp [rip_add]) (fun t1 rip1 reg1 fs1 mem1 => ?_)
  have hl1 : Loaded t1.memory B intFreeCode := by rw [mem1]; exact hl
  have rdi1 : t1.core.read .rdi = x := by rw [reg1]; exact hrdi
  have ld1 : loadN t1.memory x 8 = some v := by rw [mem1]; exact hld
  obtain ⟨c1, m1⟩ := t1
  simp only at hl1 rip1 rdi1 reg1 fs1 mem1 ld1 ⊢
  refine ex_head (stepC intFreeCode_length (o := 857) (l := 3) hl1 rip1 (by decide) i857
    e_movrr) ?_
  refine ex_head (stepC intFreeCode_length (o := 860) (l := 3) hl1 (by simp [rip1, rip_add]) (by decide) i860
    (e_loadd (ld_eq (by simp [rdi1, e0]) ld1))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, fs1, mem1⟩
  · simp [rip1, rip_add]
  · simp [rdi1]
  · simp
  · intro r a b; simp [a, b, reg1]

set_option maxHeartbeats 4000000 in
/-- Offsets `0x35f`–`0x36c`: `cnt += 1`, `rdi := REVEAL_PTR (tmp->next)`, `r13 := tmp >> 12`. -/
theorem int_walk_s3 {m : MState} {B x y : Word} {j : Nat} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 863) (hrcx : m.core.read .rcx = BitVec.ofNat 64 j)
    (hr13 : m.core.read .r13 = x) (hr11 : m.core.read .r11 = (x >>> 12) ^^^ y) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 877 ∧
      m'.core.read .rcx = BitVec.ofNat 64 (j + 1) ∧ m'.core.read .r13 = x >>> 12 ∧
      m'.core.read .rdi = y ∧ m'.core.read .r11 = (x >>> 12) ^^^ y ∧
      (∀ r, r ≠ .rcx → r ≠ .rdi → r ≠ .r13 → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrcx hr13 hr11 ⊢
  have e1 : (0x01#8).signExtend 64 = 1#64 := by decide
  have e12 : (0x0c#8 : BitVec 8).toNat % 64 = 12 := by decide
  refine ex_fC intFreeCode_length hl hrip (by decide) i863
    (e_aluI8r (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_fC intFreeCode_length hl (by simp [hrip, rip_add]) (by decide) i867
    e_shr (fun f2 => ?_)
  refine ex_head (stepC intFreeCode_length (o := 871) (l := 3) hl (by simp [hrip, rip_add]) (by decide) i871
    e_movrr) ?_
  refine ex_fC intFreeCode_length hl (by simp [hrip, rip_add]) (by decide) i874
    e_xorrr (fun f3 => ?_)
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [hrip, rip_add]
  · simp [Silmaril.X86.Ext.AluOp.resultN, e1, hrcx]; rw [BitVec.ofNat_add]
  · simp [hr13, e12]
  · simp [hr13, hr11, e12, xor_cancel_left]
  · simp [hr11]
  · intro r a b c; simp [a, b, c]

set_option maxHeartbeats 4000000 in
/-- Offsets `0x36d`–`0x375`: back to `0x87` if the revealed next is null, else on to the next
turn. -/
theorem int_walk_s4 {m : MState} {B x y : Word} (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 877)
    (hr13 : m.core.read .r13 = x >>> 12) (hr11 : m.core.read .r11 = (x >>> 12) ^^^ y) :
    ∃ m', Reaches Str9Fs.step m m' ∧
      ((y = 0 ∧ m'.core.rip = B + BitVec.ofNat 64 135) ∨ (y ≠ 0 ∧ m'.core.rip = B + BitVec.ofNat 64 886)) ∧
      (∀ r, m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hr13 hr11 ⊢
  refine ex_head (stepC intFreeCode_length (o := 877) (l := 3) hl hrip (by decide) i877 e_cmprr) ?_
  by_cases hy : y = 0
  · refine ex_jccA intFreeCode_length (o := 880) (l := 6) (tgt := 135) (b := true) hl
      (by simp [hrip, rip_add]) (by decide) i880 (by
        simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, zf_sub, nxf_read, nx_read]
        simp [hr13, hr11, hy]) (by simp [BitVec.add_assoc]) (fun t1 rip1 reg1 fs1 mem1 => ?_)
    exact ex_done ⟨Or.inl ⟨hy, rip1⟩, fun r => by rw [reg1]; rfl, by rw [fs1]; rfl, mem1⟩
  · refine ex_jccA intFreeCode_length (o := 880) (l := 6) (tgt := 886) (b := false) hl
      (by simp [hrip, rip_add]) (by decide) i880 (by
        have hy' : ¬ y = 0#64 := hy
        simp only [Silmaril.X86.Ext.Cond.eval, nxf_flags, zf_sub, nxf_read, nx_read]
        simp [hr13, hr11, eq_xor_iff, hy, hy']) (by simp [rip_add]) (fun t1 rip1 reg1 fs1 mem1 => ?_)
    exact ex_done ⟨Or.inr ⟨hy, rip1⟩, fun r => by rw [reg1]; rfl, by rw [fs1]; rfl, mem1⟩

/-- **One turn of the walk** (`0x376` … `0x375`): the entry `x = rdi` with count `j = rcx`,
`j < mp_.tcache_count`, `x` aligned and not `e`, holding `PROTECT_PTR (x, y)`: back to `0x87`
if `y` is null, else on to the next turn with `rdi = y`, `rcx = j + 1`. -/
theorem int_walk_step {c : State} {mem : Memory} {B x y e cmax : Word} {j : Nat}
    (hl : Loaded mem B intFreeCode) (hrip : c.rip = B + BitVec.ofNat 64 886)
    (hrdi : c.read .rdi = x) (hrcx : c.read .rcx = BitVec.ofNat 64 j) (hr9 : c.read .r9 = cmax)
    (hr10 : c.read .r10 = e) (hj : j < cmax.toNat) (hal : x.setWidth 8 &&& 0xf#8 = 0) (hxe : x ≠ e)
    (hld : loadN mem x 8 = some ((x >>> 12) ^^^ y)) :
    ∃ m' : MState, Reaches Str9Fs.step ⟨c, mem⟩ m' ∧ m'.memory = mem ∧
      ((y = 0 ∧ m'.core.rip = B + BitVec.ofNat 64 135) ∨ (y ≠ 0 ∧ m'.core.rip = B + BitVec.ofNat 64 886)) ∧
      m'.core.read .rdi = y ∧ m'.core.read .rcx = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .rcx → r ≠ .rdi → r ≠ .r11 → r ≠ .r13 → m'.core.read r = c.read r) ∧
      m'.core.fsBase = c.fsBase := by
  obtain ⟨m1, r1, rip1, fr1, fs1, mem1⟩ := int_walk_s1 (m := ⟨c, mem⟩) hl hrip hrdi hrcx hr9 hj hal
  obtain ⟨m2, r2, rip2, r132, r112, fr2, fs2, mem2⟩ := int_walk_s2 (by rw [mem1]; exact hl) rip1
    (by rw [fr1]; exact hrdi) (by rw [fr1]; exact hr10) hxe (by rw [mem1]; exact hld)
  obtain ⟨m3, r3, rip3, rcx3, r133, rdi3, r113, fr3, fs3, mem3⟩ := int_walk_s3 (y := y)
    (by rw [mem2, mem1]; exact hl) rip2
    (by rw [fr2 _ (by decide) (by decide), fr1]; exact hrcx) r132 r112
  obtain ⟨m4, r4, rip4, fr4, fs4, mem4⟩ := int_walk_s4 (by rw [mem3, mem2, mem1]; exact hl) rip3 r133 r113
  refine ⟨m4, ((r1.trans r2).trans r3).trans r4, by rw [mem4, mem3, mem2, mem1], rip4,
    by rw [fr4, rdi3], by rw [fr4, rcx3], fun r a b c d => ?_, by rw [fs4, fs3, fs2, fs1]⟩
  rw [fr4, fr3 r a b d, fr2 r c d, fr1]


theorem getD_ge {L : List Word} {n : Nat} (h : L.length ≤ n) : L.getD n 0 = 0 := by
  simp [List.getD, List.getElem?_eq_none h]

/-- `TcWalk` survives writes away from the entries. -/
theorem tcWalk_ww {mem mem' : Memory} {fp : Nat → Prop} {h e cmax : Word} {L : List Word}
    (hW : TcWalk mem h e cmax L) (hw : mem.WritesWithin mem' fp)
    (hap : ∀ j < L.length, ∀ i < 8, ¬ fp ((L.getD j 0).toNat + i)) : TcWalk mem' h e cmax L := by
  obtain ⟨h1, h2, h3⟩ := hW
  refine ⟨h1, h2, fun j hj => ?_⟩
  obtain ⟨a, b, c, d⟩ := h3 j hj
  exact ⟨a, b, c, ld_ww hw (hap j hj) d⟩

/-- **The turns of the walk** from entry `j` (`n` entries after it). -/
theorem int_walk_loop {B cmax e : Word} {mem : Memory} {L : List Word}
    (hl : Loaded mem B intFreeCode) (hlen : L.length ≤ cmax.toNat)
    (hw : ∀ j < L.length, L.getD j 0 ≠ 0 ∧ (L.getD j 0).setWidth 8 &&& 0xf#8 = 0 ∧ L.getD j 0 ≠ e ∧
      loadN mem (L.getD j 0) 8 = some ((L.getD j 0 >>> 12) ^^^ L.getD (j + 1) 0)) :
    ∀ (n j : Nat) (c : State), j + n + 1 = L.length → c.rip = B + BitVec.ofNat 64 886 →
      c.read .rdi = L.getD j 0 → c.read .rcx = BitVec.ofNat 64 j → c.read .r9 = cmax →
      c.read .r10 = e →
      ∃ m' : MState, Reaches Str9Fs.step ⟨c, mem⟩ m' ∧ m'.memory = mem ∧
        m'.core.rip = B + BitVec.ofNat 64 135 ∧
        (∀ r, r ≠ .rcx → r ≠ .rdi → r ≠ .r11 → r ≠ .r13 → m'.core.read r = c.read r) ∧
        m'.core.fsBase = c.fsBase := by
  intro n
  induction n with
  | zero =>
    intro j c hj hrip hrdi hrcx hr9 hr10
    obtain ⟨-, hal, hxe, hld⟩ := hw j (by omega)
    obtain ⟨m', hr, hmem, hrip', -, -, hfr, hfs⟩ :=
      int_walk_step hl hrip hrdi hrcx hr9 hr10 (by omega) hal hxe hld
    rcases hrip' with ⟨-, hr'⟩ | ⟨hy, -⟩
    · exact ⟨m', hr, hmem, hr', hfr, hfs⟩
    · exact absurd (getD_ge (by omega)) hy
  | succ n ih =>
    intro j c hj hrip hrdi hrcx hr9 hr10
    obtain ⟨-, hal, hxe, hld⟩ := hw j (by omega)
    obtain ⟨⟨c', mem'⟩, hr, hmem, hrip', hrdi', hrcx', hfr, hfs⟩ :=
      int_walk_step hl hrip hrdi hrcx hr9 hr10 (by omega) hal hxe hld
    simp only at hmem hrip' hrdi' hrcx' hfr hfs
    subst hmem
    rcases hrip' with ⟨-, hr'⟩ | ⟨-, hr'⟩
    · exact ⟨_, hr, rfl, hr', hfr, hfs⟩
    · obtain ⟨m'', hr2, hmem2, hrip2, hfr2, hfs2⟩ := ih (j + 1) c' (by omega) hr' hrdi' hrcx'
        (by rw [hfr _ (by decide) (by decide) (by decide) (by decide), hr9])
        (by rw [hfr _ (by decide) (by decide) (by decide) (by decide), hr10])
      refine ⟨m'', hr.trans hr2, hmem2, hrip2, fun r a b c d => ?_, by rw [hfs2, hfs]⟩
      rw [hfr2 r a b c d, hfr r a b c d]

theorem getD_zero_headW {L : List Word} : L.getD 0 0 = L.headD 0 := by
  cases L <;> rfl

set_option maxHeartbeats 4000000 in
/-- **The walk** from `0x330` to the count test at `0x87`: memory unchanged, `r8 = tc`,
`r9 = mp_.tcache_count`. -/
theorem int_walk {m : MState} {B offT tc idx cmax e h : Word} {L : List Word}
    (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 816) (hrdi : m.core.read .rdi = offT)
    (hrax : m.core.read .rax = idx) (hr10 : m.core.read .r10 = e) (hrcx : m.core.read .rcx = 0)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc)
    (hcmax : loadN m.memory (B + 0x158fa8#64) 8 = some cmax)
    (hent : loadN m.memory (tc + (idx <<< 3) + 0x80#64) 8 = some h)
    (hW : TcWalk m.memory h e cmax L) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 135 ∧
      m'.core.read .r8 = tc ∧ m'.core.read .r9 = cmax ∧
      (∀ r, r ≠ .rcx → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r13 →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨hhd, hlen, hw⟩ := hW
  obtain ⟨⟨c1, mem1⟩, r1, hrip1, rdi1, r81, r91, fr1, fs1, mem1e⟩ :=
    int_walk0 hl hrip hrdi hrax htc hcmax hent
  simp only at hrip1 rdi1 r81 r91 fr1 fs1 mem1e
  rcases hrip1 with ⟨-, hr⟩ | ⟨hh, hr⟩
  · exact ⟨_, r1, hr, r81, r91, fun r a b c d e f => fr1 r b c d, fs1, mem1e⟩
  · subst mem1e
    have hL : 0 < L.length := by
      cases L with
      | nil => exact absurd hhd.symm (by simpa using hh)
      | cons _ _ => simp
    obtain ⟨m2, r2, mem2, hrip2, fr2, fs2⟩ := int_walk_loop hl hlen hw (L.length - 1) 0 c1 (by omega) hr
      (by rw [rdi1, getD_zero_headW, hhd])
      (by rw [fr1 _ (by decide) (by decide) (by decide), hrcx]; rfl)
      (by rw [r91])
      (by rw [fr1 _ (by decide) (by decide) (by decide), hr10])
    refine ⟨m2, r1.trans r2, hrip2, ?_, ?_, fun r a b c d e f => ?_, by rw [fs2, fs1], mem2⟩
    · rw [fr2 _ (by decide) (by decide) (by decide) (by decide), r81]
    · rw [fr2 _ (by decide) (by decide) (by decide) (by decide), r91]
    · rw [fr2 r a b e f, fr1 r b c d]

set_option maxHeartbeats 4000000 in
/-- **Offsets `0x6b` to the count test at `0x87`**, either branch of the key test: `e->key`
differs from `tcache_key`, or it is equal and the bin is walked (`TcWalk`). -/
theorem int_chk3 {m : MState} {B q offT tc idx cmax key ekey h : Word}
    (hl : Loaded m.memory B intFreeCode)
    (hrip : m.core.rip = B + BitVec.ofNat 64 107) (hrsi : m.core.read .rsi = q)
    (hrdi : m.core.read .rdi = offT) (hr8 : m.core.read .r8 = tc) (hrax : m.core.read .rax = idx)
    (hrcx : m.core.read .rcx = 0)
    (htc : loadN m.memory (m.core.fsBase + offT) 8 = some tc)
    (hcmax : loadN m.memory (B + 0x158fa8#64) 8 = some cmax)
    (hkey : loadN m.memory (B + 0x15ff28#64) 8 = some key)
    (hekey : loadN m.memory (q + 0x18#64) 8 = some ekey)
    (hent : loadN m.memory (tc + (idx <<< 3) + 0x80#64) 8 = some h)
    (hk : ekey ≠ key ∨ ∃ L, TcWalk m.memory h (q + 0x10#64) cmax L) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = B + BitVec.ofNat 64 135 ∧
      m'.core.read .r8 = tc ∧ m'.core.read .r9 = cmax ∧ m'.core.read .r10 = q + 0x10#64 ∧
      (∀ r, r ≠ .rcx → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r13 →
        m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  by_cases hne : ekey = key
  · subst hne
    obtain ⟨L, hW⟩ := hk.resolve_left (fun h => h rfl)
    obtain ⟨⟨c1, mem1⟩, r1, hrip1, r101, fr1, fs1, mem1e⟩ := int_chk3a_eq hl hrip hrsi hcmax hkey hekey
    simp only at hrip1 r101 fr1 fs1 mem1e
    subst mem1e
    obtain ⟨m2, r2, hrip2, r82, r92, fr2, fs2, mem2⟩ := int_walk (m := ⟨c1, m.memory⟩) hl hrip1
      (by rw [fr1 _ (by decide) (by decide) (by decide), hrdi])
      (by rw [fr1 _ (by decide) (by decide) (by decide), hrax]) r101
      (by rw [fr1 _ (by decide) (by decide) (by decide), hrcx])
      (by rw [fs1]; exact htc) hcmax hent hW
    refine ⟨m2, r1.trans r2, hrip2, r82, r92, ?_, fun r a b c d e f g => ?_, by rw [fs2, fs1], mem2⟩
    · rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r101]
    · rw [fr2 r a b c d f g, fr1 r d e f]
  · obtain ⟨m1, r1, hrip1, r91, r111, r101, fr1, fs1, mem1⟩ := int_chk3a hl hrip hrsi hcmax hkey hekey hne
    refine ⟨m1, r1, hrip1, by rw [fr1 _ (by decide) (by decide) (by decide), hr8], r91, r101,
      fun r a b c d e f g => fr1 r d e f, fs1, mem1⟩

end Silmaril.Libc.Ptmalloc.X86sim.V239
