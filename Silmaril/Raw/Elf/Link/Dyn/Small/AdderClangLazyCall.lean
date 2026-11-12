module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangLazy

/-! # The adder (clang), lazy binding: a first call through the PLT

`lazy_scanf`, `lazy_printf`: from the PLT entry of an unbound import (`jmp *slot` with the slot
holding the entry's `push $j`), the process runs `push $j; jmp PLT0; push GOT[1]; jmp *GOT[2]`
and the resolver contract, and arrives at the import with the stack, the argument and
callee-saved registers and the library state of the call, and memory unchanged except the
slot and the two words pushed below the stack pointer.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt

theorem loadN_of_word' {m : Memory} {a v : Word}
    (h : m.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    loadN m a 8 = some v := by
  rw [← Silmaril.X86.Ext.leBytes_eight] at h
  simp only [loadN, h, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt v.isLt]

theorem read_wrsp (c : State) (v rip : Word) (fl : Silmaril.X86.Flags) (fs : Word) {r : Reg}
    (h : r ≠ .rsp) :
    ({ regs := c.regs.write .rsp v, rip := rip, flags := fl, fsBase := fs } : State).read r = c.read r :=
  Silmaril.Machine.RegisterFile.write_other _ _ _ _ h

/-- A lazy PLT entry: `jmp *[rip + d]; push $j; jmp PLT0`. -/
def lstubL (d j r : BitVec 32) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, .new (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip d))), 6), (6, .new (.pushI j), 5),
   (11, b8 (.jmp r), 5)]

/-- `PLT0`: `push [rip + 0x2fca]` (`GOT[1]`); `jmp *[rip + 0x2fcc]` (`GOT[2]`). -/
def plt0L : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 (.pushRM (.mem (Silmaril.X86.Ext.Mem.ofRip 0x2fca#32))), 6),
   (6, .new (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip 0x2fcc#32))), 6)]

theorem plt0L_ok : listingOk [0xff, 0x35, 0xca, 0x2f, 0x00, 0x00, 0xff, 0x25, 0xcc, 0x2f, 0x00, 0x00]
    plt0L = true := by decide +kernel
theorem lstub1_ok : listingOk [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0xe9,
    0xd0, 0xff, 0xff, 0xff] (lstubL 0x2fc2#32 1#32 0xffffffd0#32) = true := by decide +kernel
theorem lstub0_ok : listingOk [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00, 0x68, 0x00, 0x00, 0x00, 0x00, 0xe9,
    0xe0, 0xff, 0xff, 0xff] (lstubL 0x2fca#32 0#32 0xffffffe0#32) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A first call of `__isoc99_scanf` under lazy binding.** -/
theorem lazy_scanf {b lb gate res : Word} {rel : Bool} (P : AdderPlacedL b lb gate res)
    {Q : PState → Prop} {s : PState} (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 0x1040) (hpl : PltL b res s.m.memory)
    (hsp : 32 ≤ (s.m.core.read .rsp).toNat)
    (hst : ∀ a, (s.m.core.read .rsp).toNat - 32 ≤ a → a < (s.m.core.read .rsp).toNat →
      s.m.memory.permits .read a = true ∧ s.m.memory.permits .write a = true ∧
      ¬ (adderClangWorldL b lb gate res rel).Kept a)
    (k : ∀ u : PState, u.m.core.rip = scanfAt lb → u.m.core.read .rsp = s.m.core.read .rsp →
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax, .rbx, .rbp, .r12, .r13, .r14, .r15],
        u.m.core.read r = s.m.core.read r) → u.g = s.g →
      Keeps (fun a => ¬ (b.toNat + 0x4008 ≤ a ∧ a < b.toNat + 0x4010) ∧
        ((adderClangWorldL b lb gate res rel).Kept a ∨ (s.m.core.read .rsp).toNat ≤ a))
        s.m.memory u.m.memory →
      (∀ a acc, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat →
        u.m.memory.permits acc a = s.m.memory.permits acc a) →
      MustQ (adderClangWorldL b lb gate res rel) Q u) :
    MustQ (adderClangWorldL b lb gate res rel) Q s := by
  have hb := P.base.base.hb
  have hin : ∀ n, n < 0x4028 → (adderClangWorldL b lb gate res rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => img_add (L := adderClangLayout) hb hn
  have hc1 : Loaded s.m.memory (b + BitVec.ofNat 64 0x1040) [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00, 0x68,
      0x01, 0x00, 0x00, 0x00, 0xe9, 0xd0, 0xff, 0xff, 0xff] :=
    hpl.code (0x1040, _) (by simp [adderClangPltL])
  have hc0 : Loaded s.m.memory (b + BitVec.ofNat 64 0x1020) [0xff, 0x35, 0xca, 0x2f, 0x00, 0x00, 0xff,
      0x25, 0xcc, 0x2f, 0x00, 0x00] :=
    hpl.code (0x1020, _) (by simp [adderClangPltL])
  have hlt := (s.m.core.read .rsp).isLt
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have perm : ∀ (m : Memory), m.regions = s.m.memory.regions → ∀ acc, acc = .read ∨ acc = .write →
      ∀ a, (s.m.core.read .rsp).toNat - 32 ≤ a → a + 8 ≤ (s.m.core.read .rsp).toNat → m.Permitted acc a 8 := by
    intro m hm acc hacc a h1 h2
    rw [Memory.Permitted, Memory.checkSpan_iff]
    simp only [Silmaril.Process.addressLimit]
    refine ⟨by omega, by omega, fun k hk => ?_⟩
    have := hst (a + k) (by omega) (by omega)
    unfold Memory.permits at this ⊢
    rw [hm]
    rcases hacc with rfl | rfl
    · exact this.1
    · exact this.2.1
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inr rfl) _ (by rw [e8]; omega) (by rw [e8]; omega)
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) 1#64).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inr rfl) _ (by rw [e16]; omega) (by rw [e16]; omega)
  have q2 : (pushMem s.m.memory (s.m.core.read .rsp) 1#64).Permitted .read
      (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inl rfl) _ (by rw [e8]; omega) (by rw [e8]; omega)
  have notImg : ∀ x, (s.m.core.read .rsp).toNat - 32 ≤ x → x < (s.m.core.read .rsp).toNat →
      ¬ Img adderClangLayout b x := fun x h1 h2 h => (hst x h1 h2).2.2 (Or.inl h)
  have kp1 : Keeps (Img adderClangLayout b) s.m.memory (pushMem s.m.memory (s.m.core.read .rsp) 1#64) :=
    keeps_push_of (fun x h1 h2 => notImg x (by rw [e8] at h1; omega) (by rw [e8] at h2; omega))
  have kp2 : ∀ w : Word, Keeps (Img adderClangLayout b) (pushMem s.m.memory (s.m.core.read .rsp) 1#64)
      (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (s.m.core.read .rsp - 8#64) w) := fun w =>
    keeps_push_of (fun x h1 h2 => notImg x (by rw [e16] at h1; omega) (by rw [e16] at h2; omega))
  -- `jmp *slot`: the slot holds `push $1`
  refine must_listed (o := 0) lstub1_ok rfl hd (by rw [hrip]; exact hin _ (by decide)) hc1
    (by rw [hrip]; simp) ?_
  xstep [hrip, hpl.slot1]
  -- `push $1`
  refine must_listed (o := 6) lstub1_ok rfl hd (hin _ (by decide)) hc1 (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  -- `jmp PLT0`
  refine must_listed (o := 11) lstub1_ok rfl hd (hin _ (by decide)) (keeps_loaded hb kp1 (by decide) hc1)
    (by rw [ripadd]) ?_
  xstep []
  -- `PLT0`: `push GOT[1]`
  obtain ⟨w, hw⟩ := hpl.got1
  have hw1 : loadN (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (b + 0x3ff0#64) 8 = some w :=
    (keeps_loadN (off := 0x3ff0) hb kp1 (by decide)).trans hw
  refine must_listed (o := 0) plt0L_ok rfl hd (hin _ (by decide)) (keeps_loaded hb kp1 (by decide) hc0)
    (by simp) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.readRM, ofRip_addr, ripadd, Silmaril.X86.Ext.Sz.bytes]
  xstep [hw1]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  -- `jmp *GOT[2]`
  have hg2 : loadN (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (s.m.core.read .rsp - 8#64) w)
      (b + 0x3ff8#64) 8 = some res :=
    (keeps_loadN (off := 0x3ff8) hb ((kp1.trans (kp2 w))) (by decide)).trans hpl.got2
  refine must_listed (o := 6) plt0L_ok rfl hd (hin _ (by decide))
    (keeps_loaded hb (kp1.trans (kp2 w)) (by decide) hc0) (by rw [ripadd]) ?_
  xstep [hg2]
  -- the resolver, for slot 1
  have q1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inl rfl) _ (by rw [e8]; omega) (by rw [e8]; omega)
  have hj0 : loadN (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (s.m.core.read .rsp - 8#64) w)
      (s.m.core.read .rsp - 8#64 - 8#64 + 8#64) 8 = some (BitVec.ofNat 64 1) := by
    rw [BitVec.sub_add_cancel]
    apply loadN_of_word'
    exact slot_push (pushMem_read q1 p1) (Or.inr (by rw [e16, e8]; omega))
  have hA : (b + BitVec.ofNat 64 16392).toNat = b.toNat + 16392 := addr_toNat (by simp [adderClangLayout] at hb; omega)
  refine must_resolveJ (j := 1) (e := (0x4008, scanfAt lb)) hd
    (show ¬ Img adderClangLayout b res.toNat from P.res_out) (show res ≠ gate from P.res_gate) rfl rfl
    (by simp [adderClangJmp]) rfl (by simpa using hj0) ⟨?_, ?_⟩ ?_
  · show (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (s.m.core.read .rsp - 8#64) w).Permitted
      .read (b + BitVec.ofNat 64 0x4008).toNat 8
    exact permitted_congr (fun k hk => by rw [pushMem_permits, pushMem_permits]) hpl.rw1.1
  · show (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (s.m.core.read .rsp - 8#64) w).Permitted
      .write (b + BitVec.ofNat 64 0x4008).toNat 8
    exact permitted_congr (fun k hk => by rw [pushMem_permits, pushMem_permits]) hpl.rw1.2
  rintro t ⟨hrip', hrsp', hregs, -, hkeep, -, hg', hpg⟩
  have hsp16 : t.m.core.read .rsp = s.m.core.read .rsp := by
    rw [hrsp']; simp; bv_omega
  have kpush : Keeps (fun a => (adderClangWorldL b lb gate res rel).Kept a ∨ (s.m.core.read .rsp).toNat ≤ a)
      s.m.memory (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 1#64) (s.m.core.read .rsp - 8#64) w) := by
    refine Keeps.trans (pushMem_keeps fun x hx => ?_) (pushMem_keeps fun x hx => ?_)
    · rw [e8]
      rcases hx with hx | hx
      · by_contra hc; exact (hst x (by omega) (by omega)).2.2 hx
      · omega
    · rw [e16]
      rcases hx with hx | hx
      · by_contra hc; exact (hst x (by omega) (by omega)).2.2 hx
      · omega
  refine k t hrip' hsp16 (fun r hr => ?_) hg' (kpush.mono (fun a h => h.2) |>.trans
    (hkeep.mono fun a h => ⟨?_, ?_⟩)) (fun a acc h1 h2 => hpg a acc (by simp; omega)
      (by simp; omega))
  · rw [hregs r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact read_wrsp _ _ _ _ _ (by decide)
  · show ¬ ((b + BitVec.ofNat 64 16392).toNat ≤ a ∧ a < (b + BitVec.ofNat 64 16392).toNat + 8)
    rw [hA]; intro h'; exact h.1 ⟨by omega, by omega⟩
  · rcases h.2 with h2 | h2
    · exact Or.inl h2
    · right; rw [← hrsp', hsp16]; exact h2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A first call of `printf` under lazy binding (with `scanf` bound or not).** -/
theorem lazy_printf {b lb gate res : Word} {rel : Bool} (P : AdderPlacedL b lb gate res)
    {Q : PState → Prop} {s : PState} (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 0x1030) (hpl : Plt0 b res s.m.memory)
    (hsp : 32 ≤ (s.m.core.read .rsp).toNat)
    (hst : ∀ a, (s.m.core.read .rsp).toNat - 32 ≤ a → a < (s.m.core.read .rsp).toNat →
      s.m.memory.permits .read a = true ∧ s.m.memory.permits .write a = true ∧
      ¬ (adderClangWorldL b lb gate res rel).Kept a)
    (k : ∀ u : PState, u.m.core.rip = printfAt lb → u.m.core.read .rsp = s.m.core.read .rsp →
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rax, .rbx, .rbp, .r12, .r13, .r14, .r15],
        u.m.core.read r = s.m.core.read r) → u.g = s.g →
      Keeps (fun a => ¬ (b.toNat + 0x4000 ≤ a ∧ a < b.toNat + 0x4008) ∧
        ((adderClangWorldL b lb gate res rel).Kept a ∨ (s.m.core.read .rsp).toNat ≤ a))
        s.m.memory u.m.memory →
      (∀ a acc, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat →
        u.m.memory.permits acc a = s.m.memory.permits acc a) →
      MustQ (adderClangWorldL b lb gate res rel) Q u) :
    MustQ (adderClangWorldL b lb gate res rel) Q s := by
  have hb := P.base.base.hb
  have hin : ∀ n, n < 0x4028 → (adderClangWorldL b lb gate res rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => img_add (L := adderClangLayout) hb hn
  have hc1 : Loaded s.m.memory (b + BitVec.ofNat 64 0x1030) [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00, 0x68,
      0x00, 0x00, 0x00, 0x00, 0xe9, 0xe0, 0xff, 0xff, 0xff] :=
    hpl.code (0x1030, _) (by simp [adderClangPltL])
  have hc0 : Loaded s.m.memory (b + BitVec.ofNat 64 0x1020) [0xff, 0x35, 0xca, 0x2f, 0x00, 0x00, 0xff,
      0x25, 0xcc, 0x2f, 0x00, 0x00] :=
    hpl.code (0x1020, _) (by simp [adderClangPltL])
  have hlt := (s.m.core.read .rsp).isLt
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have perm : ∀ (m : Memory), m.regions = s.m.memory.regions → ∀ acc, acc = .read ∨ acc = .write →
      ∀ a, (s.m.core.read .rsp).toNat - 32 ≤ a → a + 8 ≤ (s.m.core.read .rsp).toNat → m.Permitted acc a 8 := by
    intro m hm acc hacc a h1 h2
    rw [Memory.Permitted, Memory.checkSpan_iff]
    simp only [Silmaril.Process.addressLimit]
    refine ⟨by omega, by omega, fun k hk => ?_⟩
    have := hst (a + k) (by omega) (by omega)
    unfold Memory.permits at this ⊢
    rw [hm]
    rcases hacc with rfl | rfl
    · exact this.1
    · exact this.2.1
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inr rfl) _ (by rw [e8]; omega) (by rw [e8]; omega)
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) 0#64).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inr rfl) _ (by rw [e16]; omega) (by rw [e16]; omega)
  have q2 : (pushMem s.m.memory (s.m.core.read .rsp) 0#64).Permitted .read
      (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inl rfl) _ (by rw [e8]; omega) (by rw [e8]; omega)
  have notImg : ∀ x, (s.m.core.read .rsp).toNat - 32 ≤ x → x < (s.m.core.read .rsp).toNat →
      ¬ Img adderClangLayout b x := fun x h1 h2 h => (hst x h1 h2).2.2 (Or.inl h)
  have kp1 : Keeps (Img adderClangLayout b) s.m.memory (pushMem s.m.memory (s.m.core.read .rsp) 0#64) :=
    keeps_push_of (fun x h1 h2 => notImg x (by rw [e8] at h1; omega) (by rw [e8] at h2; omega))
  have kp2 : ∀ w : Word, Keeps (Img adderClangLayout b) (pushMem s.m.memory (s.m.core.read .rsp) 0#64)
      (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (s.m.core.read .rsp - 8#64) w) := fun w =>
    keeps_push_of (fun x h1 h2 => notImg x (by rw [e16] at h1; omega) (by rw [e16] at h2; omega))
  -- `jmp *slot`: the slot holds `push $0`
  refine must_listed (o := 0) lstub0_ok rfl hd (by rw [hrip]; exact hin _ (by decide)) hc1
    (by rw [hrip]; simp) ?_
  xstep [hrip, hpl.slot0]
  -- `push $0`
  refine must_listed (o := 6) lstub0_ok rfl hd (hin _ (by decide)) hc1 (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  -- `jmp PLT0`
  refine must_listed (o := 11) lstub0_ok rfl hd (hin _ (by decide)) (keeps_loaded hb kp1 (by decide) hc1)
    (by rw [ripadd]) ?_
  xstep []
  -- `PLT0`: `push GOT[1]`
  obtain ⟨w, hw⟩ := hpl.got1
  have hw1 : loadN (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (b + 0x3ff0#64) 8 = some w :=
    (keeps_loadN (off := 0x3ff0) hb kp1 (by decide)).trans hw
  refine must_listed (o := 0) plt0L_ok rfl hd (hin _ (by decide)) (keeps_loaded hb kp1 (by decide) hc0)
    (by simp) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.readRM, ofRip_addr, ripadd, Silmaril.X86.Ext.Sz.bytes]
  xstep [hw1]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  -- `jmp *GOT[2]`
  have hg2 : loadN (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (s.m.core.read .rsp - 8#64) w)
      (b + 0x3ff8#64) 8 = some res :=
    (keeps_loadN (off := 0x3ff8) hb ((kp1.trans (kp2 w))) (by decide)).trans hpl.got2
  refine must_listed (o := 6) plt0L_ok rfl hd (hin _ (by decide))
    (keeps_loaded hb (kp1.trans (kp2 w)) (by decide) hc0) (by rw [ripadd]) ?_
  xstep [hg2]
  -- the resolver, for slot 0
  have q1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm _ rfl _ (Or.inl rfl) _ (by rw [e8]; omega) (by rw [e8]; omega)
  have hj0 : loadN (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (s.m.core.read .rsp - 8#64) w)
      (s.m.core.read .rsp - 8#64 - 8#64 + 8#64) 8 = some (BitVec.ofNat 64 0) := by
    rw [BitVec.sub_add_cancel]
    apply loadN_of_word'
    exact slot_push (pushMem_read q1 p1) (Or.inr (by rw [e16, e8]; omega))
  have hA : (b + BitVec.ofNat 64 16384).toNat = b.toNat + 16384 := addr_toNat (by simp [adderClangLayout] at hb; omega)
  refine must_resolveJ (j := 0) (e := (0x4000, printfAt lb)) hd
    (show ¬ Img adderClangLayout b res.toNat from P.res_out) (show res ≠ gate from P.res_gate) rfl rfl
    (by simp [adderClangJmp]) rfl (by simpa using hj0) ⟨?_, ?_⟩ ?_
  · show (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (s.m.core.read .rsp - 8#64) w).Permitted
      .read (b + BitVec.ofNat 64 0x4000).toNat 8
    exact permitted_congr (fun k hk => by rw [pushMem_permits, pushMem_permits]) hpl.rw0.1
  · show (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (s.m.core.read .rsp - 8#64) w).Permitted
      .write (b + BitVec.ofNat 64 0x4000).toNat 8
    exact permitted_congr (fun k hk => by rw [pushMem_permits, pushMem_permits]) hpl.rw0.2
  rintro t ⟨hrip', hrsp', hregs, -, hkeep, -, hg', hpg⟩
  have hsp16 : t.m.core.read .rsp = s.m.core.read .rsp := by
    rw [hrsp']; simp; bv_omega
  have kpush : Keeps (fun a => (adderClangWorldL b lb gate res rel).Kept a ∨ (s.m.core.read .rsp).toNat ≤ a)
      s.m.memory (pushMem (pushMem s.m.memory (s.m.core.read .rsp) 0#64) (s.m.core.read .rsp - 8#64) w) := by
    refine Keeps.trans (pushMem_keeps fun x hx => ?_) (pushMem_keeps fun x hx => ?_)
    · rw [e8]
      rcases hx with hx | hx
      · by_contra hc; exact (hst x (by omega) (by omega)).2.2 hx
      · omega
    · rw [e16]
      rcases hx with hx | hx
      · by_contra hc; exact (hst x (by omega) (by omega)).2.2 hx
      · omega
  refine k t hrip' hsp16 (fun r hr => ?_) hg' (kpush.mono (fun a h => h.2) |>.trans
    (hkeep.mono fun a h => ⟨?_, ?_⟩)) (fun a acc h1 h2 => hpg a acc (by simp; omega)
      (by simp; omega))
  · rw [hregs r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact read_wrsp _ _ _ _ _ (by decide)
  · show ¬ ((b + BitVec.ofNat 64 16384).toNat ≤ a ∧ a < (b + BitVec.ofNat 64 16384).toNat + 8)
    rw [hA]; intro h'; exact h.1 ⟨by omega, by omega⟩
  · rcases h.2 with h2 | h2
    · exact Or.inl h2
    · right; rw [← hrsp', hsp16]; exact h2

end Silmaril.Elf.Link.Dyn.Small

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt
open Silmaril.Elf.Link.Dyn.Stdio

/-- **`main` of `adderClang` under lazy binding meets `MainOk`** (proved:
`adderClangLazyMain_holds`). The second lazy call (`printf`) pushes `$0` and `GOT[1]` below the
first resolver's frame; this relies on `ResPost` and `StdioFrame` keeping the permissions of
the stack page below the entry `rsp`. -/
def Task.adderClangLazyMain : Prop :=
  ∀ (b lb gate res : Word) (rel : Bool), AdderPlacedL b lb gate res →
    MainOk (adderClangWorldL b lb gate res rel) adderClangLayout b (lsmAt lb) (cxaAt lb)
      (fun _ m => PltL b res m) (fun g => scanDD g.inp ≠ .ub) (adderPost rel)

/-- **The adder (clang) under lazy binding, given `Task.adderClangLazyMain`**: under the loader
relation with lazy binding, from every documented initial state whose `stdin` does not overflow
`int` in `scanf`, every run ends as `adderPost` says. Everything but `main` is proved: the
runtime (`crt_run`), the lazy certificate, the PLT facts. -/
theorem adderClangL_run (T : Task.adderClangLazyMain) {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn true res s.m.memory)
    (P : AdderPlacedL b lb gate res)
    (hs : AtEntry adderClangLayout (adderClangWorldL b lb gate res rel) b s)
    (hin : scanDD s.g.inp ≠ .ub) :
    MustQ (adderClangWorldL b lb gate res rel) (Ends s.g (adderPost rel) rel) s := by
  have F := Layout.facts adderClang_ok
  obtain ⟨argc, hargc⟩ := hs.argc
  have hD := adderClang_slots_lazy hc hl
  exact crt_run F (adderClangL_env P) rfl rfl (X := fun _ m => PltL b res m)
    (fun _ _ _ hk hx => hx.keep P.base.base.hb (keeps_img rfl hk))
    (T b lb gate res rel P) hs.done (pltL_of_loaded hc hl hload) hs.atexit
    (crtMem_of_loaded adderClang_info hD adderClang_img_lazy hload) hs.rip hs.al hs.room hargc hin

end Silmaril.Elf.Link.Dyn.Small
