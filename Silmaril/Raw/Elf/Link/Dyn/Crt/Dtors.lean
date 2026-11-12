module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Basic
public import Silmaril.X86.BlockCert9.Thms

/-! # The C runtime: `__do_global_dtors_aux` (with `__cxa_finalize` and `deregister_tm_clones`) -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)
open Silmaril.Elf.Link.Dyn.Proc

theorem abiEntry_of' {c : State} {m : Memory} {v : Word} (ha : (c.read .rsp).toNat % 16 = 8)
    (h : m.readBytes (c.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    AbiEntry c m := ⟨ha, by rw [h]; simp [retOf, h]⟩

theorem retOf_of' {c : State} {m : Memory} {v : Word}
    (h : m.readBytes (c.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    retOf c m = v := by
  simp [retOf, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The `.plt.got` stub of `__cxa_finalize`**: a jump to its binding. -/
theorem crt_plt {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte} {W : World}
    (hW : W.InImage = Img L b) (hb : b.toNat + L.size < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : CrtMem L b lsmA cxaA cv s.m.memory)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.plt)
    (k : MustQ W Q ⟨⟨{ s.m.core with rip := cxaA }, s.m.memory⟩, s.g⟩) : MustQ W Q s := by
  have hs := F.size
  have hp := F.bPlt
  have hc := F.bCxa
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => hW ▸ img_add hb hn
  cases hi : L.ibt
  · have hj : pltJ L = 0 := by simp [pltJ, hi]
    refine must_listed (o := 0) (i := .new (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip (rel (L.plt + pltJ L + 6) L.gotCxa))))) (l := 6) F.lPlt (by simp [pltL, hi, pltJ]) hd
      (by rw [hrip]; exact hin _ (by omega)) hm.plt (by rw [hrip]; simp) ?_
    xstep [hrip, pltJ, hi, relAddr b (x := L.plt + 0 + 6) (y := L.gotCxa) (by omega) (by omega),
      hm.cxa]
    exact k
  · have hj : pltJ L = 4 := by simp [pltJ, hi]
    refine must_listed (o := 0) (i := b8 .endbr64) (l := 4) F.lPlt (by simp [pltL, hi]) hd
      (by rw [hrip]; exact hin _ (by omega)) hm.plt (by rw [hrip]; simp) ?_
    xstep [hrip]
    refine must_listed (o := 4) (i := .new (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip (rel (L.plt + pltJ L + 6) L.gotCxa))))) (l := 6) F.lPlt (by simp [pltL, hi, hj, List.lookup]) hd (hin _ (by omega)) hm.plt
      (by rw [ripadd]) ?_
    xstep [pltJ, hi, relAddr b (x := L.plt + 4 + 6) (y := L.gotCxa) (by omega) (by omega), hm.cxa]
    exact k

/-- A push inside a stack room keeps the image. -/
theorem keeps_push {L : Layout} {b : Word} {W : World} (hW : W.InImage = Img L b) {m : Memory}
    {sp v : Word} (hroom : StackRoom W m sp) {sp' : Word} (hlo : sp.toNat - 4096 + 8 ≤ sp'.toNat)
    (hhi : sp'.toNat ≤ sp.toNat + 8) : Keeps (Img L b) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hroom
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  have := (h3 x (by omega) (by omega)).2.2
  exact this (Or.inl (by rw [hW]; exact hx))

/-- Permissions that agree on a span agree on its check. -/
theorem permitted_congr {m m' : Memory} {acc : Access} {a len : Nat}
    (h : ∀ k < len, m'.permits acc (a + k) = m.permits acc (a + k)) (hp : m.Permitted acc a len) :
    m'.Permitted acc a len := by
  unfold Memory.Permitted Memory.checkSpan at *
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp ⊢
  exact ⟨hp.1, fun k hk => by rw [h k hk]; exact hp.2 k hk⟩

/-- A push to addresses outside the image keeps the image. -/
theorem keeps_push_of {L : Layout} {b : Word} {m : Memory} {sp v : Word}
    (hout : ∀ x, (sp - 8#64).toNat ≤ x → x < (sp - 8#64).toNat + 8 → ¬ Img L b x) :
    Keeps (Img L b) m (pushMem m sp v) := by
  apply pushMem_keeps
  intro x hx
  by_contra hc
  exact hout x (by omega) (by omega) hx

/-- An image address lies apart from a stack span of the room. -/
theorem apart_stack {L : Layout} {b : Word} {W : World} (hW : W.InImage = Img L b) {m : Memory}
    {sp : Word} (hroom : StackRoom W m sp) {x a len : Nat} (hx : Img L b x)
    (hlo : sp.toNat - 4096 ≤ a) (hhi : a + len ≤ sp.toNat + 8) : a + len ≤ x ∨ x + 1 ≤ a := by
  by_contra hc
  have := (hroom.2.2 x (by omega) (by omega)).2.2
  exact this (Or.inl (by rw [hW]; exact hx))

/-- A push inside a stack room keeps what the library keeps. -/
theorem keeps_push_kept {W : World} {m : Memory} {sp v : Word} (hroom : StackRoom W m sp)
    {sp' : Word} (hlo : sp.toNat - 4096 + 8 ≤ sp'.toNat) (hhi : sp'.toNat ≤ sp.toNat + 8) :
    Keeps W.Kept m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hroom
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  exact (h3 x (by omega) (by omega)).2.2 hx

/-- `completed.0` read as a byte. -/
theorem loadN_done {L : Layout} {b lsmA cxaA : Word} {cv : Byte} {m : Memory}
    (hm : CrtMem L b lsmA cxaA cv m) :
    loadN m (b + BitVec.ofNat 64 L.cmpl) 1 = some (BitVec.ofNat 64 cv.toNat) := by
  unfold loadN; rw [hm.done]; simp [Silmaril.X86.Ext.leValue]


/-- A slot apart from a push keeps its bytes. -/
theorem slot_push {m : Memory} {sp v : Word} {a : Nat} {x : List Byte}
    (h : m.readBytes a 8 = some x) (hd : a + 8 ≤ (sp - 8#64).toNat ∨ (sp - 8#64).toNat + 8 ≤ a) :
    (pushMem m sp v).readBytes a 8 = some x := by
  rw [Keeps.readBytes (pushMem_keeps (P := fun y => a ≤ y ∧ y < a + 8) (by intro y hy; omega))
    (fun k hk => ⟨by omega, by omega⟩)]
  exact h

/-- A slot kept by a step keeps its bytes. -/
theorem slot_keeps {P : Nat → Prop} {m m' : Memory} (hk : Keeps P m m') {a : Nat} {x : List Byte}
    (h : m.readBytes a 8 = some x) (hP : ∀ k < 8, P (a + k)) : m'.readBytes a 8 = some x := by
  rw [Keeps.readBytes hk hP]; exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem crt_dtors {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {W : World}
    (E : CrtEnv L W b lsmA cxaA) {Q : PState → Prop} {s : PState} (hd : s.g.done = none)
    (hm : CrtMem L b lsmA cxaA 0#8 s.m.memory) (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.dtors)
    (hal : (s.m.core.read .rsp).toNat % 16 = 8) (hroom : StackRoom W s.m.memory (s.m.core.read .rsp))
    {ra : Word} (hret : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ra])) (hat : s.g.atexit = [])
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = ra → CrtMem L b lsmA cxaA 1#8 t.m.memory →
      MustQ W Q t) :
    MustQ W Q s := by
  have hs := F.size
  have hdt := F.bDtors
  have ht := F.bTmc
  have htc_ := F.tc
  have hc := F.bCxa
  have hdso := F.bDso
  have hpl := F.bPlt
  have hdr := F.bDereg
  have hb := E.hb
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => E.hW ▸ img_add hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  refine must_listed (o := 0) F.lDtors rfl hd (by rw [hrip]; exact hin _ (by omega)) hm.dtors
    (by rw [hrip]; simp) ?_
  xstep [hrip]
  refine must_listed (o := 4) F.lDtors rfl hd (hin _ (by omega)) hm.dtors (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.dtors + 4 + 7) (y := L.cmpl) (by omega) (by omega), loadN_done hm, Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, BitVec.sub_zero, Silmaril.X86.Ext.isZeroN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have hm1 := hm.keep F hb (keeps_push (v := s.m.core.read .rbp) E.hW hroom (sp' := s.m.core.read .rsp)
    (by omega) (by omega))
  have hz : (cxaA == 0#64) = false := by simpa using E.cxa_ne
  have hz' : (cxaA - 0#64 == 0#64) = false := by simpa using E.cxa_ne
  refine must_listed (o := 11) F.lDtors rfl hd (hin _ (by omega)) hm.dtors (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, BitVec.sub_zero, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
  refine must_listed (o := 13) F.lDtors rfl hd (hin _ (by omega)) hm.dtors (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 14) F.lDtors rfl hd (hin _ (by omega)) hm1.dtors (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.dtors + 14 + 8) (y := L.gotCxa) (by omega) (by omega), hm1.cxa, hz', beq_iff_eq, E.cxa_ne, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, BitVec.sub_zero, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
  refine must_listed (o := 22) F.lDtors rfl hd (hin _ (by omega)) hm1.dtors (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 25) F.lDtors rfl hd (hin _ (by omega)) hm1.dtors (by rw [ripadd]) ?_
  xstep [hz', beq_iff_eq, E.cxa_ne, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, BitVec.sub_zero, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
  split
  · rename_i heq; simp at heq
  · rename_i heq; simp only [Option.some.injEq] at heq
    exact absurd ((BitVec.sub_zero cxaA).symm.trans (of_decide_eq_true (p := cxaA - 0#64 = 0#64) heq))
      E.cxa_ne
  rename_i heq
  refine must_listed (o := 27) F.lDtors rfl hd (hin _ (by omega)) hm1.dtors (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.dtors + 27 + 7) (y := L.dso) (by omega) (by omega), hm1.dso]
  -- `call __cxa_finalize@plt`
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have r2 : (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)).Permitted .read
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inl rfl) (by omega) (by omega)
  have hm2 := hm1.keep F hb (keeps_push (v := b + BitVec.ofNat 64 (L.dtors + 39)) E.hW hroom.pushMem
    (sp' := s.m.core.read .rsp - 8#64) (by omega) (by omega))
  refine must_listed (o := 34) F.lDtors rfl hd (hin _ (by omega)) hm1.dtors (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep [relAddr b (x := L.dtors + 34 + 5) (y := L.plt) (by omega) (by omega)]
  -- `__cxa_finalize@plt`, then `__cxa_finalize`
  refine crt_plt F E.hW hb hd hm2 (by simp) ?_
  have hr2 := pushMem_read (v := b + BitVec.ofNat 64 (L.dtors + 39)) r2 p2
  refine must_contract hd
    (by rw [E.hW]; exact E.cxa_out) (fun r => extStep_fn (f := .cxaFinalize) E.cxa_gate
      (fun res slots h => E.cxa_res res slots h) E.cxa_fn r) ⟨?_, hat⟩ ?_
  · exact abiEntry_of' (v := b + BitVec.ofNat 64 (L.dtors + 39)) (by simp [e16]; omega)
      (by simpa using hr2)
  rintro t ⟨⟨hab, hkeep⟩, hg, -⟩
  have hsc : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := e16
  have hpc : t.m.core.rip = b + BitVec.ofNat 64 (L.dtors + 39) := by
    rw [hab.pc]; exact retOf_of' (by simpa using hr2)
  have hst : t.m.core.read .rsp = s.m.core.read .rsp - 8#64 := by
    rw [hab.stack]; simp
  have hkimg : Keeps (Img L b) (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (s.m.core.read .rsp - 8#64) (b + BitVec.ofNat 64 (L.dtors + 39))) t.m.memory :=
    Keeps.mono hkeep (fun a ha => Or.inl (Or.inl (by rw [E.hW]; exact ha)))
  have hm3 := hm2.keep F hb hkimg
  have hkst : ∀ a, (s.m.core.read .rsp).toNat - 16 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      t.m.memory.bytes.get? a = (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
        (s.m.core.read .rbp)) (s.m.core.read .rsp - 8#64)
        (b + BitVec.ofNat 64 (L.dtors + 39))).bytes.get? a ∧ ∀ acc, t.m.memory.permits acc a =
        s.m.memory.permits acc a := by
    intro a h1 h2
    have := hkeep a (Or.inr (by simp; omega))
    exact ⟨this.1, fun acc => (this.2 acc).trans rfl⟩
  have hdt' : t.g.done = none := by rw [hg]; exact hd
  have hperm : ∀ k < 24, ∀ acc, t.m.memory.permits acc ((s.m.core.read .rsp).toNat - 16 + k) =
      s.m.memory.permits acc ((s.m.core.read .rsp).toNat - 16 + k) :=
    fun k hk acc => (hkst _ (by omega) (by omega)).2 acc
  have p3 : t.m.memory.Permitted .write (t.m.core.read .rsp - 8#64).toNat 8 := by
    rw [hst, e16]
    exact permitted_congr (fun k hk => hperm k (by omega) _)
      (by have := perm_room (acc := .write) hroom (Or.inr rfl) (a := (s.m.core.read .rsp).toNat - 16)
            (len := 8) (by omega) (by omega); exact this)
  have r3 : t.m.memory.Permitted .read (t.m.core.read .rsp - 8#64).toNat 8 := by
    rw [hst, e16]
    exact permitted_congr (fun k hk => hperm k (by omega) _)
      (by have := perm_room (acc := .read) hroom (Or.inl rfl) (a := (s.m.core.read .rsp).toNat - 16)
            (len := 8) (by omega) (by omega); exact this)
  have hout3 : ∀ x, (t.m.core.read .rsp - 8#64).toNat ≤ x → x < (t.m.core.read .rsp - 8#64).toNat + 8 →
      ¬ Img L b x := by
    rw [hst, e16]; intro x h1 h2
    have := (hroom.2.2 x (by omega) (by omega)).2.2
    exact fun hx => this (Or.inl (by rw [E.hW]; exact hx))
  have hm4 := hm3.keep F hb (keeps_push_of (v := b + BitVec.ofNat 64 (L.dtors + 39 + 5)) hout3)
  have hr4 := pushMem_read (v := b + BitVec.ofNat 64 (L.dtors + 39 + 5)) r3 p3
  rw [hst, e16] at hr4
  have haddr : (18446744073709551608 + (18446744073709551608 + (s.m.core.read .rsp).toNat)) %
      18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by omega
  refine must_listed (o := 39) F.lDtors rfl hdt' (by rw [hpc]; exact hin _ (by omega)) hm3.dtors (by rw [hpc, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem p3]
  xstep [hpc, relAddr b (x := L.dtors + 39 + 5) (y := L.dereg) (by omega) (by omega)]
  -- `deregister_tm_clones`
  refine must_listed (o := 0) F.lDereg rfl hdt' (hin _ (by omega)) hm4.dereg (by simp) ?_
  xstep []
  refine must_listed (o := 7) F.lDereg rfl hdt' (hin _ (by omega)) hm4.dereg (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.dereg + 7) (y := L.tmc) (by omega) (by omega)]
  refine must_listed (o := 14) F.lDereg rfl hdt' (hin _ (by omega)) hm4.dereg (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.dereg + 7 + 7) (y := L.tmc) (by omega) (by omega)]
  refine must_listed (o := 17) F.lDereg rfl hdt' (hin _ (by omega)) hm4.dereg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
  refine must_listed (o := 40) F.lDereg rfl hdt' (hin _ (by omega)) hm4.dereg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hst, haddr, hr4]
  have hm4' := hm4
  rw [hst] at hm4'
  refine must_listed (o := 44) F.lDtors rfl hdt' (hin _ (by omega)) hm4'.dtors (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.dtors + 44 + 7) (y := L.cmpl) (by omega) (by omega)]
  obtain ⟨m5, hs5, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := 1#64) hm4'.wDone
  xstep [Silmaril.X86.Ext.writeRM8, relAddr b (x := L.dtors + 39 + 5 + 7) (y := L.cmpl) (by omega) (by omega),
    hs5]
  have hm5 := hm4'.store_done F hb hs5
  have hS5 := Silmaril.X86.Ext.Stored.of_storeN hs5
  have htm : Img L b (b + BitVec.ofNat 64 L.cmpl).toNat := img_add hb (by omega)
  have st5 : ∀ a, (s.m.core.read .rsp).toNat - 4096 ≤ a → a + 8 ≤ (s.m.core.read .rsp).toNat + 8 →
      m5.readBytes a 8 = (pushMem t.m.memory (s.m.core.read .rsp - 8#64)
        (b + BitVec.ofNat 64 (L.dtors + 39 + 5))).readBytes a 8 := by
    intro a h1 h2
    have := apart_stack E.hW hroom htm h1 h2
    exact hS5.readWith_disjoint _ _ _ (by simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]; omega)
  have r1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inl rfl) (by omega) (by omega)
  have c1 := pushMem_read (v := s.m.core.read .rbp) r1 p1
  have c2 := slot_push (sp := s.m.core.read .rsp - 8#64) (v := b + BitVec.ofNat 64 (L.dtors + 39)) c1
    (Or.inr (by rw [e16, e8]; omega))
  have c3 := slot_keeps hkeep c2 (fun k hk => Or.inr (by simp; omega))
  have c4 := slot_push (sp := s.m.core.read .rsp - 8#64) (v := b + BitVec.ofNat 64 (L.dtors + 39 + 5)) c3
    (Or.inr (by rw [e16, e8]; omega))
  rw [← st5 _ (by omega) (by omega), e8] at c4
  have d1 := slot_push (sp := s.m.core.read .rsp) (v := s.m.core.read .rbp) hret (Or.inr (by rw [e8]; omega))
  have d2 := slot_push (sp := s.m.core.read .rsp - 8#64) (v := b + BitVec.ofNat 64 (L.dtors + 39)) d1
    (Or.inr (by rw [e16]; omega))
  have d3 := slot_keeps hkeep d2 (fun k hk => Or.inr (by simp; omega))
  have d4 := slot_push (sp := s.m.core.read .rsp - 8#64) (v := b + BitVec.ofNat 64 (L.dtors + 39 + 5)) d3
    (Or.inr (by rw [e16]; omega))
  rw [← st5 _ (by omega) (by omega)] at d4
  have haddr8 : (18446744073709551608 + (s.m.core.read .rsp).toNat) % 18446744073709551616 =
      (s.m.core.read .rsp).toNat - 8 := by omega
  refine must_listed (o := 51) F.lDtors rfl hdt' (hin _ (by omega)) hm5.dtors (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, haddr8, c4]
  refine must_listed (o := 52) F.lDtors rfl hdt' (hin _ (by omega)) hm5.dtors (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, BitVec.sub_add_cancel, d4]
  exact k _ hg rfl hm5

end Silmaril.Elf.Link.Dyn.Crt
