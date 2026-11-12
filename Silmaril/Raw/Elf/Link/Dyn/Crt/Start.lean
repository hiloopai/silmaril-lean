module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Dtors

/-! # The C runtime: `_start` up to the call of `__libc_start_main`

The same proof as `Hello.gcc_start` (for hello-gcc's own placement), over every layout. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`_start`**: to `__libc_start_main` with `rdi = main`, `rsi = argc`, `rdx = argv`, a
System V entry and the image facts intact. -/
theorem crt_start {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte} {W : World}
    (E : CrtEnv L W b lsmA cxaA) {Q : PState → Prop} {s : PState} (hd : s.g.done = none)
    (hm : CrtMem L b lsmA cxaA cv s.m.memory) (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.start)
    (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom W s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = lsmA → CrtMem L b lsmA cxaA cv t.m.memory →
      Keeps W.Kept s.m.memory t.m.memory → t.m.core.fsBase = s.m.core.fsBase →
      AbiEntry t.m.core t.m.memory → t.m.core.read .rdi = b + BitVec.ofNat 64 L.main →
      t.m.core.read .rsi = argc → t.m.core.read .rdx = s.m.core.read .rsp + 8#64 →
      MustQ W Q t) :
    MustQ W Q s := by
  have hs := F.size
  have hst := F.bStart
  have hmn := F.bMain
  have hl := F.bLsm
  have hb := E.hb
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => E.hW ▸ img_add hb hn
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have k1 := keeps_push (v := s.m.core.read .rax) E.hW hroom (sp' := s.m.core.read .rsp)
    (by omega) (by omega)
  have hm1 : CrtMem L b lsmA cxaA cv (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)) :=
    hm.keep F hb k1
  have k2 := keeps_push (m := pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
    (v := s.m.core.read .rsp - 8#64) E.hW hroom.pushMem (sp' := s.m.core.read .rsp - 8#64)
    (by omega) (by omega)
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have hm2 : CrtMem L b lsmA cxaA cv (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
      (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)) :=
    hm1.keep F hb k2
  have p3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inr rfl) (by omega) (by omega)
  have r3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .read
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inl rfl) (by omega) (by omega)
  have k3 := keeps_push (m := pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
    (v := b + BitVec.ofNat 64 (L.start + 37)) E.hW hroom.pushMem.pushMem
    (sp' := s.m.core.read .rsp - 8#64 - 8#64) (by omega) (by omega)
  have hm3 : CrtMem L b lsmA cxaA cv (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
      (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
      (s.m.core.read .rsp - 8#64 - 8#64) (b + BitVec.ofNat 64 (L.start + 37))) :=
    hm2.keep F hb k3
  have k123 := ((keeps_push_kept (v := s.m.core.read .rax) hroom (sp' := s.m.core.read .rsp)
    (by omega) (by omega)).trans (keeps_push_kept (m := pushMem s.m.memory (s.m.core.read .rsp)
      (s.m.core.read .rax)) (v := s.m.core.read .rsp - 8#64) hroom.pushMem
      (sp' := s.m.core.read .rsp - 8#64) (by omega) (by omega))).trans
    (keeps_push_kept (m := pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
      (v := b + BitVec.ofNat 64 (L.start + 37)) hroom.pushMem.pushMem
      (sp' := s.m.core.read .rsp - 8#64 - 8#64) (by omega) (by omega))
  have hret := pushMem_read (v := b + BitVec.ofNat 64 (L.start + 37)) r3 p3
  refine must_listed (o := 0) F.lStart rfl hd (by rw [hrip]; exact hin _ (by omega)) hm.start
    (by rw [hrip]; simp) ?_
  xstep [hrip]
  refine must_listed (o := 4) F.lStart rfl hd (hin _ (by omega)) hm.start (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 6) F.lStart rfl hd (hin _ (by omega)) hm.start (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 9) F.lStart rfl hd (hin _ (by omega)) hm.start (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hargc]
  refine must_listed (o := 10) F.lStart rfl hd (hin _ (by omega)) hm.start (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 13) F.lStart rfl hd (hin _ (by omega)) hm.start (by rw [ripadd]) ?_
  xstep []
  rw [and16 hal (by omega)]
  refine must_listed (o := 17) F.lStart rfl hd (hin _ (by omega)) hm.start (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 18) F.lStart rfl hd (hin _ (by omega)) hm1.start (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 19) F.lStart rfl hd (hin _ (by omega)) hm2.start (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 22) F.lStart rfl hd (hin _ (by omega)) hm2.start (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 24) F.lStart rfl hd (hin _ (by omega)) hm2.start (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.start + 24 + 7) (y := L.main) (by omega) (by omega)]
  refine must_listed (o := 31) F.lStart rfl hd (hin _ (by omega)) hm2.start (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.start + 31 + 6) (y := L.gotLsm) (by omega) (by omega)]
  rw [pushWord_mem (by simpa using p3)]
  simp only [hm2.lsm, WP_ok, st_write_regs, st_read_mk]
  refine k _ rfl rfl ?_ ?_ rfl ?_ ?_ ?_ ?_
  · simpa using hm3
  · simpa using k123
  · refine abiEntry_of' (v := b + BitVec.ofNat 64 (L.start + 37)) ?_ ?_
    · simp [e24]; omega
    · simpa using hret
  all_goals simp

end Silmaril.Elf.Link.Dyn.Crt
