module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Basic
public import Silmaril.X86.BlockCert9.Thms

/-! # The C runtime: `_init`, `_fini`, `frame_dummy` (with `register_tm_clones`) -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_init`**, entered as a callback with `__gmon_start__` unbound: it returns to its return
address with memory and the library state unchanged. -/
theorem crt_init {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte} {W : World}
    (hW : W.InImage = Img L b) (hb : b.toNat + L.size < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : CrtMem L b lsmA cxaA cv s.m.memory)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.init) {ra : Word}
    (hret : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ra]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = ra → t.m.memory = s.m.memory →
      t.m.core.read .rsp = s.m.core.read .rsp + 8#64 → t.m.core.fsBase = s.m.core.fsBase →
      MustQ W Q t) :
    MustQ W Q s := by
  have hs := F.size
  have hi := F.bInit
  have hg := F.bGmon
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => hW ▸ img_add hb hn
  refine must_listed (o := 0) F.lInit rfl hd (by rw [hrip]; exact hin _ (by omega)) hm.init
    (by rw [hrip]; simp) ?_
  xstep [hrip]
  refine must_listed (o := 4) F.lInit rfl hd (hin _ (by omega)) hm.init (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) F.lInit rfl hd (hin _ (by omega)) hm.init (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.init + 15) (y := L.gotGmon) (by omega) (by omega), hm.gGmon]
  refine must_listed (o := 15) F.lInit rfl hd (hin _ (by omega)) hm.init (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 18) F.lInit rfl hd (hin _ (by omega)) hm.init (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 22) F.lInit rfl hd (hin _ (by omega)) hm.init (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 26) F.lInit rfl hd (hin _ (by omega)) hm.init (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, Silmaril.X86.Ext.AluOp.resultN, BitVec.sub_add_cancel, hret]
  exact k _ rfl rfl rfl (by simp) rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_fini`**: it returns with memory and the library state unchanged. -/
theorem crt_fini {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte} {W : World}
    (hW : W.InImage = Img L b) (hb : b.toNat + L.size < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : CrtMem L b lsmA cxaA cv s.m.memory)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.fini) {ra : Word}
    (hret : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ra]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = ra → t.m.memory = s.m.memory →
      t.m.core.read .rsp = s.m.core.read .rsp + 8#64 → t.m.core.fsBase = s.m.core.fsBase →
      MustQ W Q t) :
    MustQ W Q s := by
  have hs := F.size
  have hi := F.bFini
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => hW ▸ img_add hb hn
  refine must_listed (o := 0) F.lFini rfl hd (by rw [hrip]; exact hin _ (by omega)) hm.fini
    (by rw [hrip]; simp) ?_
  xstep [hrip]
  refine must_listed (o := 4) F.lFini rfl hd (hin _ (by omega)) hm.fini (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) F.lFini rfl hd (hin _ (by omega)) hm.fini (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 12) F.lFini rfl hd (hin _ (by omega)) hm.fini (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, Silmaril.X86.Ext.AluOp.resultN, BitVec.sub_add_cancel, hret]
  exact k _ rfl rfl rfl (by simp) rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`frame_dummy`**, a tail call of `register_tm_clones`, with `_ITM_registerTMCloneTable`
unbound and the clone table empty: it returns with memory and the library state unchanged. -/
theorem crt_fdummy {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {cv : Byte} {W : World}
    (hW : W.InImage = Img L b) (hb : b.toNat + L.size < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : CrtMem L b lsmA cxaA cv s.m.memory)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.fdummy) {ra : Word}
    (hret : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ra]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = ra → t.m.memory = s.m.memory →
      t.m.core.read .rsp = s.m.core.read .rsp + 8#64 → t.m.core.fsBase = s.m.core.fsBase →
      MustQ W Q t) :
    MustQ W Q s := by
  have hs := F.size
  have hi := F.bFdummy
  have hr := F.bReg
  have ht := F.bTmc
  have htc_ := F.tc
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => hW ▸ img_add hb hn
  refine must_listed (o := 0) F.lFdummy rfl hd (by rw [hrip]; exact hin _ (by omega)) hm.fdummy
    (by rw [hrip]; simp) ?_
  xstep [hrip]
  refine must_listed (o := 4) F.lFdummy rfl hd (hin _ (by omega)) hm.fdummy (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.fdummy + 4 + 5) (y := L.reg) (by omega) (by omega)]
  refine must_listed (o := 0) F.lReg rfl hd (hin _ (by omega)) hm.reg (by simp) ?_
  xstep []
  refine must_listed (o := 7) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.reg + 7) (y := L.tmc) (by omega) (by omega)]
  refine must_listed (o := 14) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [relAddr b (x := L.reg + 7 + 7) (y := L.tmc) (by omega) (by omega)]
  refine must_listed (o := 17) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, Silmaril.X86.Ext.ShiftOp.result, Silmaril.X86.Ext.ShiftOp.flags]
  refine must_listed (o := 20) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, Silmaril.X86.Ext.ShiftOp.result, Silmaril.X86.Ext.ShiftOp.flags]
  refine must_listed (o := 24) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, Silmaril.X86.Ext.ShiftOp.result, Silmaril.X86.Ext.ShiftOp.flags]
  refine must_listed (o := 28) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, Silmaril.X86.Ext.ShiftOp.result, Silmaril.X86.Ext.ShiftOp.flags]
  refine must_listed (o := 31) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, Silmaril.X86.Ext.ShiftOp.result, Silmaril.X86.Ext.ShiftOp.flags]
  refine must_listed (o := 34) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, BitVec.sub_self, Silmaril.X86.Ext.ShiftOp.result, Silmaril.X86.Ext.ShiftOp.flags, Silmaril.X86.Ext.isZeroN]
  refine must_listed (o := 56) F.lReg rfl hd (hin _ (by omega)) hm.reg (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hret]
  exact k _ rfl rfl rfl (by simp) rfl

end Silmaril.Elf.Link.Dyn.Crt
