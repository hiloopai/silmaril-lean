module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccStart

/-! # hello-gcc: the callbacks `_init`, `frame_dummy`, `_fini` -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

/-- A callback entered at `f` with the image facts. -/
structure Cb (W : World) (b lb : Word) (t : PState) (f : Word) : Prop where
  rip : t.m.core.rip = f
  al : (t.m.core.read .rsp).toNat % 16 = 8
  ret : t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])
  room : StackRoom W t.m.memory (t.m.core.read .rsp)
  mem : GccMem b lb t.m.memory
  done : t.g.done = none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_init`** (`0x1000`): `__gmon_start__` is 0, so it returns at once. -/
theorem gcc_init {b lb gate : Word} {rel : Bool} (E : GccEnv b lb gate) {Q : PState → Prop}
    {t : PState} (hc : Cb (gccWorld b lb gate rel) b lb t (b + 0x1000#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ (gccWorld b lb gate rel) Q u) :
    MustQ (gccWorld b lb gate rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4018 → (gccWorld b lb gate rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => gcc_in E.hb hn
  have hd := hc.done
  refine must_listed (o := 0) gcc_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hc.rip]
  refine must_listed (o := 4) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hc.mem.gmon]
  refine must_listed (o := 0xf) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x12) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.BlockCert9.eval_e_test]
  refine must_listed (o := 0x16) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x1a) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`frame_dummy`** (`0x1160`) and `register_tm_clones`: `__TMC_END__ - __TMC_END__ = 0`, so
it returns without calling `_ITM_registerTMCloneTable`. -/
theorem gcc_frameDummy {b lb gate : Word} {rel : Bool} (E : GccEnv b lb gate) {Q : PState → Prop}
    {t : PState} (hc : Cb (gccWorld b lb gate rel) b lb t (b + 0x1160#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ (gccWorld b lb gate rel) Q u) :
    MustQ (gccWorld b lb gate rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4018 → (gccWorld b lb gate rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => gcc_in E.hb hn
  have hd := hc.done
  refine must_listed (o := 0x160) gcc_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 0x164) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xe0) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xe7) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xee) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xf1) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xf4) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xf8) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xfc) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xff) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x102) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  have hz : Silmaril.X86.Ext.Cond.eval
      (Silmaril.X86.Ext.ShiftOp.sar.flags
        (Silmaril.X86.Ext.ShiftOp.shr.result (0#64) 63 + Silmaril.X86.Ext.ShiftOp.sar.result (0#64) 3) 1
        (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.add (Silmaril.X86.Ext.ShiftOp.shr.result (0#64) 63)
          (Silmaril.X86.Ext.ShiftOp.sar.result (0#64) 3))) Silmaril.X86.Ext.Cond.e = some true := by
    decide
  xstep [hz]
  refine must_listed (o := 0x118) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl rfl

end Silmaril.Elf.Link.Dyn.Hello
