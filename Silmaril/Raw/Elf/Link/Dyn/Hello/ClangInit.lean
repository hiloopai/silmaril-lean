module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.ClangStart

/-! # hello-clang: `_init`, `frame_dummy`, `_fini` -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

/-- A callback entered at `f` with the image facts. -/
structure CCb (W : World) (b lb ps : Word) (t : PState) (f : Word) : Prop where
  rip : t.m.core.rip = f
  al : (t.m.core.read .rsp).toNat % 16 = 8
  ret : t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])
  room : StackRoom W t.m.memory (t.m.core.read .rsp)
  mem : ClangMem b lb ps t.m.memory
  done : t.g.done = none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_init`** (`0x1000`): `__gmon_start__` is 0, so it returns at once. -/
theorem clang_init {b lb gate res ps : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res) {Q : PState → Prop}
    {t : PState} (hc : CCb (clangWorld b lb gate res lazy rel) b lb ps t (b + 0x1000#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ (clangWorld b lb gate res lazy rel) Q u) :
    MustQ (clangWorld b lb gate res lazy rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4020 → (clangWorld b lb gate res lazy rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => clang_in E.hb hn
  have hd := hc.done
  refine must_listed (o := 0) clang_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hc.rip]
  refine must_listed (o := 4) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hc.mem.gmon]
  refine must_listed (o := 0xf) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x12) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.BlockCert9.eval_e_test]
  refine must_listed (o := 0x16) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x1a) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`frame_dummy`** (`0x1130`) and `register_tm_clones`: `__TMC_END__ - __TMC_END__ = 0`, so
it returns without calling `_ITM_registerTMCloneTable`. -/
theorem clang_frameDummy {b lb gate res ps : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res) {Q : PState → Prop}
    {t : PState} (hc : CCb (clangWorld b lb gate res lazy rel) b lb ps t (b + 0x1130#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → u.m.memory = t.m.memory →
      MustQ (clangWorld b lb gate res lazy rel) Q u) :
    MustQ (clangWorld b lb gate res lazy rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4020 → (clangWorld b lb gate res lazy rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => clang_in E.hb hn
  have hd := hc.done
  refine must_listed (o := 0x130) clang_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 0x134) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xb0) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xb7) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xbe) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xc1) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xc4) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xc8) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xcc) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xcf) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0xd2) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  have hz : Silmaril.X86.Ext.Cond.eval
      (Silmaril.X86.Ext.ShiftOp.sar.flags
        (Silmaril.X86.Ext.ShiftOp.shr.result (0#64) 63 + Silmaril.X86.Ext.ShiftOp.sar.result (0#64) 3) 1
        (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.add (Silmaril.X86.Ext.ShiftOp.shr.result (0#64) 63)
          (Silmaril.X86.Ext.ShiftOp.sar.result (0#64) 3))) Silmaril.X86.Ext.Cond.e = some true := by
    decide
  xstep [hz]
  refine must_listed (o := 0xe8) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_fini`** (`0x1154`). -/
theorem clang_fini {b lb gate res ps : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res) {Q : PState → Prop}
    {t : PState} (hc : CCb (clangWorld b lb gate res lazy rel) b lb ps t (b + 0x1154#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → MustQ (clangWorld b lb gate res lazy rel) Q u) :
    MustQ (clangWorld b lb gate res lazy rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4020 → (clangWorld b lb gate res lazy rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => clang_in E.hb hn
  have hd := hc.done
  refine must_listed (o := 0x154) clang_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 0x158) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x15c) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x160) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hc.ret]
  exact k _ rfl rfl

end Silmaril.Elf.Link.Dyn.Hello
