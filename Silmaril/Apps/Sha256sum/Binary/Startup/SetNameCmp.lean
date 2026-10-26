module

public import Silmaril.Apps.Sha256sum.Binary.Startup.SetNameSlash

/-! # `set_program_name` (`sha256sum-min`): `cmp r8, m8` for the `/` case loops

The `"/.libs/"` and `"lt-"` loops compare a byte of `argv[0]` with one of `.rodata` by
`cmp r8, m8` (`.new (.aluR .cmp _ (.mem _))`, at `0x40347b` and `0x4036ef`). Through
`execNew_aluR` and `rm8_read_mem` the load stays under a `match` that `simp` cannot rewrite
with the load's value without exhausting memory (every build ran out of memory at 16-40G).

* `execNew_aluR_cmp_mem` (VERIFIED): the step with the load in `Option.map` form (rewritten
  like the load of `movzx`);
* `cmp_sv`, `cmp_go`: `sv`, `sl_go` with `execNew_aluR_cmp_mem` in place of `execNew_aluR`
  and `rm8_read_mem`.

The loop VCs also keep `rax` a variable `A` with `A = k`: with the literal, an equal literal
`cmp rax, imm` leaves a proof the kernel rejects with deep recursion.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.SetName

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN storeN Mem)
open Silmaril.X86.SegVC

/-- `cmp r8, m8` in map form: `execNew_aluR` with `rm8_read_mem` leaves a `match` on the
load, which `simp` cannot rewrite with the load's value without blowing up; in this form the
load is rewritten like the one of `movzx`. -/
theorem execNew_aluR_cmp_mem (d : Silmaril.X86.Ext8.BReg) (a : Mem) (s : State) (m : Memory)
    (next : Word) :
    Silmaril.X86.Ext8.execNew (.aluR .cmp d (.mem a)) s m next =
      Silmaril.X86.Ext.retire next ((loadN m (a.addr s next) 1).map fun v =>
        ({ s with flags := Silmaril.X86.Ext.AluOp.flagsN .cmp (d.read s) (v.setWidth 8) }, m)) := by
  rcases hv : loadN m (a.addr s next) 1 with _ | v
  · simp [Silmaril.X86.Ext8.execNew, rm8_read_mem, hv, Silmaril.X86.Ext.retire]
  · simp [Silmaril.X86.Ext8.execNew, hv, Silmaril.X86.Ext.retire,
      Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read]

end Silmaril.Apps.Sha256sum.Binary.Startup.SetName

/-- `sv` with `cmp r8, m8` through `execNew_aluR_cmp_mem` (not `execNew_aluR`, `rm8_read_mem`). -/
macro "cmp_sv " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| seg_vc [Silmaril.X86.SegVC.exec8_base, Silmaril.X86.SegVC.exec8_new,
      Silmaril.X86.SegVC.execNew_movx_reg, Silmaril.X86.SegVC.execNew_movx_mem,
      Silmaril.X86.SegVC.execNew_mov_mem, Silmaril.X86.SegVC.execNew_mov_reg,
      Silmaril.X86.SegVC.execNew_movR_mem, Silmaril.X86.SegVC.execNew_test_reg,
      Silmaril.X86.SegVC.execNew_alu_reg, Silmaril.X86.SegVC.execNew_aluA,
      Silmaril.X86.SegVC.bread_low, Silmaril.X86.SegVC.bread_high,
      Silmaril.X86.SegVC.bwrite_low, Silmaril.X86.SegVC.bwrite_high,
      Silmaril.Apps.Sha256sum.Binary.Startup.onOk_retire_push,
      Silmaril.Apps.Sha256sum.Binary.Startup.sub_sub_lit, BitVec.sub_sub, BitVec.reduceAnd,
      BitVec.reduceBEq, BitVec.and_self, Silmaril.Apps.Sha256sum.Binary.Startup.setWidth_8_64,
      Silmaril.Apps.Sha256sum.Binary.Startup.setWidth_8_64_32,
      Silmaril.Apps.Sha256sum.Binary.Startup.setWidth_64_32, false_implies,
      Silmaril.Apps.Sha256sum.Binary.Startup.ofNat_shl, Nat.reduceShiftLeft,
      Silmaril.Apps.Sha256sum.Binary.Startup.SetName.execNew_aluR_cmp_mem,
      Silmaril.X86.Ext.Base.value_rip, Silmaril.X86.Ext.Base.value_none, Silmaril.X86.Ext.Mem.ofRip,
      Silmaril.X86.Ext.Mem.ofIndex, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Lift.ix,
      Silmaril.Apps.Sha256sum.Binary.Startup.write_write_same, $ls,*])

/-- `sl_go` with `cmp_sv`. -/
macro "cmp_go " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (cmp_sv [$ls,*]; ((repeat' sl_split1) <;> sv_close); iterate 60 (all_goals (try (cmp_sv [$ls,*]; ((repeat' sl_split1) <;> sv_close))))))
