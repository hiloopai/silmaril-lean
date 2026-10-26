module

public import Silmaril.X86.SegVC.Tactic
public import Silmaril.X86.Ext8.Basic

/-!
# `seg_vc8`: the segment VC tactic over the `Ext8` variant

`seg_vc` unfolds `SegVC.wpN` for instances whose executor is `X86.Ext.exec`. An instance over
the `Ext8` variant (such as `X86Sys.Isa.sys8`) executes `X86.Ext8.exec`, which is `Ext.exec`
on `base` instructions (`Ext8.exec_base`) and `Ext8.execNew` on the new byte forms. The
lemmas here put both in the shape `seg_vc` expects:

* `exec8_base`, `exec8_new`: dispatch;
* `execNew_*`: the new forms with a register or memory byte operand, one equation each, as
  `retire` of the result (`seg_vc` then finishes them like any `X86.Ext` instruction: stores
  meet `onOk_retire_storeN`, loads are left as `loadN` facts);
* `BReg.read`/`BReg.write` of the low and the legacy high byte registers (`movzbl %ah`).

`seg_vc8 [lemmas]` is `seg_vc` with these lemmas added.

Everything here is VERIFIED (no `sorry`, no new axiom): every lemma is `rfl`.
-/

@[expose] public section

namespace Silmaril.X86.SegVC

open Silmaril.X86 (State Word Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Result retire loadN storeN Sz)
open Silmaril.X86.Ext8 (BReg RM8 New)

theorem exec8_base (i : Ext.Instr) (s : State) (m : Memory) (l : Nat) :
    Ext8.exec (.base i) s m l = Ext.exec i s m l := rfl

theorem exec8_new (i : New) (s : State) (m : Memory) (l : Nat) :
    Ext8.exec (.new i) s m l = Ext8.execNew i s m (s.rip + BitVec.ofNat 64 l) := rfl

theorem bread_low (s : State) (r : Reg) : (BReg.low r).read s = (s.read r).setWidth 8 := rfl
theorem bread_high (s : State) (r : Reg) :
    (BReg.high r).read s = (s.read r).extractLsb' 8 8 := rfl

theorem bwrite_low (s : State) (r : Reg) (v : BitVec 8) :
    (BReg.low r).write s v = Ext.writeByte s r v := rfl
theorem bwrite_high (s : State) (r : Reg) (v : BitVec 8) :
    (BReg.high r).write s v = s.write r ((s.read r &&& ~~~(0xFF00#64)) ||| (v.setWidth 64 <<< 8)) :=
  rfl

/-- `movzx`/`movsx r, r8`. -/
theorem execNew_movx_reg (sx : Bool) (sz : Sz) (dst : Reg) (b : BReg) (s : State) (m : Memory)
    (next : Word) :
    Ext8.execNew (.movx sx sz dst (.reg b)) s m next =
      retire next (some (sz.write s dst
        (if sx then (b.read s).signExtend sz.bits else (b.read s).setWidth sz.bits), m)) := rfl

/-- `movzx`/`movsx r, m8`. -/
theorem execNew_movx_mem (sx : Bool) (sz : Sz) (dst : Reg) (a : Ext.Mem) (s : State) (m : Memory)
    (next : Word) :
    Ext8.execNew (.movx sx sz dst (.mem a)) s m next =
      retire next ((loadN m (a.addr s next) 1).map fun v =>
        (sz.write s dst (if sx then (v.setWidth 8).signExtend sz.bits
          else (v.setWidth 8).setWidth sz.bits), m)) := by
  simp only [Ext8.execNew, RM8.read, Option.map_map]
  rfl

/-- `mov m8, r8`: a byte store. -/
theorem execNew_mov_mem (a : Ext.Mem) (b : BReg) (s : State) (m : Memory) (next : Word) :
    Ext8.execNew (.mov (.mem a) b) s m next =
      retire next ((storeN m (a.addr s next) 1 ((b.read s).setWidth 64)).map fun after => (s, after)) :=
  rfl

/-- `mov r8, r8`. -/
theorem execNew_mov_reg (d b : BReg) (s : State) (m : Memory) (next : Word) :
    Ext8.execNew (.mov (.reg d) b) s m next = retire next (some (d.write s (b.read s), m)) := rfl

/-- `mov r8, m8`. -/
theorem execNew_movR_mem (d : BReg) (a : Ext.Mem) (s : State) (m : Memory) (next : Word) :
    Ext8.execNew (.movR d (.mem a)) s m next =
      retire next ((loadN m (a.addr s next) 1).map fun v => (d.write s (v.setWidth 8), m)) := by
  simp only [Ext8.execNew, RM8.read, Option.map_map]
  rfl

/-- `test r8, r8`. -/
theorem execNew_test_reg (d b : BReg) (s : State) (m : Memory) (next : Word) :
    Ext8.execNew (.test (.reg d) b) s m next =
      retire next (some ({ s with flags := Ext.logicFlagsN (d.read s &&& b.read s) }, m)) := rfl

/-- `op r8, r8` (ADD OR AND SUB XOR CMP). -/
theorem execNew_alu_reg (op : Silmaril.X86.AluOp) (d b : BReg) (s : State) (m : Memory)
    (next : Word) :
    Ext8.execNew (.alu op (.reg d) b) s m next =
      retire next (if op = .cmp then
          some ({ s with flags := Ext.AluOp.flagsN op (d.read s) (b.read s) }, m)
        else some ({ d.write s (Ext.AluOp.resultN op (d.read s) (b.read s)) with
          flags := Ext.AluOp.flagsN op (d.read s) (b.read s) }, m)) := by
  simp only [Ext8.execNew, Ext8.alu8, RM8.read, RM8.write]
  split <;> rfl

/-- `op al, imm8`. -/
theorem execNew_aluA (op : Silmaril.X86.AluOp) (imm : BitVec 8) (s : State) (m : Memory)
    (next : Word) :
    Ext8.execNew (.aluA op imm) s m next =
      retire next (if op = .cmp then
          some ({ s with flags := Ext.AluOp.flagsN op ((s.read .rax).setWidth 8) imm }, m)
        else some ({ Ext.writeByte s .rax (Ext.AluOp.resultN op ((s.read .rax).setWidth 8) imm) with
          flags := Ext.AluOp.flagsN op ((s.read .rax).setWidth 8) imm }, m)) := by
  simp only [Ext8.execNew, Ext8.alu8, RM8.read, RM8.write, BReg.read, BReg.write]
  split <;> rfl

/-- `seg_vc8 [lemmas]`: `seg_vc` over an `Ext8` instance (`X86Sys.Isa.sys8`). -/
syntax "seg_vc8 " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| seg_vc8 [$ls,*]) => `(tactic|
    seg_vc [Silmaril.X86.SegVC.exec8_base, Silmaril.X86.SegVC.exec8_new,
      Silmaril.X86.SegVC.execNew_movx_reg, Silmaril.X86.SegVC.execNew_movx_mem,
      Silmaril.X86.SegVC.execNew_mov_mem, Silmaril.X86.SegVC.execNew_mov_reg,
      Silmaril.X86.SegVC.execNew_movR_mem, Silmaril.X86.SegVC.execNew_test_reg,
      Silmaril.X86.SegVC.execNew_alu_reg, Silmaril.X86.SegVC.execNew_aluA,
      Silmaril.X86.SegVC.bread_low, Silmaril.X86.SegVC.bread_high,
      Silmaril.X86.SegVC.bwrite_low, Silmaril.X86.SegVC.bwrite_high, $ls,*])

end Silmaril.X86.SegVC
