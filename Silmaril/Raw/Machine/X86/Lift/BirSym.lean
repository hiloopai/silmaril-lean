-- Imported from an earlier development
-- Source: Silmaril/X86/Lift/BirSym.lean; sha256=63e186abb2c3c4dac68e39e181ba29731be7f0f5b1baf896066748c9b035d642
-- Reproduce with tools/mor/examples/import_x86_lift.rs; declaration namespaces retained.
module

public import Silmaril.Raw.Machine.X86.Lift.BirInstr

/-!
# `symStep`: the symbolic instruction table, and its soundness

`symStep σ i len` gives the Bir statements and the new symbolic state for one
`LInstr`; `symStep_sound` relates it to `LInstr.exec`. `symExec` folds it over
a block and `symExec_sound` is the block-simulation theorem.
-/

@[expose] public section

namespace Silmaril.X86.Lift.Bir

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

variable {σ : SState} {env : Env} {s : State} {mem : Memory}

theorem Rel.regs_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) (r : Reg) : (σ.regs r).wf n :=
  E.wf_mono hn (h.wf.1 r)

theorem Rel.flags_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) : σ.flags.wf n :=
  F.wf_mono hn h.wf.2.1

theorem Rel.regs_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) (r : Reg) :
    (σ.regs r).den env1 = s.read r := by
  rw [E.den_ext hx (wf_lift h (h.wf.1 r)), h.regs]

theorem Rel.flags_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) :
    σ.flags.den env1 = s.flags := by
  rw [F.den_ext hx (h.len ▸ h.wf.2.1), h.flags]

theorem one_setWidth (sz : Sz) : (1#64).setWidth sz.bits = 1#sz.bits := by cases sz <;> rfl

/-- The 8-bit source operand of an extension ALU form. -/
def Src8.sym (σ : SState) : Src8 → E
  | .reg r => σ.regs r
  | .imm b => .imm (b.setWidth 64)

theorem Src8.sym_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) (src : Src8) :
    ((src.sym σ).den env1).setWidth 8 = src.read s := by
  cases src with
  | reg r => simp [Src8.sym, Src8.read, h.regs_den hx]
  | imm b => simp [Src8.sym, Src8.read, E.den]

theorem Src8.sym_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) (src : Src8) :
    (src.sym σ).wf n := by
  cases src <;> simp [Src8.sym, E.wf, h.regs_wf hn]

/-- The shift count operand. -/
def countSym (σ : SState) : Count → E
  | .cl => σ.regs .rcx
  | .one => .imm 1#64
  | .imm n => .imm (n.setWidth 64)

theorem countSym_den (h : Rel σ env s mem) {env1 : Env} (hx : env.Ext env1) (c : Count) :
    ((countSym σ c).den env1).setWidth 8 = c.raw s := by
  cases c with
  | cl => simp [countSym, Count.raw, h.regs_den hx]
  | one => rfl
  | imm b => simp [countSym, Count.raw, E.den]

theorem countSym_wf (h : Rel σ env s mem) {n : Nat} (hn : σ.n ≤ n) (c : Count) :
    (countSym σ c).wf n := by
  cases c <;> simp [countSym, E.wf, h.regs_wf hn]

/-! ## The table -/

/-- Bits 15:8 of a register, as the low byte of an expression. -/
def hiByte (a : E) : E := .shift 64 .shr a (.imm 8#64)

/-- Replace bits 15:8 of `old` by the low byte of `new`. -/
def setHiByte (old new : E) : E :=
  .alu 64 .or (.alu 64 .and old (.imm (~~~(0xFF00#64)))) (.shl (.zext 8 new) 8)

theorem hiByte_den (env : Env) (a : E) : ((hiByte a).den env).setWidth 8 = ((a.den env) >>> 8).setWidth 8 := by
  simp [hiByte, E.den, ShiftOp.result]

theorem setHiByte_den (env : Env) (old new : E) :
    (setHiByte old new).den env =
      (old.den env &&& ~~~(0xFF00#64)) ||| (((new.den env).setWidth 8).setWidth 64 <<< 8) := by
  simp [setHiByte, E.den, AluOp.resultN]

/-- Update one XMM register of a symbolic state. -/
def xsetS (x : Fin 16 → E × E) (d : Fin 16) (v : E × E) : Fin 16 → E × E :=
  fun i => if i = d then v else x i

/-- The alignment check of an SSE access, if it is an aligned form. -/
def alignChk (al : Bool) (a : E) : List Stmt := if al then [.align a 16] else []

/-- One symbolic step; `none` for instructions the lifter does not handle. -/
def symStep (σ : SState) (i : LInstr) (len : Nat) : Option (List Stmt × SState) :=
  let nx := nxOf σ len
  match i with
  | .ext i =>
    match i with
    | .mov sz dst src => some (sMov σ len sz dst (σ.regs src))
    | .movI sz dst imm => some (sMov σ len sz dst (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .movI16 dst imm => some (sMovN σ len .w dst (.imm (imm.setWidth 64)))
    | .movI32 dst imm => some (sSet σ len dst (.imm (imm.setWidth 64)))
    | .movabs dst imm => some (sSet σ len dst (.imm imm))
    | .load sz dst src => some (sReadSet σ len (.mem src) sz.bytes dst (.zext sz.bits))
    | .store n dst src => some (sMovN σ len n dst (σ.regs src))
    | .movx sx sz n dst src => some (sReadSet σ len src n.bytes dst
        (fun e => if sx then .zext sz.bits (.sext n.bits e) else .zext sz.bits (.zext n.bits e)))
    | .movsxd dst src => some (sReadSet σ len src 4 dst (.sext 32))
    | .lea sz dst m => some (sSet σ len dst (.zext sz.bits (sAddr σ nx m)))
    | .alu sz op dst src => some (sAlu σ len sz op dst (σ.regs src))
    | .aluR sz op dst src =>
      if op = .cmp then some (sReadF σ len src sz.bytes (fun y => .alu sz.bits op (σ.regs dst) y))
      else some (sReadSetF σ len src sz.bytes dst (fun y => .alu sz.bits op (σ.regs dst) y)
        (fun y => .alu sz.bits op (σ.regs dst) y))
    | .aluI sz op dst imm => some (sAlu σ len sz op dst (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .aluI8 sz op dst imm => some (sAlu σ len sz op dst (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .aluA sz op imm => some (sAlu σ len sz op (.reg .rax) (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .test sz dst src => some (sReadF σ len dst sz.bytes (fun x => .test sz.bits x (σ.regs src)))
    | .testA sz imm =>
      some (sFlags σ len (.test sz.bits (σ.regs .rax) (.imm ((imm.signExtend sz.bits).setWidth 64))))
    | .incdec sz dec dst =>
      some (sRMW σ len sz dst (fun x => .alu sz.bits (if dec then .sub else .add) x (.imm 1#64))
        (some fun x => if dec then .dec sz.bits x σ.flags else .inc sz.bits x σ.flags))
    | .bswap sz dst => some (sSet σ len dst (.bswap sz (σ.regs dst)))
    | .unary sz .neg dst => some (sRMW σ len sz dst (.neg sz.bits) (some (.neg sz.bits)))
    | .unary sz .not dst => some (sRMW σ len sz dst (.not sz.bits) none)
    | .imul sz dst src => some (sReadSetF σ len src sz.bytes dst (.mul sz.bits (σ.regs dst))
        (.imul sz.bits (σ.regs dst)))
    | .shift sz op dst count =>
      some (sRMW σ len sz dst (fun x => .shift sz.bits op x (countSym σ count))
        (some fun x => .shift sz.bits op x (countSym σ count) σ.flags))
    | .cxd sz => some (sSet σ len .rdx (.signmask sz.bits (σ.regs .rax)))
    | .cxe .d => some (sSet σ len .rax (.zext 32 (.sext 16 (σ.regs .rax))))
    | .cxe .q => some (sSet σ len .rax (.sext 32 (σ.regs .rax)))
    | .bitcount op sz dst src => some (sReadSetF σ len src sz.bytes dst (.bitcount op sz.bits)
        (.bitcount op sz.bits))
    | .mov8 dst src => some (sReadSet σ len src 1 dst (.merge .b (σ.regs dst)))
    | .movI8 dst imm => some (sMovN σ len .b dst (.imm (imm.setWidth 64)))
    | .nop _ | .endbr64 => some ([], { σ with rip := nx })
    | .ud2 => some ([.trap], σ)
    | .jmp rel => some ([], { σ with rip := addImm nx (rel.signExtend 64) })
    | .jmp8 rel => some ([], { σ with rip := addImm nx (rel.signExtend 64) })
    | .jcc c rel =>
      some ([.cond c σ.flags], { σ.fresh with rip := .sel (.v σ.n) (addImm nx (rel.signExtend 64)) nx })
    | .jcc8 c rel =>
      some ([.cond c σ.flags], { σ.fresh with rip := .sel (.v σ.n) (addImm nx (rel.signExtend 64)) nx })
    | .setcc c dst =>
      let w := sWriteN σ.fresh nx .b dst (.v σ.n)
      some ([.cond c σ.flags] ++ w.1, { w.2 with rip := nx })
    | .call rel => some ([sPushStmt σ nx], { sPushState σ with rip := addImm nx (rel.signExtend 64) })
    | .ret => some ([.pop (σ.regs .rsp)], { sPopState σ with rip := .v σ.n })
    | .push src => some ([sPushStmt σ (σ.regs src)], { sPushState σ with rip := nx })
    | .pushRM src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [sPushStmt rd.2.2 rd.2.1], { sPushState rd.2.2 with rip := nx })
    | .pop dst => some ([.pop (σ.regs .rsp)], { (sPopState σ).setReg dst (.v σ.n) with rip := nx })
    | .leave =>
      let σt := σ.setReg .rsp (σ.regs .rbp)
      some ([.pop (σ.regs .rbp)], { (sPopState σt).setReg .rbp (.v σ.n) with rip := nx })
    | .div .. => none
    -- Byte TEST/CMP, MUL and CMOV joined `Ext.Instr` after this lifter was written; the
    -- proposer still emits gcc's byte and CMOV forms as `XInstr` extension forms.
    | .test8 .. | .testI8 .. | .testA8 .. | .cmpI8 .. | .cmpA8 .. | .mul .. | .cmov .. => none
  | .x i =>
    match i with
    | .alu8 op dst src =>
      let rd := sRead σ nx 1 dst
      let y := src.sym σ
      let fl : F := .alu 8 op rd.2.1 y
      if op = .cmp then some (rd.1 ++ [], { rd.2.2 with flags := fl, rip := nx })
      else
        let w := sWriteN rd.2.2 nx .b dst (.alu 8 op rd.2.1 y)
        some (rd.1 ++ w.1, { w.2 with flags := fl, rip := nx })
    | .test8 dst src => some (sReadF σ len dst 1 (fun x => .test 8 x (src.sym σ)))
    | .cmov sz c dst src =>
      let rd := sRead σ nx sz.bytes src
      some (rd.1 ++ [.cond c σ.flags],
        { rd.2.2.fresh.setReg dst (.sel (.v rd.2.2.n) (.zext sz.bits rd.2.1) (.zext sz.bits (σ.regs dst)))
          with rip := nx })
    | .bt dst src => some (sFlags σ len (.bt (σ.regs dst) (σ.regs src) σ.flags))
    | .jmpInd src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [], { rd.2.2 with rip := rd.2.1 })
    | .callInd src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [sPushStmt rd.2.2 nx], { sPushState rd.2.2 with rip := rd.2.1 })
    | .aluHi op r imm =>
      let x := hiByte (σ.regs r)
      let fl : F := .alu 8 op x (.imm (imm.setWidth 64))
      if op = .cmp then some ([], { σ with flags := fl, rip := nx })
      else some ([], { σ.setReg r (setHiByte (σ.regs r) (.alu 8 op x (.imm (imm.setWidth 64))))
        with flags := fl, rip := nx })
    | .testHi r imm =>
      some ([], { σ with flags := .test 8 (hiByte (σ.regs r)) (.imm (imm.setWidth 64)), rip := nx })
  | .sse i =>
    match i with
    | .load128 al d m =>
      let a := sAddr σ nx m
      some (alignChk al a ++ [.load 8 a, .load 8 (.add a (.imm 8#64))],
        { σ.fresh.fresh with xmm := xsetS σ.xmm d (.v σ.n, .v (σ.n + 1)), rip := nx })
    | .store128 al m src =>
      let a := sAddr σ nx m
      some (alignChk al a ++ [.store 8 a (σ.xmm src).1, .store 8 (.add a (.imm 8#64)) (σ.xmm src).2],
        { σ with rip := nx })
    | .zero d => some ([], { σ with xmm := xsetS σ.xmm d (.imm 0, .imm 0), rip := nx })
    | .mov d src => some ([], { σ with xmm := xsetS σ.xmm d (σ.xmm src), rip := nx })

end Silmaril.X86.Lift.Bir
