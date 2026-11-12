module

public import Silmaril.X86.Str9Fs.Thms

/-!
# ptmalloc x86sim: the stepping kit (any code, any version)

`stepC`: one `Str9Fs` step of any `code` loaded at `A`, from a decode fact and the execution
result; `ex_head`/`ex_fC` chain steps as continuations. The `exec_*`/`fx_*`/`e_*` lemmas give the
result of each instruction form met on the allocator's tcache paths, with loads and stores as
hypotheses (the memory stays abstract). Nothing here names a glibc version: a block proof of a
version supplies its code bytes and decode facts.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.X86
namespace Silmaril.Libc.Ptmalloc.X86sim
variable {A : Word}
theorem exec_base (i : Silmaril.X86.Ext.Instr) (c : State) (mem : Memory) (l : Nat) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base i)))) c mem l = Silmaril.X86.Ext.exec i c mem l := by
  simp [Str9Fs.exec, Silmaril.X86.Str9.exec, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec]

theorem reaches_head {s t u : MState} (h : Str9Fs.step s = some t)
    (h2 : Reaches Str9Fs.step t u) : Reaches Str9Fs.step s u := by
  obtain ⟨n, hn⟩ := h2
  exact ⟨n + 1, by simp [run, h, hn]⟩

theorem ex_head {P : MState → Prop} {s t : MState} (h : Str9Fs.step s = some t)
    (h2 : ∃ u, Reaches Str9Fs.step t u ∧ P u) : ∃ u, Reaches Str9Fs.step s u ∧ P u := by
  obtain ⟨u, hu, hp⟩ := h2
  exact ⟨u, reaches_head h hu, hp⟩


open Silmaril.Machine.LittleEndian (encodeWords)
theorem exec_push {c : State} {mem mem' : Memory} {r : Reg} {l : Nat}
    (h : Silmaril.X86.pushWord c mem (c.read r) = some (c.write .rsp (c.read .rsp - 8#64), mem')) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.push r))))) c mem l =
      .ok { c.write .rsp (c.read .rsp - 8#64) with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, h]

theorem rip_add (A : Word) (a b : Nat) :
    A + BitVec.ofNat 64 a + BitVec.ofNat 64 b = A + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]


theorem exec_endbr {c : State} {mem : Memory} {l : Nat} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base .endbr64)))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]

theorem exec_movrr {c : State} {mem : Memory} {l : Nat} {d s : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.reg d) s))))) c mem l =
      .ok { c.write d (c.read s) with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]

theorem exec_subrsp {c : State} {mem : Memory} {l : Nat} {imm : BitVec 8} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .q .sub (.reg .rsp) imm))))) c mem l =
      .ok { c.write .rsp (c.read .rsp - imm.signExtend 64) with
        rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 64) .sub (c.read .rsp) (imm.signExtend 64), ?_⟩
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.AluOp.resultN,
    Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]
  rfl


section
open Silmaril.X86.Ext (loadN storeN Mem Index RM Sz Narrow Cond subFlagsN logicFlagsN)
/-- The simp set of the semantic unfolding. -/
macro "esimp" : tactic => `(tactic| simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
  Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep,
  Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.writeNarrow,
  Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
  Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.ofRip,
  Silmaril.X86.Ext.Index.value, Silmaril.X86.Ext.Count.raw, Silmaril.X86.Ext.Narrow.bytes,
  Silmaril.X86.Ext.Narrow.bits])

variable {c : State} {mem : Memory} {l : Nat}

theorem exec_jcc {cond : Cond} {rel : BitVec 32} {b : Bool} (h : cond.eval c.flags = some b) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.jcc cond rel))))) c mem l =
      .ok { c with rip := if b then c.rip + BitVec.ofNat 64 l + rel.signExtend 64
        else c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]; cases b <;> simp [Silmaril.X86.Ext.exec, h]

theorem exec_jcc8 {cond : Cond} {rel : BitVec 8} {b : Bool} (h : cond.eval c.flags = some b) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.jcc8 cond rel))))) c mem l =
      .ok { c with rip := if b then c.rip + BitVec.ofNat 64 l + rel.signExtend 64
        else c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]; cases b <;> simp [Silmaril.X86.Ext.exec, h]

/-- `cmpb $imm, mem` -/
theorem exec_cmpI8m {mm : Ext.Mem} {imm : BitVec 8} {v : Word}
    (h : loadN mem (mm.addr c (c.rip + BitVec.ofNat 64 l)) 1 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.cmpI8 (.mem mm) imm))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := subFlagsN (v.setWidth 8) imm } mem := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.readNarrow,
    Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits, h]

/-- `test r, r` (64-bit). -/
theorem exec_testrr {r : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.test .q (.reg r) r))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := logicFlagsN (c.read r &&& c.read r) } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.retire, Option.map_some]
  rfl

/-- `lea d, [r + disp]` (64-bit). -/
theorem exec_lea {d r : Reg} {disp : BitVec 32} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.lea .q d (Ext.Mem.ofReg r none disp)))))) c mem l =
      .ok { c.write d (c.read r + disp.signExtend 64) with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]; esimp

/-- `xor r32, r32`. -/
theorem xor32_self (c : State) (r : Reg) :
    Sz.d.write c r (Silmaril.X86.Ext.AluOp.resultN .xor (Sz.d.read c r) (Sz.d.read c r)) =
      c.write r 0 := by
  unfold Sz.write
  congr 1
  show (BitVec.setWidth 32 (c.read r) ^^^ BitVec.setWidth 32 (c.read r)).setWidth 64 = 0
  rw [BitVec.xor_self]; rfl

theorem exec_xor32 {r : Reg} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .d .xor (.reg r) r))))) c mem l =
      .ok { c.write r 0 with rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 32) .xor ((c.read r).setWidth 32) ((c.read r).setWidth 32), ?_⟩
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, Option.map_some]
  simp only [reduceCtorEq, ite_false, Option.map_some, xor32_self]
  rfl

/-- `cmp $imm8, r` (64-bit). -/
theorem exec_cmpI8r {r : Reg} {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .q .cmp (.reg r) imm))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := subFlagsN (c.read r) (imm.signExtend 64) } mem := by
  rw [exec_base]; esimp; rfl

/-- `op $imm8, r` (64-bit, not `cmp`). -/
theorem exec_aluI8r {op : Silmaril.X86.AluOp} {r : Reg} {imm : BitVec 8} (hop : op ≠ .cmp) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .q op (.reg r) imm))))) c mem l =
      .ok { c.write r (Silmaril.X86.Ext.AluOp.resultN op (c.read r) (imm.signExtend 64)) with
        rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 64) op (c.read r) (imm.signExtend 64), ?_⟩
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, hop,
    Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]

/-- `op $imm8, r32` (not `cmp`). -/
theorem exec_aluI8r32 {op : Silmaril.X86.AluOp} {r : Reg} {imm : BitVec 8} (hop : op ≠ .cmp) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .d op (.reg r) imm))))) c mem l =
      .ok { c.write r ((Silmaril.X86.Ext.AluOp.resultN op ((c.read r).setWidth 32)
          (imm.signExtend 32)).setWidth 64) with
        rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 32) op ((c.read r).setWidth 32) (imm.signExtend 32), ?_⟩
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, hop,
    Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]

/-- `shr $imm, r` (64-bit). -/
theorem exec_shr {r : Reg} {imm : BitVec 8} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.shift .q .shr (.reg r) (.imm imm)))))) c mem l =
      .ok { c.write r (c.read r >>> (imm.toNat % 64)) with
        rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]; esimp; simp [Silmaril.X86.Ext.ShiftOp.result]

/-- `mov r, [rip + disp]` (64-bit load). -/
theorem exec_loadrip {d : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.rip + BitVec.ofNat 64 l + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofRip disp)))))) c mem l =
      .ok { c.write d v with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]; esimp; rw [show Sz.q.bytes = 8 from rfl, h]; rfl

/-- `cmp r, [rip + disp]` (64-bit). -/
theorem exec_cmprip {r : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.rip + BitVec.ofNat 64 l + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluR .q .cmp r (.mem (Ext.Mem.ofRip disp))))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := subFlagsN (c.read r) v } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp only [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip,
    Silmaril.X86.Ext.Base.value_rip, Option.map_none, Option.getD_none, BitVec.add_zero, h,
    Option.map_some, ite_true, Silmaril.X86.Ext.retire]
  rfl


/-- `mov %fs:0(b), d` (64-bit). -/
theorem exec_fsload {d b : Reg} {v : Word} (h : loadN mem (c.fsBase + c.read b) 8 = some v) :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.load .q d (Mem.fsAt 0#32)))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok { c.write d v with rip := c.rip + BitVec.ofNat 64 l } mem := by
  simp only [Str9Fs.exec, Str9Fs.execNew, Str9Fs.execFs, Silmaril.X86.Ext9.exec,
    Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.fsAt,
    Silmaril.X86.Ext.Mem.ofFs, h, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]
  rfl

/-- `movzwl (b, i, 2), d`. -/
theorem exec_movzw {d b i : Reg} {hi : i ≠ .rsp} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 1)) 2 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.movx false .d .w d
      (.mem (Ext.Mem.ofReg b (some ⟨i, 1#2, hi⟩) 0#32))))))) c mem l =
      .ok { c.write d (((v.setWidth 16).setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readNarrow]
  rw [show Narrow.w.bytes = 2 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]
  rfl


/-- `test cx, cx` (16-bit). -/
theorem exec_test16 {r : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.new (.test16 (.reg r) r)))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := logicFlagsN ((c.read r).setWidth 16 &&& (c.read r).setWidth 16) } mem := by
  simp only [Str9Fs.exec, Silmaril.X86.Str9.exec, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew,
    Silmaril.X86.Ext9.test16, Silmaril.X86.Ext.readNarrow]
  rfl

/-- `test $imm8, %al`. -/
theorem exec_testA8 {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.testA8 imm))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := logicFlagsN ((c.read .rax).setWidth 8 &&& imm) } mem := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]

/-- `mov (b, i, 8), d` (64-bit load). -/
theorem exec_loadidx8 {d b i : Reg} {hi : i ≠ .rsp} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 3)) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) 0#32)))))) c mem l =
      .ok { c.write d v with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]

/-- `xor (b), d` (64-bit). -/
theorem exec_xorm {d b : Reg} {v : Word} (h : loadN mem (c.read b) 8 = some v) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluR .q .xor d (.mem (Ext.Mem.ofReg b none 0#32))))))) c mem l =
      .ok { c.write d (c.read d ^^^ v) with rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 64) .xor (c.read d) v, ?_⟩
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
    Silmaril.X86.Ext.AluOp.resultN]
  rfl

/-- `mov s, (b, i, 8)` (64-bit store). -/
theorem exec_storeidx8 {s b i : Reg} {hi : i ≠ .rsp} {mem' : Memory}
    (h : storeN mem (c.read b + (c.read i <<< 3)) 8 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.mem (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) 0#32)) s))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.read]

/-- `mov %s16, (b, i, 2)`. -/
theorem exec_storew {s b i : Reg} {hi : i ≠ .rsp} {mem' : Memory}
    (h : storeN mem (c.read b + (c.read i <<< 1)) 2 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.store .w (.mem (Ext.Mem.ofReg b (some ⟨i, 1#2, hi⟩) 0#32)) s))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeNarrow]
  rw [Silmaril.X86.Ext.storeN_setWidth]
  rw [show Narrow.w.bytes = 2 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value,
    Silmaril.X86.Ext.retire, h]

/-- `movq $0, 8(b)`. -/
theorem exec_movI0 {b : Reg} {mem' : Memory}
    (h : storeN mem (c.read b + 8#64) 8 0#64 = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.movI .q (.mem (Ext.Mem.ofReg b none 8#32)) 0#32))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.retire, h]

/-- `pop r`. -/
theorem exec_pop {r : Reg} {v : Word}
    (h : mem.readBytes (c.read .rsp).toNat 8 = some (encodeWords [v])) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.pop r))))) c mem l =
      .ok { (c.write .rsp (c.read .rsp + 8#64)).write r v with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.popWord_of_readBytes h]

/-- `ret`. -/
theorem exec_ret {v : Word}
    (h : mem.readBytes (c.read .rsp).toNat 8 = some (encodeWords [v])) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base .ret)))) c mem l =
      .ok { c.write .rsp (c.read .rsp + 8#64) with rip := v } mem := by
  rw [exec_base]
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.popWord_of_readBytes h]

end

/-- The span `[p, p + k)` misses `[lo, hi)`. -/
def Apart (p k lo hi : Nat) : Prop := ∀ i < k, ¬ (lo ≤ p + i ∧ p + i < hi)

open Silmaril.X86.Ext (Loaded loadN storeN Mem Index RM Sz Narrow Cond subFlagsN logicFlagsN)
theorem stepC {code : List Byte} {N : Nat} (hN : code.length = N) {A : Word} {m : MState} {o l : Nat}
    {i : Str9Fs.Instr} {c : State} {mem : Memory}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o)
    (hfit : o + l ≤ N) (hdec : Str9Fs.decode ((code.drop o).take l) = some (i, l))
    (hx : Str9Fs.exec i m.core m.memory l = .ok c mem) :
    Str9Fs.step m = some ⟨c, mem⟩ :=
  Str9Fs.isa.step_of (s := m) trivial hl hrip (by rw [hN]; exact hfit) hdec hx trivial

/-- A step whose flags are abstract. -/
theorem ex_fC {code : List Byte} {N : Nat} (hN : code.length = N) {A : Word} {P : MState → Prop}
    {m : MState} {o l : Nat} {i : Str9Fs.Instr} {F : Silmaril.X86.Flags → State} {mem' : Memory}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o)
    (hfit : o + l ≤ N) (hdec : Str9Fs.decode ((code.drop o).take l) = some (i, l))
    (hx : ∃ f, Str9Fs.exec i m.core m.memory l = .ok (F f) mem')
    (cont : ∀ f, ∃ u, Reaches Str9Fs.step ⟨F f, mem'⟩ u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  obtain ⟨f, hf⟩ := hx
  exact ex_head (stepC hN hl hrip hfit hdec hf) (cont f)

/-- A write outside the code keeps it loaded. -/
theorem loadedC_ww {code : List Byte} {N : Nat} (hN : code.length = N) {A : Word}
    {mem mem' : Memory} {fp : Nat → Prop} (hl : Loaded mem A code)
    (hw : mem.WritesWithin mem' fp) (hout : ∀ i < N, ¬ fp (A.toNat + i)) :
    Loaded mem' A code := by
  unfold Loaded at hl ⊢
  rw [hN] at hl ⊢
  rw [hw.fetchBytes hout]; exact hl

/-- A store apart from the code keeps it loaded. -/
theorem loadedC_store {code : List Byte} {N : Nat} (hN : code.length = N) {A : Word}
    {m m' : Memory} {a : Word} {k : Nat} {w : Word} (hl : Loaded m A code)
    (hs : storeN m a k w = some m') (hap : Apart a.toNat k A.toNat (A.toNat + N)) :
    Loaded m' A code := by
  have wo := Silmaril.X86.Ext.storeN_writesOnly hs
  rw [Memory.writesOnly_iff_writesWithin] at wo
  refine loadedC_ww hN hl wo (fun i hi ⟨h1, h2⟩ => ?_)
  obtain ⟨j, hj, hj'⟩ : ∃ j < k, a.toNat + j = A.toNat + i := ⟨A.toNat + i - a.toNat, by omega, by omega⟩
  exact hap j hj ⟨by omega, by omega⟩

/-! ## Compact successor states

`{ s with rip := x }` elaborates to a structure instance that mentions `s` once per field, so a
chain of steps duplicates the earlier states and `simp` on the result can blow up. `nx`/`nxf`
name the update instead; the `e_*` lemmas restate the instruction forms with them. -/

/-- `s` with `rip := x`. -/
def nx (s : State) (x : Word) : State := { s with rip := x }
/-- `s` with `rip := x` and `flags := f`. -/
def nxf (s : State) (x : Word) (f : Silmaril.X86.Flags) : State := { s with rip := x, flags := f }

@[simp] theorem nx_read (s : State) (x : Word) (r : Reg) : (nx s x).read r = s.read r := rfl
@[simp] theorem nx_rip (s : State) (x : Word) : (nx s x).rip = x := rfl
@[simp] theorem nx_flags (s : State) (x : Word) : (nx s x).flags = s.flags := rfl
@[simp] theorem nx_fsBase (s : State) (x : Word) : (nx s x).fsBase = s.fsBase := rfl
@[simp] theorem nxf_read (s : State) (x : Word) (f : Silmaril.X86.Flags) (r : Reg) :
    (nxf s x f).read r = s.read r := rfl
@[simp] theorem nxf_rip (s : State) (x : Word) (f : Silmaril.X86.Flags) : (nxf s x f).rip = x := rfl
@[simp] theorem nxf_flags (s : State) (x : Word) (f : Silmaril.X86.Flags) : (nxf s x f).flags = f := rfl
@[simp] theorem nxf_fsBase (s : State) (x : Word) (f : Silmaril.X86.Flags) :
    (nxf s x f).fsBase = s.fsBase := rfl

/-! ## More instruction forms -/

section
variable {c : State} {mem : Memory} {l : Nat}

/-- `mov disp(b), d` (64-bit load). -/
theorem fx_loadd {d b : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofReg b none disp)))))) c mem l =
      .ok { c.write d v with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]

/-- `mov disp(b, i, 8), d` (64-bit load). -/
theorem fx_loadidx8d {d b i : Reg} {hi : i ≠ .rsp} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 3) + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) disp)))))) c mem l =
      .ok { c.write d v with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]

/-- `mov %fs:0(b), d32`. -/
theorem fx_fsload32 {d b : Reg} {v : Word} (h : loadN mem (c.fsBase + c.read b) 4 = some v) :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.load .d d (Mem.fsAt 0#32)))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok { c.write d ((v.setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } mem := by
  simp only [Str9Fs.exec, Str9Fs.execNew, Str9Fs.execFs, Silmaril.X86.Ext9.exec,
    Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM]
  rw [show Sz.d.bytes = 4 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.fsAt,
    Silmaril.X86.Ext.Mem.ofFs, h, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]
  rfl

/-- `cmpq $0, %fs:0(b)`. -/
theorem fx_fscmp0 {b : Reg} {v : Word} (h : loadN mem (c.fsBase + c.read b) 8 = some v) :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.aluI8 .q .cmp (.mem (Mem.fsAt 0#32)) 0#8))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := subFlagsN v 0#64 } mem := by
  simp only [Str9Fs.exec, Str9Fs.execNew, Str9Fs.execFs, Silmaril.X86.Ext9.exec,
    Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.fsAt,
    Silmaril.X86.Ext.Mem.ofFs, h, Silmaril.X86.Ext.retire]
  rfl

/-- `mov s32, %fs:0(b)`. -/
theorem fx_fsstore32 {s b : Reg} {mem' : Memory}
    (h : storeN mem (c.fsBase + c.read b) 4 (((c.read s).setWidth 32).setWidth 64) = some mem') :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.mov .d (.mem (Mem.fsAt 0#32)) s))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  simp only [Str9Fs.exec, Str9Fs.execNew, Str9Fs.execFs, Silmaril.X86.Ext9.exec,
    Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM]
  rw [show Sz.d.bytes = 4 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.fsAt,
    Silmaril.X86.Ext.Mem.ofFs, Silmaril.X86.Ext.Sz.read, h, Silmaril.X86.Ext.retire]

/-- `lea disp(%rip), d`. -/
theorem fx_learip {d : Reg} {disp : BitVec 32} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.lea .q d (Ext.Mem.ofRip disp)))))) c mem l =
      .ok { c.write d (c.rip + BitVec.ofNat 64 l + disp.signExtend 64) with
        rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]; esimp

/-- `call rel32`. -/
theorem fx_call {rel : BitVec 32} {mem' : Memory}
    (h : Silmaril.X86.pushWord c mem (c.rip + BitVec.ofNat 64 l) =
      some (c.write .rsp (c.read .rsp - 8#64), mem')) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.call rel))))) c mem l =
      .ok { c.write .rsp (c.read .rsp - 8#64) with
        rip := c.rip + BitVec.ofNat 64 l + rel.signExtend 64 } mem' := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, h]

/-- `jmp rel32`. -/
theorem fx_jmp {rel : BitVec 32} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.jmp rel))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l + rel.signExtend 64 } mem := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec]

/-- `mov s32, d32` (register to register; zero-extends). -/
theorem fx_mov32 {d s : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .d (.reg d) s))))) c mem l =
      .ok { c.write d (((c.read s).setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } mem := by
  rw [exec_base]
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]

/-- `neg r` (64-bit). -/
theorem fx_neg {r : Reg} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.unary .q .neg (.reg r)))))) c mem l =
      .ok { c.write r (-c.read r) with rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.negFlagsN (c.read r), ?_⟩
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]
  rfl

/-- `cmp s, d` (64-bit, register operands): the flags of `d - s`. -/
theorem fx_cmprr {d s : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .q .cmp (.reg d) s))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := subFlagsN (c.read d) (c.read s) } mem := by
  rw [exec_base]; esimp; rfl

/-- `cmp s, disp(b)` (64-bit): the flags of `[b + disp] - s`. -/
theorem fx_cmpmr {b s : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .q .cmp (.mem (Ext.Mem.ofReg b none disp)) s))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := subFlagsN v (c.read s) } mem := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, h, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.Sz.read]
  rfl

/-- `test $imm8, r8` (a byte register). -/
theorem fx_testI8r {r : Reg} {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.testI8 (.reg r) imm))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l, flags := logicFlagsN ((c.read r).setWidth 8 &&& imm) } mem := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.readNarrow,
    Silmaril.X86.Ext.Narrow.bits]

/-- `mov s, disp(b)` (64-bit store). -/
theorem fx_storeqd {s b : Reg} {disp : BitVec 32} {mem' : Memory}
    (h : storeN mem (c.read b + disp.signExtend 64) 8 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.mem (Ext.Mem.ofReg b none disp)) s))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.Sz.read, h]

/-- `mov s, disp(b, i, 8)` (64-bit store). -/
theorem fx_storeidx8d {s b i : Reg} {hi : i ≠ .rsp} {disp : BitVec 32} {mem' : Memory}
    (h : storeN mem (c.read b + (c.read i <<< 3) + disp.signExtend 64) 8 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.mem (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) disp)) s))))) c mem l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.read]

/-- `xor disp(b, i, 8), d` (64-bit). -/
theorem fx_xoridx8d {d b i : Reg} {hi : i ≠ .rsp} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 3) + disp.signExtend 64) 8 = some v) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluR .q .xor d (.mem (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) disp))))))) c mem l =
      .ok { c.write d (c.read d ^^^ v) with rip := c.rip + BitVec.ofNat 64 l, flags := f } mem := by
  rw [exec_base]
  refine ⟨Silmaril.X86.Ext.AluOp.flagsN (n := 64) .xor (c.read d) v, ?_⟩
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM]
  rw [show Sz.q.bytes = 8 from rfl]
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value, h,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
    Silmaril.X86.Ext.AluOp.resultN]
  rfl

end

/-! ### The forms with compact successor states -/

section
variable {c : State} {mem : Memory} {l : Nat}
open Silmaril.X86.Ext (Mem)

theorem e_endbr : Str9Fs.exec (.str9 (.ext9 (.ext8 (.base .endbr64)))) c mem l =
    .ok (nx c (c.rip + BitVec.ofNat 64 l)) mem := exec_endbr
theorem e_testrr {r : Reg} : Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.test .q (.reg r) r))))) c mem l =
    .ok (nxf c (c.rip + BitVec.ofNat 64 l) (logicFlagsN (c.read r &&& c.read r))) mem := exec_testrr
theorem e_jcc {cond : Cond} {rel : BitVec 32} {b : Bool} (h : cond.eval c.flags = some b) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.jcc cond rel))))) c mem l =
      .ok (nx c (if b then c.rip + BitVec.ofNat 64 l + rel.signExtend 64
        else c.rip + BitVec.ofNat 64 l)) mem := exec_jcc h
theorem e_jcc8 {cond : Cond} {rel : BitVec 8} {b : Bool} (h : cond.eval c.flags = some b) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.jcc8 cond rel))))) c mem l =
      .ok (nx c (if b then c.rip + BitVec.ofNat 64 l + rel.signExtend 64
        else c.rip + BitVec.ofNat 64 l)) mem := exec_jcc8 h
theorem e_movrr {d s : Reg} : Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.reg d) s))))) c mem l =
    .ok (nx (c.write d (c.read s)) (c.rip + BitVec.ofNat 64 l)) mem := exec_movrr
theorem e_lea {d r : Reg} {disp : BitVec 32} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.lea .q d (Ext.Mem.ofReg r none disp)))))) c mem l =
      .ok (nx (c.write d (c.read r + disp.signExtend 64)) (c.rip + BitVec.ofNat 64 l)) mem := exec_lea
theorem e_subrsp {imm : BitVec 8} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .q .sub (.reg .rsp) imm))))) c mem l =
      .ok (nxf (c.write .rsp (c.read .rsp - imm.signExtend 64)) (c.rip + BitVec.ofNat 64 l) f) mem :=
  exec_subrsp
theorem e_loadrip {d : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.rip + BitVec.ofNat 64 l + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofRip disp)))))) c mem l =
      .ok (nx (c.write d v) (c.rip + BitVec.ofNat 64 l)) mem := exec_loadrip h
theorem e_xor32 {r : Reg} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .d .xor (.reg r) r))))) c mem l =
      .ok (nxf (c.write r 0) (c.rip + BitVec.ofNat 64 l) f) mem := exec_xor32
theorem e_cmpI8r {r : Reg} {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .q .cmp (.reg r) imm))))) c mem l =
      .ok (nxf c (c.rip + BitVec.ofNat 64 l) (subFlagsN (c.read r) (imm.signExtend 64))) mem := exec_cmpI8r
theorem e_aluI8r {op : Silmaril.X86.AluOp} {r : Reg} {imm : BitVec 8} (hop : op ≠ .cmp) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .q op (.reg r) imm))))) c mem l =
      .ok (nxf (c.write r (Silmaril.X86.Ext.AluOp.resultN op (c.read r) (imm.signExtend 64)))
        (c.rip + BitVec.ofNat 64 l) f) mem := exec_aluI8r hop
theorem e_aluI8r32 {op : Silmaril.X86.AluOp} {r : Reg} {imm : BitVec 8} (hop : op ≠ .cmp) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .d op (.reg r) imm))))) c mem l =
      .ok (nxf (c.write r ((Silmaril.X86.Ext.AluOp.resultN op ((c.read r).setWidth 32)
          (imm.signExtend 32)).setWidth 64)) (c.rip + BitVec.ofNat 64 l) f) mem := exec_aluI8r32 hop
theorem e_shr {r : Reg} {imm : BitVec 8} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.shift .q .shr (.reg r) (.imm imm)))))) c mem l =
      .ok (nxf (c.write r (c.read r >>> (imm.toNat % 64))) (c.rip + BitVec.ofNat 64 l) f) mem := exec_shr
theorem e_cmprip {r : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.rip + BitVec.ofNat 64 l + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluR .q .cmp r (.mem (Ext.Mem.ofRip disp))))))) c mem l =
      .ok (nxf c (c.rip + BitVec.ofNat 64 l) (subFlagsN (c.read r) v)) mem := exec_cmprip h
theorem e_fsload {d b : Reg} {v : Word} (h : loadN mem (c.fsBase + c.read b) 8 = some v) :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.load .q d (Mem.fsAt 0#32)))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok (nx (c.write d v) (c.rip + BitVec.ofNat 64 l)) mem := exec_fsload h
theorem e_movzw {d b i : Reg} {hi : i ≠ .rsp} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 1)) 2 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.movx false .d .w d
      (.mem (Ext.Mem.ofReg b (some ⟨i, 1#2, hi⟩) 0#32))))))) c mem l =
      .ok (nx (c.write d (((v.setWidth 16).setWidth 32).setWidth 64)) (c.rip + BitVec.ofNat 64 l)) mem :=
  exec_movzw h
theorem e_testA8 {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.testA8 imm))))) c mem l =
      .ok (nxf c (c.rip + BitVec.ofNat 64 l) (logicFlagsN ((c.read .rax).setWidth 8 &&& imm))) mem := exec_testA8
theorem e_storew {s b i : Reg} {hi : i ≠ .rsp} {mem' : Memory}
    (h : storeN mem (c.read b + (c.read i <<< 1)) 2 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.store .w (.mem (Ext.Mem.ofReg b (some ⟨i, 1#2, hi⟩) 0#32)) s))))) c mem l =
      .ok (nx c (c.rip + BitVec.ofNat 64 l)) mem' := exec_storew h
theorem e_pop {r : Reg} {v : Word}
    (h : mem.readBytes (c.read .rsp).toNat 8 = some (encodeWords [v])) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.pop r))))) c mem l =
      .ok (nx ((c.write .rsp (c.read .rsp + 8#64)).write r v) (c.rip + BitVec.ofNat 64 l)) mem := exec_pop h
theorem e_ret {v : Word}
    (h : mem.readBytes (c.read .rsp).toNat 8 = some (encodeWords [v])) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base .ret)))) c mem l =
      .ok (nx (c.write .rsp (c.read .rsp + 8#64)) v) mem := exec_ret h
theorem e_loadd {d b : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofReg b none disp)))))) c mem l =
      .ok (nx (c.write d v) (c.rip + BitVec.ofNat 64 l)) mem := fx_loadd h
theorem e_loadidx8d {d b i : Reg} {hi : i ≠ .rsp} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 3) + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.load .q d (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) disp)))))) c mem l =
      .ok (nx (c.write d v) (c.rip + BitVec.ofNat 64 l)) mem := fx_loadidx8d h
theorem e_fsload32 {d b : Reg} {v : Word} (h : loadN mem (c.fsBase + c.read b) 4 = some v) :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.load .d d (Mem.fsAt 0#32)))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok (nx (c.write d ((v.setWidth 32).setWidth 64)) (c.rip + BitVec.ofNat 64 l)) mem :=
  fx_fsload32 h
theorem e_fscmp0 {b : Reg} {v : Word} (h : loadN mem (c.fsBase + c.read b) 8 = some v) :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.aluI8 .q .cmp (.mem (Mem.fsAt 0#32)) 0#8))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok (nxf c (c.rip + BitVec.ofNat 64 l) (subFlagsN v 0#64)) mem := fx_fscmp0 h
theorem e_fsstore32 {s b : Reg} {mem' : Memory}
    (h : storeN mem (c.fsBase + c.read b) 4 (((c.read s).setWidth 32).setWidth 64) = some mem') :
    Str9Fs.exec (.new (.fs (.ext8 (.base (.mov .d (.mem (Mem.fsAt 0#32)) s))) (Ext.Mem.ofReg b none 0#32)))
      c mem l = .ok (nx c (c.rip + BitVec.ofNat 64 l)) mem' := fx_fsstore32 h
theorem e_learip {d : Reg} {disp : BitVec 32} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.lea .q d (Ext.Mem.ofRip disp)))))) c mem l =
      .ok (nx (c.write d (c.rip + BitVec.ofNat 64 l + disp.signExtend 64))
        (c.rip + BitVec.ofNat 64 l)) mem := fx_learip
theorem e_jmp {rel : BitVec 32} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.jmp rel))))) c mem l =
      .ok (nx c (c.rip + BitVec.ofNat 64 l + rel.signExtend 64)) mem := fx_jmp
theorem e_mov32 {d s : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .d (.reg d) s))))) c mem l =
      .ok (nx (c.write d (((c.read s).setWidth 32).setWidth 64)) (c.rip + BitVec.ofNat 64 l)) mem := fx_mov32
theorem e_neg {r : Reg} : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.unary .q .neg (.reg r)))))) c mem l =
      .ok (nxf (c.write r (-c.read r)) (c.rip + BitVec.ofNat 64 l) f) mem := fx_neg
theorem e_cmprr {d s : Reg} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .q .cmp (.reg d) s))))) c mem l =
      .ok (nxf c (c.rip + BitVec.ofNat 64 l) (subFlagsN (c.read d) (c.read s))) mem := fx_cmprr
theorem e_cmpmr {b s : Reg} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + disp.signExtend 64) 8 = some v) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.alu .q .cmp (.mem (Ext.Mem.ofReg b none disp)) s))))) c mem l =
      .ok (nxf c (c.rip + BitVec.ofNat 64 l) (subFlagsN v (c.read s))) mem := fx_cmpmr h
theorem e_testI8r {r : Reg} {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.testI8 (.reg r) imm))))) c mem l =
      .ok (nxf c (c.rip + BitVec.ofNat 64 l) (logicFlagsN ((c.read r).setWidth 8 &&& imm))) mem := fx_testI8r
theorem e_storeqd {s b : Reg} {disp : BitVec 32} {mem' : Memory}
    (h : storeN mem (c.read b + disp.signExtend 64) 8 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.mem (Ext.Mem.ofReg b none disp)) s))))) c mem l =
      .ok (nx c (c.rip + BitVec.ofNat 64 l)) mem' := fx_storeqd h
theorem e_storeidx8d {s b i : Reg} {hi : i ≠ .rsp} {disp : BitVec 32} {mem' : Memory}
    (h : storeN mem (c.read b + (c.read i <<< 3) + disp.signExtend 64) 8 (c.read s) = some mem') :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.mov .q (.mem (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) disp)) s))))) c mem l =
      .ok (nx c (c.rip + BitVec.ofNat 64 l)) mem' := fx_storeidx8d h
theorem e_xoridx8d {d b i : Reg} {hi : i ≠ .rsp} {disp : BitVec 32} {v : Word}
    (h : loadN mem (c.read b + (c.read i <<< 3) + disp.signExtend 64) 8 = some v) : ∃ f : Silmaril.X86.Flags,
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluR .q .xor d (.mem (Ext.Mem.ofReg b (some ⟨i, 3#2, hi⟩) disp))))))) c mem l =
      .ok (nxf (c.write d (c.read d ^^^ v)) (c.rip + BitVec.ofNat 64 l) f) mem := fx_xoridx8d h

/-- `and $imm8, r32` with its flags. -/
theorem e_andI8r32 {r : Reg} {imm : BitVec 8} :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.aluI8 .d .and (.reg r) imm))))) c mem l =
      .ok (nxf (c.write r (((c.read r).setWidth 32).setWidth 64 &&& (imm.signExtend 32).setWidth 64))
        (c.rip + BitVec.ofNat 64 l) (logicFlagsN ((c.read r).setWidth 32 &&& imm.signExtend 32))) mem := by
  rw [exec_base]
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.Sz.write,
    Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, nxf]
  exact ⟨congrArg (fun v => (Silmaril.X86.State.write c r v).regs) BitVec.setWidth_and, rfl⟩

end

/-- A load apart from the written bytes is unchanged. -/
theorem ld_ww {mem mem' : Memory} {fp : Nat → Prop} (hw : mem.WritesWithin mem' fp) {a : Word} {k : Nat}
    {v : Word} (hout : ∀ i < k, ¬ fp (a.toNat + i)) (h : loadN mem a k = some v) :
    loadN mem' a k = some v := by
  unfold loadN at h ⊢; rw [hw.readBytes hout]; exact h

theorem rd_ww {mem mem' : Memory} {fp : Nat → Prop} (hw : mem.WritesWithin mem' fp) {a k : Nat}
    {bs : List Byte} (hout : ∀ i < k, ¬ fp (a + i)) (h : mem.readBytes a k = some bs) :
    mem'.readBytes a k = some bs := by rw [hw.readBytes hout]; exact h

end Silmaril.Libc.Ptmalloc.X86sim
