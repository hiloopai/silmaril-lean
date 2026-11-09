module

public import Silmaril.X86.BlockCert.Ext8.Defs
public import Silmaril.X86.BlockCert.Thms
public import Silmaril.X86.Stencils.ByteLoop.Thms
import Silmaril.Proofs.X86.BlockCert.Ext8.Bridge

/-!
# `Ext8` block certificates: theorems

* `run8_open`: a checked `Ext8` listing whose run succeeds is a run of the open machine, with
  the memory unchanged;
* `Cert.from_block`, `Cert.total`, `Cert.contract`: the VCs of a certificate give a total
  System V `FnContract` on `Open.isa`;
* `Cert.next_of`, `Cert.vc_of_blocks`: assembling the VC.

The leaf-frame lemmas (`BlockCert.Frame.*`) are re-exported through `BlockCert.Thms`.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert8

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded Mem loadN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

/-- **The bridge.** -/
theorem run8_open {code : List Byte} {base : Word} {L : List LI} {o : Nat} {m m' : MState}
    (hok : listing8 code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : run8 L m = some m') :
    Reaches Open.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.X86.BlockCert8.run8_open L o m m' hok hl hrip h


/-! ## Single instructions

Each lemma runs one `Ext8` instruction symbolically: it retires at the next instruction, keeps
the memory, and the registers change as stated (`Eff`). Flags are left unspecified except where
a branch reads them (`cmp_jcc_end`). -/


/-- What a retired instruction did to the registers. -/
def Eff (s c : State) (l : Nat) (f : Reg → Word) : Prop :=
  c.rip = s.rip + BitVec.ofNat 64 l ∧ ∀ r, c.read r = f r

theorem mov_q (s : State) (mem : Memory) (l : Nat) (d a : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.mov .q (.reg d) a)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then s.read a else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d <;> simp [h, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]

theorem xor8_mem (s : State) (mem : Memory) (l : Nat) (a p : Reg) (k : BitVec 32) (v : Word)
    (hv : loadN mem (s.read p + k.signExtend 64) 1 = some v) :
    ∃ c, Silmaril.X86.Ext8.exec (.new (.aluR .xor (.low a) (.mem (Mem.ofReg p none k))))
        s mem l = .ok c mem ∧ c.rip = s.rip + BitVec.ofNat 64 l ∧
      (c.read a).setWidth 8 = (s.read a).setWidth 8 ^^^ v.setWidth 8 ∧
      ∀ r, r ≠ a → c.read r = s.read r := by
  simp [Silmaril.X86.Ext8.exec, Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.RM8.read, Mem.addr, Mem.ofReg, hv,
    Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.BReg.write,
    Silmaril.X86.Ext8.BReg.read, Silmaril.X86.Ext.retire]
  exact ⟨by rw [Silmaril.X86.Ext.writeByte_read_low]; rfl,
    fun r hr => by simp [Silmaril.X86.Ext.writeByte, hr]⟩

theorem movzb (s : State) (mem : Memory) (l : Nat) (a : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.movx false .d .b a (.reg a))) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = a then ((s.read a).setWidth 8).setWidth 64 else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = a
  · subst h
    simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Narrow.bits]
  · simp [h, Silmaril.X86.Ext.Sz.write]

theorem shr_q (s : State) (mem : Memory) (l : Nat) (d : Reg) (n : BitVec 8) (hn : n.toNat < 64) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.shift .q .shr (.reg d) (.imm n))) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then s.read d >>> n.toNat else s.read r) := by
  simp [Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Count.raw, Eff]
  intro r; by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.ShiftOp.result, Nat.mod_eq_of_lt hn]
  · simp [h]

theorem xor_q_mem (s : State) (mem : Memory) (l : Nat) (d : Reg) (M : Mem) (w : Word)
    (hM : M.base = .none) (hw : loadN mem (M.addr s 0#64) 8 = some w) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.aluR .q .xor d (.mem M))) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then s.read d ^^^ w else s.read r) := by
  have : M.addr s (s.rip + BitVec.ofNat 64 l) = M.addr s 0#64 :=
    Mem.addr_congr_of_ne_rip (by rw [hM]; decide) _ _ _
  simp [Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.retire, Eff, this, hw,
    Silmaril.X86.Ext.Sz.bytes]
  intro r; by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.AluOp.resultN]
  · simp [h]

theorem add_q_i8 (s : State) (mem : Memory) (l : Nat) (d : Reg) (k : BitVec 8) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.aluI8 .q .add (.reg d) k)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then s.read d + k.signExtend 64 else s.read r) := by
  simp [Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, Eff]
  intro r; by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.AluOp.resultN]
  · simp [h]


/-- One checked step of a listing that falls through. -/
theorem run8_cons_of {i : Silmaril.X86.Ext8.Instr} {l : Nat} {rest : List LI} {m : MState}
    {c : State} (h : Silmaril.X86.Ext8.exec i m.core m.memory l = .ok c m.memory)
    (hr : c.rip = m.core.rip + BitVec.ofNat 64 l) :
    run8 ((i, l) :: rest) m = run8 rest ⟨c, m.memory⟩ := by
  simp [run8, h, hr]

/-- `cmp` sets the zero flag iff its operands are equal. -/
theorem cmp_zero {n : Nat} (x y : BitVec n) :
    (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp x y).zero = some (decide (x = y)) := by
  simp only [Silmaril.X86.Ext.AluOp.flagsN]
  exact Silmaril.X86.Stencils.ByteLoop.subFlagsN_zero x y

/-- **A block end `cmp x, y; jne rel32`**: the registers and memory are kept, and control goes
to the fall-through if `x = y`, else to the branch target. -/
theorem cmp_jne_end (m : MState) (x y : Reg) (rel : BitVec 32) :
    ∃ c, run8 [(.base (.alu .q .cmp (.reg x) y), 3), (.base (.jcc .ne rel), 6)] m =
        some ⟨c, m.memory⟩ ∧ (∀ r, c.read r = m.core.read r) ∧
      c.rip = if m.core.read x = m.core.read y then m.core.rip + 9#64
        else m.core.rip + 9#64 + rel.signExtend 64 := by
  by_cases h : m.core.read x = m.core.read y <;>
  simp [run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Cond.eval, cmp_zero, h,
    Silmaril.X86.Ext.kNot, BitVec.add_assoc]

/-- **A block end `cmp x, y; jne rel8`**. -/
theorem cmp_jne8_end (m : MState) (x y : Reg) (rel : BitVec 8) :
    ∃ c, run8 [(.base (.alu .q .cmp (.reg x) y), 3), (.base (.jcc8 .ne rel), 2)] m =
        some ⟨c, m.memory⟩ ∧ (∀ r, c.read r = m.core.read r) ∧
      c.rip = if m.core.read x = m.core.read y then m.core.rip + 5#64
        else m.core.rip + 5#64 + rel.signExtend 64 := by
  by_cases h : m.core.read x = m.core.read y <;>
  simp [run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Cond.eval, cmp_zero, h,
    Silmaril.X86.Ext.kNot, BitVec.add_assoc]

namespace Cert

theorem from_block {F : Cert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) {m0 : MState} {b : Blk} {m : MState} (hb : b ∈ F.blocks)
    (ha : F.ann b.off m0 m) (hrip : m.core.rip = F.base + BitVec.ofNat 64 b.off)
    (hl : Loaded m.memory F.base F.code) : ∃ t, Reaches Open.step m t ∧ Q m0 t :=
  Silmaril.Proofs.X86.BlockCert8.from_block hc hvc m0 _ b m rfl hb ha hrip hl

theorem next_of {F : Cert} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat} (b : Blk)
    (hb : b ∈ F.blocks) (hrip : m'.core.rip = F.base + BitVec.ofNat 64 b.off)
    (ha : F.ann b.off m0 m') (hμ : F.measure b.off m0 m' < μ) : F.Next Q m0 μ m' :=
  .inr ⟨b, hb, hrip, ha, hμ⟩

theorem vc_of_blocks {F : Cert} {Q : MState → MState → Prop}
    (h : ∀ b ∈ F.blocks, F.BlockVC Q b) : F.VC Q := h

/-- **Total correctness from a certificate.** -/
theorem total {F : Cert} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Silmaril.Proofs.X86.BlockCert8.total S hentry hc hvc hpre

/-- **The function contract** of a certificate. -/
def contract (F : Cert) (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    FnContract Open.isa :=
  ⟨S, total S hentry hc hvc hpre⟩

end Cert

end Silmaril.X86.BlockCert8
