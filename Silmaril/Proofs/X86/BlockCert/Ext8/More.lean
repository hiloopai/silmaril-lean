module

public import Silmaril.X86.BlockCert.Ext8.Thms

/-!
# More single-instruction and block-end lemmas for `Ext8` listings

Register effects (`Eff`) of `not r32`, `lea`, `nop`, `and r32, imm8`, `add r64, r64`,
`mov r32, imm32`, `xor r64, r64`, `xor r32, r32`; and the block ends `test r,r; je`,
`cmp r, imm8; jbe` and `ret`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.X86.BlockCert8

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Mem loadN)
open Silmaril.Process (Memory)

theorem not_d (s : State) (mem : Memory) (l : Nat) (d : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.unary .d .not (.reg d))) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then (~~~((s.read d).setWidth 32)).setWidth 64 else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]; rfl
  · simp [h, Silmaril.X86.Ext.Sz.write]

theorem lea_q (s : State) (mem : Memory) (l : Nat) (d : Reg) (M : Mem)
    (hM : M.base ≠ .rip) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.lea .q d M)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then M.addr s 0#64 else s.read r) := by
  have := Mem.addr_congr_of_ne_rip hM s (s.rip + BitVec.ofNat 64 l) 0#64
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write, this]
  · simp [h, Silmaril.X86.Ext.Sz.write]

theorem nop_eff (s : State) (mem : Memory) (l : Nat) (n : Fin 15) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.nop n)) s mem l = .ok c mem ∧
      Eff s c l (fun r => s.read r) :=
  ⟨_, rfl, rfl, fun _ => rfl⟩

theorem and_d_i8 (s : State) (mem : Memory) (l : Nat) (d : Reg) (k : BitVec 8) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.aluI8 .d .and (.reg d) k)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then ((s.read d).setWidth 32 &&& k.signExtend 32).setWidth 64
        else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.aluStep,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.AluOp.resultN]
    exact BitVec.setWidth_and ..
  · simp [h, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM]

theorem add_q_rr (s : State) (mem : Memory) (l : Nat) (d a : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.alu .q .add (.reg d) a)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then s.read d + s.read a else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.aluStep,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.AluOp.resultN]; rfl
  · simp [h, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM]

theorem xor_q_rr (s : State) (mem : Memory) (l : Nat) (d a : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.alu .q .xor (.reg d) a)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then s.read d ^^^ s.read a else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.aluStep,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.AluOp.resultN]; rfl
  · simp [h, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM]

theorem xor_d_self (s : State) (mem : Memory) (l : Nat) (d : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.alu .d .xor (.reg d) d)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then 0#64 else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.aluStep,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.AluOp.resultN]
    show BitVec.setWidth 64 ((BitVec.setWidth 32 (s.read r) ^^^ BitVec.setWidth 32 (s.read r) : BitVec 32)) = 0#64
    simp
  · simp [h, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM]

theorem movI32_eff (s : State) (mem : Memory) (l : Nat) (d : Reg) (v : BitVec 32) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.movI32 d v)) s mem l = .ok c mem ∧
      Eff s c l (fun r => if r = d then v.setWidth 64 else s.read r) := by
  refine ⟨_, rfl, rfl, fun r => ?_⟩
  by_cases h : r = d
  · subst h; simp [Silmaril.X86.Ext.Sz.write]
  · simp [h, Silmaril.X86.Ext.Sz.write]

/-- `test x, x` sets the zero flag iff `x = 0`. -/
theorem test_zero (s : State) (mem : Memory) (l : Nat) (x : Reg) :
    ∃ c, Silmaril.X86.Ext8.exec (.base (.test .q (.reg x) x)) s mem l = .ok c mem ∧
      c.regs = s.regs ∧ c.rip = s.rip + BitVec.ofNat 64 l ∧
      c.flags.zero = some (decide (s.read x = 0)) := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  show some (((s.read x &&& s.read x : Word)) == 0#64) = _
  rw [BitVec.and_self]
  rfl

/-- **A block end `test x, x; je rel32`**. -/
theorem test_je_end (m : MState) (x : Reg) (rel : BitVec 32) :
    ∃ c, run8 [(.base (.test .q (.reg x) x), 3), (.base (.jcc .e rel), 6)] m =
        some ⟨c, m.memory⟩ ∧ (∀ r, c.read r = m.core.read r) ∧
      c.rip = if m.core.read x = 0 then m.core.rip + 9#64 + rel.signExtend 64
        else m.core.rip + 9#64 := by
  obtain ⟨c1, h1, hr1, hp1, hz1⟩ := test_zero m.core m.memory 3 x
  rw [run8_cons_of h1 hp1]
  by_cases h : m.core.regs x = 0#64 <;>
  simp [run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.Cond.eval, hz1, h, hp1, BitVec.add_assoc, Silmaril.X86.State.read, hr1]

/-- **A block end `test x, x; je rel8`**. -/
theorem test_je8_end (m : MState) (x : Reg) (rel : BitVec 8) :
    ∃ c, run8 [(.base (.test .q (.reg x) x), 3), (.base (.jcc8 .e rel), 2)] m =
        some ⟨c, m.memory⟩ ∧ (∀ r, c.read r = m.core.read r) ∧
      c.rip = if m.core.read x = 0 then m.core.rip + 5#64 + rel.signExtend 64
        else m.core.rip + 5#64 := by
  obtain ⟨c1, h1, hr1, hp1, hz1⟩ := test_zero m.core m.memory 3 x
  rw [run8_cons_of h1 hp1]
  by_cases h : m.core.regs x = 0#64 <;>
  simp [run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.Cond.eval, hz1, h, hp1, BitVec.add_assoc, Silmaril.X86.State.read, hr1]

/-- **A block end `cmp $imm8, x; jbe rel32`** (unsigned `x ≤ imm`). -/
theorem cmpi8_jbe_end (m : MState) (x : Reg) (k : BitVec 8) (rel : BitVec 32) :
    ∃ c, run8 [(.base (.aluI8 .q .cmp (.reg x) k), 4), (.base (.jcc .be rel), 6)] m =
        some ⟨c, m.memory⟩ ∧ (∀ r, c.read r = m.core.read r) ∧
      c.rip = if m.core.read x ≤ k.signExtend 64 then m.core.rip + 10#64 + rel.signExtend 64
        else m.core.rip + 10#64 := by
  have hbe0 : ∀ x y : Word,
      Silmaril.X86.Ext.kOr (some (Silmaril.X86.Ext.subBorrowN x y))
      (some (Silmaril.X86.Ext.isZeroN (x - y))) = some (decide (x ≤ y)) := by
    intro x y
    simp only [Silmaril.X86.Ext.isZeroN]
    rw [Silmaril.X86.Ext.subBorrowN_eq (w := 63)]
    by_cases hl : (x : Word) < (y : Word)
    · have h1 : BitVec.ult (x : Word) (y : Word) = true := BitVec.ult_iff_lt.mpr hl
      have h2 : (x : Word) ≤ (y : Word) := by bv_omega
      rw [h1]; simp [Silmaril.X86.Ext.kOr, h2]
    · have h1 : BitVec.ult (x : Word) (y : Word) = false := by
        cases hu : BitVec.ult x y
        · rfl
        · exact absurd (BitVec.ult_iff_lt.mp hu) hl
      rw [h1]
      by_cases e : (x : Word) = (y : Word)
      · have h3 : ((x : Word) - (y : Word) == 0#64) = true := by simp [e]
        rw [h3]; simp [Silmaril.X86.Ext.kOr, e]
      · have h3 : ((x : Word) - (y : Word) == 0#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h0; apply e; bv_omega
        have h4 : ¬ (x : Word) ≤ (y : Word) := by bv_omega
        rw [h3]; simp [Silmaril.X86.Ext.kOr, h4]
  obtain ⟨c1, h1, hr1, hp1, hf1⟩ : ∃ c, Silmaril.X86.Ext8.exec
      (.base (.aluI8 .q .cmp (.reg x) k)) m.core m.memory 4 = .ok c m.memory ∧
      c.regs = m.core.regs ∧ c.rip = m.core.rip + 4#64 ∧
      Silmaril.X86.Ext.Cond.eval c.flags .be = some (decide (m.core.read x ≤ k.signExtend 64)) := by
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    show Silmaril.X86.Ext.Cond.eval
      (Silmaril.X86.Ext.subFlagsN (m.core.read x) (k.signExtend 64)) .be = _
    simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.subFlagsN]
    exact hbe0 _ _
  rw [run8_cons_of h1 hp1]
  by_cases h : m.core.regs x ≤ k.signExtend 64 <;>
  simp [run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, hf1, h,
    hp1, BitVec.add_assoc, Silmaril.X86.State.read, hr1]

/-- **A block end `ret`**, with the return address readable at `rsp`. -/
theorem ret_end (m : MState) {w : Word}
    (h : (m.memory.readBytes (m.core.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes? = some w) :
    ∃ c, run8 [(.base .ret, 1)] m = some ⟨c, m.memory⟩ ∧ c.rip = w ∧
      c.read .rsp = m.core.read .rsp + 8#64 ∧ ∀ r, r ≠ .rsp → c.read r = m.core.read r := by
  cases hb : m.memory.readBytes (m.core.read .rsp).toNat 8 with
  | none => rw [hb] at h; cases h
  | some bs =>
    rw [hb] at h
    simp [run8, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.popWord, hb,
      Option.bind] at h ⊢
    simp only [h]
    refine ⟨_, rfl, rfl, by simp, fun r hr => ?_⟩
    show (m.core.write .rsp _).read r = _
    exact Silmaril.X86.State.read_write_other _ _ _ _ hr

end Silmaril.X86.BlockCert8
