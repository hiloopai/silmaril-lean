module

public import Silmaril.Machine.RiscV.LPS.Embed.Defs
public import Mathlib.Tactic.SplitIfs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-!
# Instruction-level agreement of LPS and `RiscV.Ext`

`Agree s c` relates an Ext register state and an LPS core (same pc, same architectural
integer register reads; x0 reads zero in both).

* `exec_embedCompute`: on every register-only Ext instruction (the 21 base operations,
  the RV64 word forms, and all of RV64M), LPS's `exec` retires with exactly Ext's value in
  `rd` and pc + 4. The M-extension lemmas (`mulDiv_mulh`, `mulDiv_div`, …) show the two
  formulations agree: LPS computes on mathematical integers and wraps (`Int.tdiv`,
  `Int.fdiv` of the exact product), Ext uses `BitVec.sdiv`/`srem` and 128-bit products.
* `refines_retire`: for every non-memory Ext instruction, whenever Ext retires, LPS
  retires to an agreeing core.
* `lps_retires_jump`: branches and jumps always retire in LPS, including where Ext
  (no C extension, IALIGN = 32) reports `targetMisaligned`.
* `exec_embed_load`/`exec_embed_store`: LPS issues its memory effect at Ext's effective
  address without an alignment test.

All proofs are checked by the kernel (no `bv_decide`).
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

open Silmaril.RiscV
open Core (rset)

/-- An Ext register state and an LPS core agree: same pc and the same architectural integer
register reads. -/
def Agree (s : RiscV.State) (c : Core) : Prop := c.pc = s.pc ∧ ∀ r, c.rget r = s.read r

theorem ltS_eq {n : Nat} (a b : BitVec n) : ltS a b = a.slt b := by
  simp [ltS, BitVec.slt]

theorem ltU_eq {n : Nat} (a b : BitVec n) : ltU a b = a.ult b := by
  simp [ltU, BitVec.ult]

theorem rget_rset (r q : Reg) (v : Word) (c : Core) :
    (rset r v c).rget q = if q = 0#5 then 0#64 else if q = r then v else c.rget q := by
  unfold Core.rset Core.rget isX0
  by_cases hq : q = 0#5
  · subst hq; simp [w0]
  · have hq' : (q.toNat == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h; exact hq (BitVec.eq_of_toNat_eq (by simpa using h))
    by_cases hr : r = 0
    · subst hr
      simp [hq', hq]
    · have hr' : (r.toNat == 0) = false := by
        simp only [beq_eq_false_iff_ne]; intro h; exact hr (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hq', hr', Bool.false_eq_true, ↓reduceIte, hq, regGet]
      by_cases hqr : q = r
      · subst hqr; simp [BvMap.get_set_same]
      · simp [hqr, BvMap.get_set_other _ _ (Ne.symm hqr)]

theorem read_write' (s : RiscV.State) (r q : Reg) (v : Word) :
    (s.write r v).read q = if q = 0#5 then 0#64 else if q = r then v else s.read q := by
  by_cases hq : q = 0#5
  · subst hq; simp
  · by_cases hqr : q = r
    · subst hqr; simp [hq, RiscV.State.read_write_same s q v hq]
    · simp [hq, hqr, RiscV.State.read_write_other s r q v hqr]

theorem Agree.write {s : RiscV.State} {c : Core} (h : Agree s c) (r : Reg) (v p : Word) :
    Agree { s.write r v with pc := p } (rset r v { c with pc := p }) := by
  refine ⟨?_, fun q => ?_⟩
  · unfold Core.rset; split <;> rfl
  · rw [rget_rset]
    change _ = (s.write r v).read q
    rw [read_write']
    have := h.2 q
    simp only [Core.rget] at this ⊢
    split <;> simp_all

theorem low32_eq (x : Word) : low32 x = Ext.low32 x := by
  apply BitVec.eq_of_toNat_eq
  simp [low32, Ext.low32]

theorem ofInt_neg_one (n : Nat) : BitVec.ofInt n (-1) = BitVec.allOnes n := by
  rw [BitVec.ofInt_neg, ← BitVec.neg_one_eq_allOnes]
  rfl

theorem mulDiv_div {n : Nat} (a b : BitVec n) : mulDiv .div a b = Ext.divS a b := by
  unfold mulDiv Ext.divS
  by_cases hb : b = 0#n
  · simp [hb, ofInt_neg_one]
  · have : (b.toNat == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h0; exact hb (BitVec.eq_of_toNat_eq (by simpa using h0))
    simp only [this, hb, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]

theorem mulDiv_divu {n : Nat} (a b : BitVec n) : mulDiv .divu a b = Ext.divU a b := by
  unfold mulDiv Ext.divU
  by_cases hb : b = 0#n
  · simp [hb, ofInt_neg_one]
  · have : (b.toNat == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h0; exact hb (BitVec.eq_of_toNat_eq (by simpa using h0))
    simp only [this, hb, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)

theorem mulDiv_rem {n : Nat} (a b : BitVec n) : mulDiv .rem a b = Ext.remS a b := by
  unfold mulDiv Ext.remS
  by_cases hb : b = 0#n
  · simp [hb]
  · have : (b.toNat == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h0; exact hb (BitVec.eq_of_toNat_eq (by simpa using h0))
    simp only [this, hb, Bool.false_eq_true, ↓reduceIte]
    rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem mulDiv_remu {n : Nat} (a b : BitVec n) : mulDiv .remu a b = Ext.remU a b := by
  unfold mulDiv Ext.remU
  by_cases hb : b = 0#n
  · simp [hb]
  · have : (b.toNat == 0) = false := by
      simp only [beq_eq_false_iff_ne]; intro h0; exact hb (BitVec.eq_of_toNat_eq (by simpa using h0))
    simp only [this, hb, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_umod]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)

theorem mulDiv_mulhu (a b : Word) : mulDiv .mulhu a b = Ext.mulHighU a b := by
  unfold mulDiv mulhUU Ext.mulHighU
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb
    simpa using this
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt hprod]
  rw [BitVec.toNat_ofInt]
  have : Int.fdiv ((a.toNat : Int) * (b.toNat : Int)) (2 ^ 64) =
      ((a.toNat * b.toNat / 2 ^ 64 : Nat) : Int) := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]; push_cast; rfl
  rw [this]
  omega


/-- Bits `[64, 128)` of an exact 128-bit product, read as a 64-bit word, are its floor
quotient by `2^64` modulo `2^64`. -/
private theorem high_of_ofInt (P : Int) :
    ((BitVec.ofInt 128 P >>> 64).setWidth 64 : BitVec 64) = BitVec.ofInt 64 (Int.fdiv P (2 ^ 64)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofInt,
    Nat.shiftRight_eq_div_pow]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem mulDiv_mulh (a b : Word) : mulDiv .mulh a b = Ext.mulHigh a b := by
  unfold mulDiv mulhSS Ext.mulHigh
  have : a.signExtend 128 * b.signExtend 128 = BitVec.ofInt 128 (a.toInt * b.toInt) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_mul, BitVec.toInt_ofInt, BitVec.toInt_signExtend_of_le (by decide),
      BitVec.toInt_signExtend_of_le (by decide)]
  rw [this, high_of_ofInt]

theorem mulDiv_mulhsu (a b : Word) : mulDiv .mulhsu a b = Ext.mulHighSU a b := by
  unfold mulDiv mulhSU Ext.mulHighSU
  have hb : (b.setWidth 128).toInt = (b.toNat : Int) := by
    rw [BitVec.toInt_setWidth]
    have := b.isLt
    rw [Int.bmod_eq_of_le] <;> omega
  have : a.signExtend 128 * b.setWidth 128 = BitVec.ofInt 128 (a.toInt * (b.toNat : Int)) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_mul, BitVec.toInt_ofInt, BitVec.toInt_signExtend_of_le (by decide), hb]
  rw [this, high_of_ofInt]


theorem ite_one_zero (p : Bool) : (if p then (1 : Word) else 0) = boolWord p := by
  cases p <;> rfl

theorem toNat_and_63 (b : Word) : (b &&& BitVec.ofNat 64 63).toNat = (b.setWidth 6).toNat := by
  rw [BitVec.toNat_and, BitVec.toNat_setWidth]
  show b.toNat &&& (2 ^ 6 - 1) = b.toNat % 2 ^ 6
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem toNat_and_31 (b : BitVec 32) : (b &&& BitVec.ofNat 32 31).toNat = b.toNat % 32 := by
  rw [BitVec.toNat_and]
  show b.toNat &&& (2 ^ 5 - 1) = b.toNat % 2 ^ 5
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem alu64_shift (op : ShiftOp) (a b : Word) :
    alu64 (embedShiftOp op) a b = ShiftOp.eval op a (b.setWidth 6) := by
  cases op <;> simp only [embedShiftOp, alu64, alu, ShiftOp.eval, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', toNat_and_63]

theorem alu64_shiftImm (op : ShiftOp) (a : Word) (s : BitVec 6) :
    alu64 (embedShiftOp op) a (zext 64 s) = ShiftOp.eval op a s := by
  rw [alu64_shift]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [zext]

theorem alu32_shift (op : ShiftOp) (x : Word) (s : BitVec 32) :
    sext 64 (alu32 (embedShiftOp op) (low32 x) s) =
      Ext.evalShiftW op x (BitVec.ofNat 5 (s.toNat % 32)) := by
  have hs : (s &&& BitVec.ofNat 32 31).toNat = (BitVec.ofNat 5 (s.toNat % 32)).toNat := by
    rw [toNat_and_31]; simp
  cases op <;> simp only [embedShiftOp, alu32, alu, Ext.evalShiftW, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', hs, low32_eq, sext, Ext.sext32]


theorem regW_shift (op : ShiftOp) (x y : Word) :
    sext 64 (alu32 (embedShiftOp op) (low32 x) (low32 y)) = Ext.evalShiftW op x (y.setWidth 5) := by
  rw [alu32_shift]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [low32]

theorem shiftW_amount (a : BitVec 5) : BitVec.ofNat 5 ((zext 32 a).toNat % 32) = a := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp [zext]
  omega

theorem exec_embedCompute {s : RiscV.State} {c : Core} (h : Agree s c) (cmp : Ext.Compute) :
    exec 4 (embedCompute cmp) c =
      .done (rset cmp.dest (cmp.value s) { c with pc := c.pc + 4 }) := by
  have hpc := h.1
  cases cmp with
  | base b =>
    cases b with
    | imm op rd rs1 v =>
      cases op <;> simp only [embedCompute, embedBase, embedImmOp, exec, h.2, Ext.Compute.value,
        RiscV.Instr.value, ImmOp.eval, Ext.Compute.dest, RiscV.Instr.dest, Eff.done.injEq] <;>
        congr 1 <;> simp only [alu64, alu, sext, ltS_eq, ltU_eq, ite_one_zero]
    | reg op rd rs1 rs2 =>
      cases op <;> simp only [embedCompute, embedBase, embedRegOp, exec, h.2, Ext.Compute.value,
        RiscV.Instr.value, RegOp.eval, Ext.Compute.dest, RiscV.Instr.dest, Eff.done.injEq] <;>
        congr 1 <;> first
          | simp only [alu64, alu, ltS_eq, ltU_eq, ite_one_zero]; done
          | exact alu64_shift .sll _ _
          | exact alu64_shift .srl _ _
          | exact alu64_shift .sra _ _
    | shift op rd rs1 a =>
      simp only [embedCompute, embedBase, exec, h.2, Ext.Compute.value, RiscV.Instr.value,
        Ext.Compute.dest, RiscV.Instr.dest, Eff.done.injEq]
      congr 1
      exact alu64_shiftImm op _ _
    | upper op rd v =>
      cases op <;> simp only [embedCompute, embedBase, exec, hpc, Ext.Compute.value,
        RiscV.Instr.value, UpperOp.eval, Ext.Compute.dest, RiscV.Instr.dest, Eff.done.injEq] <;>
        congr 1
  | addiw rd rs1 imm =>
    simp only [embedCompute, exec, h.2, Ext.Compute.value, Ext.Compute.dest, Eff.done.injEq]
    congr 1
  | shiftW op rd rs1 a =>
    simp only [embedCompute, exec, h.2, Ext.Compute.value, Ext.Compute.dest, Eff.done.injEq]
    congr 1
    rw [alu32_shift, shiftW_amount]
  | regW op rd rs1 rs2 =>
    have base : ∀ o : Ext.RegWOp, exec 4 (embedCompute (.regW o rd rs1 rs2)) c =
        .done (rset rd (sext 64 (alu32 (embedRegWOp o) (low32 (s.read rs1)) (low32 (s.read rs2))))
          { c with pc := c.pc + 4 }) := by
      intro o; simp only [embedCompute, exec, h.2]
    rw [base]
    simp only [Ext.Compute.value, Ext.Compute.dest, Eff.done.injEq]
    congr 1
    cases op with
    | add => simp only [embedRegWOp, Ext.RegWOp.eval, sext, alu32, alu, low32_eq, Ext.sext32]
    | sub => simp only [embedRegWOp, Ext.RegWOp.eval, sext, alu32, alu, low32_eq, Ext.sext32]
    | sll => exact regW_shift .sll _ _
    | srl => exact regW_shift .srl _ _
    | sra => exact regW_shift .sra _ _
  | mulDiv op rd rs1 rs2 =>
    cases op <;> (simp only [embedCompute, embedMulOp, exec, h.2, Ext.Compute.value,
      Ext.MulOp.eval, Ext.Compute.dest, Eff.done.injEq, mulDiv_mulh, mulDiv_mulhsu, mulDiv_mulhu,
      mulDiv_div, mulDiv_divu, mulDiv_rem, mulDiv_remu]; try congr 1)
  | mulDivW op rd rs1 rs2 =>
    cases op <;> simp only [embedCompute, embedMulWOp, exec, h.2, Ext.Compute.value,
      Ext.MulWOp.eval, Ext.Compute.dest, Eff.done.injEq, low32_eq, mulDiv_div, mulDiv_divu,
      mulDiv_rem, mulDiv_remu] <;> congr 1

/-- Agreement is preserved by every register-only instruction. -/
theorem Agree.compute {s : RiscV.State} {c : Core} (h : Agree s c) (cmp : Ext.Compute) :
    ∃ c', exec 4 (embedCompute cmp) c = .done c' ∧ Agree (cmp.step s) c' := by
  refine ⟨_, exec_embedCompute h cmp, ?_⟩
  have := h.write cmp.dest (cmp.value s) (s.pc + 4)
  rw [h.1] at *
  exact this


theorem eqB_eq {n : Nat} (a b : BitVec n) : eqB a b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [eqB]
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [eqB, h, this]

theorem branchTaken_embed (op : Ext.BranchOp) (a b : Word) :
    branchTaken (embedBranchOp op) a b = op.eval a b := by
  cases op <;> simp [branchTaken, embedBranchOp, Ext.BranchOp.eval, eqB_eq, ltS_eq, ltU_eq, bne]

theorem Agree.withPc {s : RiscV.State} {c : Core} (h : Agree s c) (p : Word) :
    Agree { s with pc := p } { c with pc := p } :=
  ⟨rfl, fun r => by
    have := h.2 r
    simp only [Core.rget, RiscV.State.read] at this ⊢
    exact this⟩

/-- An embedded branch always retires in LPS; its pc is Ext's target or fall-through. -/
theorem exec_embed_branch {s : RiscV.State} {c : Core} (h : Agree s c) (op : Ext.BranchOp)
    (rs1 rs2 : Reg) (half : BitVec 12) :
    exec 4 (embed (.branch op rs1 rs2 half)) c =
      .done { c with pc := if op.eval (s.read rs1) (s.read rs2) then s.pc + Ext.branchOffset half
                           else s.pc + 4 } := by
  simp only [embed, exec, h.2, branchTaken_embed, h.1]
  rfl

/-- An embedded JAL always retires in LPS. -/
theorem exec_embed_jal {s : RiscV.State} {c : Core} (h : Agree s c) (rd : Reg)
    (half : BitVec 20) :
    exec 4 (embed (.jal rd half)) c =
      .done (rset rd (s.pc + 4) { c with pc := s.pc + Ext.jalOffset half }) := by
  simp only [embed, exec, h.1]
  rfl

/-- An embedded JALR always retires in LPS, at Ext's target. -/
theorem exec_embed_jalr {s : RiscV.State} {c : Core} (h : Agree s c) (rd rs1 : Reg)
    (off : BitVec 12) :
    exec 4 (embed (.jalr rd rs1 off)) c =
      .done (rset rd (s.pc + 4) { c with pc := Ext.jalrTarget s rs1 off }) := by
  simp only [embed, exec, h.1, h.2]
  rfl


/-- Step-level refinement on every non-memory Ext instruction: whenever Ext retires, LPS
retires to an agreeing core. -/
theorem refines_retire {m m' : Ext.MState} {c : Core} (h : Agree m.core c) (i : Ext.Instr)
    (hload : ∀ op rd rs1 off, i ≠ .load op rd rs1 off)
    (hstore : ∀ op rs1 rs2 off, i ≠ .store op rs1 rs2 off)
    (hr : i.exec m = .retired m') : ∃ c', exec 4 (embed i) c = .done c' ∧ Agree m'.core c' := by
  cases i with
  | compute cmp =>
    cases hr
    exact h.compute cmp
  | load op rd rs1 off => exact absurd rfl (hload op rd rs1 off)
  | store op rs1 rs2 off => exact absurd rfl (hstore op rs1 rs2 off)
  | branch op rs1 rs2 half =>
    refine ⟨_, exec_embed_branch h op rs1 rs2 half, ?_⟩
    simp only [Ext.Instr.exec, Ext.jumpTo] at hr
    split at hr
    · rename_i taken
      split at hr
      · cases hr; simp only [taken, ↓reduceIte]; exact h.withPc _
      · cases hr
    · rename_i taken
      cases hr; simp only [taken]; exact h.withPc _
  | jal rd half =>
    refine ⟨_, exec_embed_jal h rd half, ?_⟩
    simp only [Ext.Instr.exec, Ext.jumpTo] at hr
    split at hr
    · cases hr; exact h.write rd _ _
    · cases hr
  | jalr rd rs1 off =>
    refine ⟨_, exec_embed_jalr h rd rs1 off, ?_⟩
    simp only [Ext.Instr.exec, Ext.jumpTo] at hr
    split at hr
    · cases hr; exact h.write rd _ _
    · cases hr
  | ebreak => cases hr

/-- Where Ext reports `targetMisaligned` (IALIGN = 32), LPS (IALIGN = 16) still retires:
on such instructions LPS is strictly more defined. -/
theorem lps_retires_jump {c : Core} (i : Ext.Instr)
    (hjump : (∃ op rs1 rs2 h, i = .branch op rs1 rs2 h) ∨ (∃ rd h, i = .jal rd h) ∨
      (∃ rd rs1 o, i = .jalr rd rs1 o)) :
    ∃ c', exec 4 (embed i) c = .done c' := by
  rcases hjump with ⟨op, rs1, rs2, half, rfl⟩ | ⟨rd, half, rfl⟩ | ⟨rd, rs1, o, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩


/-- An embedded load issues one LPS memory read at Ext's effective address, with no alignment
test: misaligned plain loads are performed by LPS, where Ext reports `dataMisaligned`. -/
theorem exec_embed_load {s : RiscV.State} {c : Core} (h : Agree s c) (op : Ext.LoadOp)
    (rd rs1 : Reg) (off : BitVec 12) :
    exec 4 (embed (.load op rd rs1 off)) c =
      loadVal (embedLoadOp op).1 (embedLoadOp op).2 (Ext.effectiveAddress s rs1 off)
        (fun v => .done (rset rd v { c with pc := c.pc + 4 })) := by
  simp only [embed, exec, h.2]
  rfl

/-- An embedded store issues one LPS memory write of the low bytes of `rs2` at Ext's
effective address, with no alignment test. -/
theorem exec_embed_store {s : RiscV.State} {c : Core} (h : Agree s c) (op : Ext.StoreOp)
    (rs1 rs2 : Reg) (off : BitVec 12) :
    exec 4 (embed (.store op rs1 rs2 off)) c =
      storeVal (embedStoreOp op) (Ext.effectiveAddress s rs1 off) (s.read rs2)
        (.done (invalResv (Ext.effectiveAddress s rs1 off) { c with pc := c.pc + 4 })) := by
  simp only [embed, exec, h.2]
  rfl

end Silmaril.RiscV.LPS
