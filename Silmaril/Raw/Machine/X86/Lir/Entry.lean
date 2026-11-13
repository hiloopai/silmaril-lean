module

public import Silmaril.Machine.X86.Lir.Moves.Defs

/-!
# The prologue

`sim_entry`: from the machine at the first instruction of a function
(`Env.Entry`), the prologue either stops at the UD2 of its stack-limit check
(`Env.Overflow`), when fewer than `need` bytes of stack are left, or reaches
the entry block with the frame set up and the parameters in their locations
(`Env.Body`).
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

theorem exec_aluI_q (s : State) (m : Memory) (op : Silmaril.X86.AluOp) (dst : Reg) (imm : BitVec 32)
    (h : op ≠ .cmp) :
    Ext.exec (.aluI .q op (.reg dst) imm) s m =
      .ok { s.write dst (Ext.AluOp.resultN op (s.read dst) (imm.signExtend 64)) with
        flags := Ext.AluOp.flagsN op (s.read dst) (imm.signExtend 64)
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.aluI .q op (.reg dst) imm).length } m := by
  rw [Ext.exec_aluI_reg _ _ _ _ _ _ h]; rfl

theorem runSeq_subRsp {s : State} {m : Memory} {e F : Nat} (hrsp : s.read .rsp = BitVec.ofNat 64 e)
    (hF : F < 2 ^ 31) (hle : F ≤ e) (he : e < 2 ^ 64) (rest : List Ext.Instr) :
    ∃ s', runSeq (.aluI .q .sub (.reg .rsp) (BitVec.ofNat 32 F) :: rest) s m = runSeq rest s' m ∧
      s'.read .rsp = BitVec.ofNat 64 (e - F) ∧ (∀ q, q ≠ .rsp → s'.read q = s.read q) := by
  have ex := exec_aluI_q s m .sub .rsp (BitVec.ofNat 32 F) (by decide)
  refine ⟨_, runSeq_cons_of ex (by intro h; cases h) rfl, ?_,
    fun q hq => by simp [State.read_write_other _ _ _ _ hq]⟩
  simp only [read_flags_rip, State.read_write_same, hrsp, Ext.AluOp.resultN, signExtend_ofNat32 hF]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt (a := F) (by omega), Nat.mod_eq_of_lt (a := e - F) (by omega)]
  omega

theorem runSeq_addRsp {s : State} {m : Memory} {e F : Nat} (hrsp : s.read .rsp = BitVec.ofNat 64 e)
    (hF : F < 2 ^ 31) (rest : List Ext.Instr) :
    ∃ s', runSeq (.aluI .q .add (.reg .rsp) (BitVec.ofNat 32 F) :: rest) s m = runSeq rest s' m ∧
      s'.read .rsp = BitVec.ofNat 64 (e + F) ∧ (∀ q, q ≠ .rsp → s'.read q = s.read q) := by
  have ex := exec_aluI_q s m .add .rsp (BitVec.ofNat 32 F) (by decide)
  refine ⟨_, runSeq_cons_of ex (by intro h; cases h) rfl, ?_,
    fun q hq => by simp [State.read_write_other _ _ _ _ hq]⟩
  simp only [read_flags_rip, State.read_write_same, hrsp, Ext.AluOp.resultN, signExtend_ofNat32 hF,
    BitVec.ofNat_add]

section

variable {S : Space} {n : Nat} (hv : S.Valid n)
include hv

theorem runSeq_push {s : State} {m : Memory} (hreg : m.regions = S.regions n) {e : Nat}
    (hrsp : s.read .rsp = BitVec.ofNat 64 e) (hlo : S.stackLo + 8 ≤ e) (hhi : e ≤ S.stackHi)
    (r : Reg) (rest : List Ext.Instr) :
    ∃ s' m', runSeq (.push r :: rest) s m = runSeq rest s' m' ∧
      s'.read .rsp = BitVec.ofNat 64 (e - 8) ∧ (∀ q, q ≠ .rsp → s'.read q = s.read q) ∧
      WordAt m' (e - 8) (s.read r) ∧ Memory.WritesOnly m m' (e - 8) 8 := by
  obtain ⟨m', h, w, o⟩ := push_at hv hreg hrsp hlo hhi (s.read r)
  have ex := exec_push_ok s m r (by rw [h, hrsp, sub8_eq (by omega) (by have := hv.stack_end; omega)])
  rw [hrsp, sub8_eq (by omega) (by have := hv.stack_end; omega)] at ex
  exact ⟨_, m', runSeq_cons_of ex (by intro h; cases h) rfl, by simp,
    fun q hq => by simp [State.read_write_other _ _ _ _ hq], w, o⟩

theorem runSeq_pop {s : State} {m : Memory} (hreg : m.regions = S.regions n) {e : Nat}
    (hrsp : s.read .rsp = BitVec.ofNat 64 e) (hlo : S.stackLo ≤ e) (hhi : e + 8 ≤ S.stackHi)
    {v : Word} (hw : WordAt m e v) (r : Reg) (hr : r ≠ .rsp) (rest : List Ext.Instr) :
    ∃ s', runSeq (.pop r :: rest) s m = runSeq rest s' m ∧
      s'.read .rsp = BitVec.ofNat 64 (e + 8) ∧ s'.read r = v ∧
      (∀ q, q ≠ .rsp → q ≠ r → s'.read q = s.read q) := by
  have h := pop_at hv hreg hrsp hlo hhi hw
  have ex := exec_pop_ok s m r (v := v) (by rw [h, hrsp, add8_eq])
  exact ⟨_, runSeq_cons_of ex (by intro h; cases h) rfl,
    by simp [State.read_write_other _ _ _ _ (Ne.symm hr), hrsp, add8_eq], by simp,
    fun q hq hqr => by simp [State.read_write_other _ _ _ _ hqr, State.read_write_other _ _ _ _ hq]⟩

theorem run_pushSeq {c : State} {m : Memory} (hreg : m.regions = S.regions n) {e ns : Nat}
    (hrsp : c.read .rsp = BitVec.ofNat 64 e) (hlo : S.stackLo + 32 + frameSize ns ≤ e)
    (hhi : e ≤ S.stackHi) (hF : frameSize ns < 2 ^ 31) :
    ∃ c' m', runSeq (pushSeq ns) c m = some (c', m') ∧
      c'.read .rsp = BitVec.ofNat 64 (e - 32 - frameSize ns) ∧
      (∀ r, r ≠ .rsp → c'.read r = c.read r) ∧
      Env.Pushed e m' (c.read .rbp) (c.read .rbx) (c.read .r12) (c.read .r13) ∧
      m'.regions = m.regions ∧ (∀ x, x < e - 32 ∨ e ≤ x → m'.bytes.get? x = m.bytes.get? x) := by
  have he : e < 2 ^ 64 := by have := hv.stack_end; omega
  obtain ⟨s₁, m₁, h₁, r₁, k₁, w₁, o₁⟩ := runSeq_push hv hreg hrsp (by omega) hhi .rbp
    [.push .rbx, .push .r12, .push .r13, .aluI .q .sub (.reg .rsp) (BitVec.ofNat 32 (frameSize ns))]
  obtain ⟨s₂, m₂, h₂, r₂, k₂, w₂, o₂⟩ := runSeq_push hv (o₁.1.trans hreg) r₁ (by omega) (by omega)
    .rbx [.push .r12, .push .r13, .aluI .q .sub (.reg .rsp) (BitVec.ofNat 32 (frameSize ns))]
  obtain ⟨s₃, m₃, h₃, r₃, k₃, w₃, o₃⟩ := runSeq_push hv (o₂.1.trans (o₁.1.trans hreg)) r₂
    (by omega) (by omega) .r12 [.push .r13, .aluI .q .sub (.reg .rsp) (BitVec.ofNat 32 (frameSize ns))]
  obtain ⟨s₄, m₄, h₄, r₄, k₄, w₄, o₄⟩ := runSeq_push hv (o₃.1.trans (o₂.1.trans (o₁.1.trans hreg)))
    r₃ (by omega) (by omega) .r13 [.aluI .q .sub (.reg .rsp) (BitVec.ofNat 32 (frameSize ns))]
  obtain ⟨s₅, h₅, r₅, k₅⟩ := runSeq_subRsp (m := m₄) r₄ hF (by omega) (by omega) []
  refine ⟨s₅, m₄, by rw [pushSeq, h₁, h₂, h₃, h₄, h₅]; rfl, by rw [r₅]; congr 1,
    fun r hr => by rw [k₅ r hr, k₄ r hr, k₃ r hr, k₂ r hr, k₁ r hr], ?_,
    o₄.1.trans (o₃.1.trans (o₂.1.trans o₁.1)), fun x hx => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact ((w₁.of_writesOnly o₂ (by omega)).of_writesOnly o₃ (by omega)).of_writesOnly o₄ (by omega)
    · rw [← k₁ .rbx (by decide)]
      have := (w₂.of_writesOnly o₃ (by omega)).of_writesOnly o₄ (by omega)
      rwa [show e - 8 - 8 = e - 16 by omega] at this
    · rw [← k₁ .r12 (by decide), ← k₂ .r12 (by decide)]
      have := w₃.of_writesOnly o₄ (by omega)
      rwa [show e - 8 - 8 - 8 = e - 24 by omega] at this
    · rw [← k₁ .r13 (by decide), ← k₂ .r13 (by decide), ← k₃ .r13 (by decide)]
      rwa [show e - 8 - 8 - 8 - 8 = e - 32 by omega] at w₄
  · rw [o₄.2 x (by omega), o₃.2 x (by omega), o₂.2 x (by omega), o₁.2 x (by omega)]

end

theorem run_check3 (c : State) (m : Memory) {e lo : Nat} (ns : Nat)
    (hrsp : c.read .rsp = BitVec.ofNat 64 e) (h14 : c.read .r14 = BitVec.ofNat 64 lo) (hle : lo ≤ e)
    (he : e < 2 ^ 64) (hneed : need ns < 2 ^ 31) :
    ∃ c', runSeq [.mov .q (.reg .r11) .rsp, .alu .q .sub (.reg .r11) .r14,
        .aluI .q .cmp (.reg .r11) (BitVec.ofNat 32 (need ns))] c m = some (c', m) ∧
      (∀ r, r ≠ .r11 → c'.read r = c.read r) ∧
      c'.flags = Ext.subFlagsN (BitVec.ofNat 64 (e - lo)) (BitVec.ofNat 64 (need ns)) := by
  rw [runSeq_cons_of (exec_mov_q _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (exec_alu_q _ _ _ _ _ (by decide)) (by intro h; cases h) rfl,
    runSeq_cons_of (exec_cmpI_q _ _ _ _) (by intro h; cases h) rfl]
  refine ⟨_, rfl, fun r hr => by simp [State.read_write_other _ _ _ _ hr], ?_⟩
  have e1 : (BitVec.ofNat 64 e - BitVec.ofNat 64 lo : BitVec 64) = BitVec.ofNat 64 (e - lo) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt (a := lo) (by omega), Nat.mod_eq_of_lt (a := e - lo) (by omega)]
    omega
  simp [State.read_write_other _ _ _ _ (show Reg.r14 ≠ .r11 by decide), hrsp, h14,
    Ext.AluOp.resultN, e1, signExtend_ofNat32 hneed]

end Silmaril.X86.Backend
