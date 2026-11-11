module

public import Silmaril.Wasm.Auto.Rules.Defs
public import Silmaril.Wasm.Auto.EGraph.Thms
import Mathlib.Tactic.Ring

/-! # Soundness of the rewrite library

Every schema of `Silmaril.Wasm.Auto.Rules.schemas` is sound at `i32` and `i64`. A rule is
proved over abstract operand values: each pattern variable holds a trap (`none`) or an
integer of its type, and after splitting on these cases the goal is a `BitVec` identity,
closed by `simp`, `ring`, `ac_rfl` or `bv_omega` (no SAT solving, no compiled evaluation).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Rules

open Silmaril.Wasm.Auto.Rules
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

theorem typed_cases {t : IntType} {o : Option Val} (h : TypedV t o) :
    o = none ∨ ∃ x, o = some (intVal t x) := by
  cases o with
  | none => exact .inl rfl
  | some v =>
    obtain ⟨x, rfl⟩ := h v rfl
    exact .inr ⟨x, rfl⟩

/-- The variable hypothesis at one variable. -/
theorem typed_at {ρ : Nat → Option Val} {vs : List (IntType × Nat)}
    (h : ∀ tn ∈ vs, TypedV tn.1 (ρ tn.2)) {t : IntType} {n : Nat} (hm : (t, n) ∈ vs) :
    ρ n = none ∨ ∃ x, ρ n = some (intVal t x) :=
  typed_cases (h (t, n) hm)

theorem bool32_toNat_lt (b : Bool) : (bool32 b).toNat < 2 := by
  cases b <;> decide

@[simp] theorem intVal_inj {t : IntType} {x y : BitVec t.width} :
    intVal t x = intVal t y ↔ x = y := by
  constructor
  · intro h; cases t <;> cases h <;> rfl
  · rintro rfl; rfl

/-! ## `BitVec` facts the rules need -/

theorem rotateLeft_zero' {w : Nat} (x : BitVec w) : x.rotateLeft 0 = x := by
  simp [BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.ushiftRight_eq_zero]

theorem rotateRight_zero' {w : Nat} (x : BitVec w) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem beq_comm' {w : Nat} (x y : BitVec w) : (x == y) = (y == x) := by
  by_cases h : x = y
  · simp [h]
  · have h' : y ≠ x := Ne.symm h
    simp [h, h']

theorem bne_comm' {w : Nat} (x y : BitVec w) : (x != y) = (y != x) := by
  simp only [bne, beq_comm' x y]

theorem bool32_beq_zero (b : Bool) : (bool32 b == 0) = !b := by cases b <;> rfl

theorem bool32_bne_zero (b : Bool) : (bool32 b != 0) = b := by cases b <;> rfl

theorem asInt_i32 (x : BitVec 32) :
    asInt .i32 (Val.i32 x) = (some x : Option (BitVec IntType.i32.width)) := rfl

theorem asInt_intVal_i32 (x : BitVec 32) :
    asInt .i32 (intVal .i32 x) = (some x : Option (BitVec IntType.i32.width)) := rfl

theorem mul_two_shl_i32 (x : BitVec IntType.i32.width) :
    x * 2#IntType.i32.width = x <<< ((1#IntType.i32.width).toNat % IntType.i32.width) := by
  change BitVec 32 at x
  show x * 2#32 = x <<< 1
  bv_omega

theorem mul_two_shl_i64 (x : BitVec IntType.i64.width) :
    x * 2#IntType.i64.width = x <<< ((1#IntType.i64.width).toNat % IntType.i64.width) := by
  change BitVec 64 at x
  show x * 2#64 = x <<< 1
  bv_omega

theorem mul_ones_i32 (x : BitVec IntType.i32.width) :
    x * BitVec.ofNat IntType.i32.width (ones .i32) = 0#IntType.i32.width - x := by
  change BitVec 32 at x
  show x * 4294967295#32 = 0#32 - x
  bv_omega

theorem mul_ones_i64 (x : BitVec IntType.i64.width) :
    x * BitVec.ofNat IntType.i64.width (ones .i64) = 0#IntType.i64.width - x := by
  change BitVec 64 at x
  show x * 18446744073709551615#64 = 0#64 - x
  bv_omega

theorem width_ne_zero (t : IntType) : t.width ≠ 0 := by cases t <;> decide

theorem one_ne_neg_one (t : IntType) : ¬ (1#t.width = -1#t.width) := by cases t <;> decide

theorem ones_eq (t : IntType) : BitVec.ofNat t.width (ones t) = BitVec.allOnes t.width := by
  cases t <;> decide

theorem intBinOp_divu_one (t : IntType) (x : BitVec t.width) :
    intBinOp t (.div .unsigned) x (BitVec.ofNat _ 1) = .ok x := by
  simp [intBinOp, width_ne_zero]

theorem intBinOp_divs_one (t : IntType) (x : BitVec t.width) :
    intBinOp t (.div .signed) x (BitVec.ofNat _ 1) = .ok x := by
  simp [intBinOp, width_ne_zero, one_ne_neg_one]

theorem intBinOp_remu_one (t : IntType) (x : BitVec t.width) :
    intBinOp t (.rem .unsigned) x (BitVec.ofNat _ 1) = .ok 0 := by
  simp [intBinOp, width_ne_zero]

theorem intBinOp_or_ones (t : IntType) (x : BitVec t.width) :
    intBinOp t .or x (BitVec.ofNat _ (ones t)) = .ok (BitVec.ofNat _ (ones t)) := by
  simp [intBinOp, ones_eq]

/-- `eqz (eqz x)` is `x ≠ 0`, on optional values. -/
theorem testV_testV {t : IntType} {o : Option Val} (h : TypedV t o) :
    testV .i32 (testV t o) = relV t .ne o (some (intVal t (BitVec.ofNat _ 0))) := by
  rcases typed_cases h with rfl | ⟨x, rfl⟩
  · rfl
  · have hb : intTestOp .i32 .eqz (intTestOp t .eqz x) = intRelOp t .ne x (BitVec.ofNat _ 0) := by
      show bool32 (bool32 (x == 0) == 0) = bool32 (!(x == 0))
      cases x == 0 <;> rfl
    cases t <;> exact congrArg (some ∘ Val.i32) hb

/-- `eqz x ≠ 0` is `eqz x`, on optional values. -/
theorem relV_ne_testV {t : IntType} {o : Option Val} (h : TypedV t o) :
    relV .i32 .ne (testV t o) (some (intVal .i32 (BitVec.ofNat _ 0))) = testV t o := by
  rcases typed_cases h with rfl | ⟨x, rfl⟩
  · rfl
  · have hb : intRelOp .i32 .ne (intTestOp t .eqz x) (BitVec.ofNat _ 0) = intTestOp t .eqz x := by
      show bool32 (bool32 (x == 0) != 0) = bool32 (x == 0)
      cases x == 0 <;> rfl
    cases t <;> exact congrArg (some ∘ Val.i32) hb

/-- Close a rule's `BitVec` side condition. -/
macro "rule_close" : tactic => `(tactic| first
  | exact mul_two_shl_i32 _
  | exact mul_two_shl_i64 _
  | rfl
  | (simp; done)
  | (simp [bool32]; done)
  | (simp [bool32] <;> rfl)
  | (simp only [BitVec.ofNat_eq_ofNat]; done)
  | (rw [beq_comm']; done)
  | (rw [bne_comm']; done)
  | (simp only [← BitVec.ofNat_eq_ofNat] at *; ring)
  | ac_rfl
  | ring
  | bv_omega
  | (simp only [IntType.width] at *; bv_omega))

/-- Prove a rule at a concrete type: split every pattern variable into a trap or an
integer, evaluate both sides; `rule_close` then closes the `BitVec` identity. -/
macro "rule_split" : tactic => `(tactic| (
  intro ρ h _ht
  dsimp only
  simp only [Pat.vars, List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  repeat' (obtain ⟨hh, h⟩ := h; rcases typed_cases hh with hh | ⟨_, hh⟩)
  all_goals try rcases typed_cases h with h | ⟨_, h⟩
  all_goals
    simp_all only [Pat.eval, unV, testV, binV, relV, Option.bind_none, Option.bind_some,
      Option.map_none, Option.map_some, asInt_intVal, intBinOp, intRelOp, intTestOp,
      Option.some.injEq, intVal_inj, imp_self, implies_true, forall_eq', reduceCtorEq,
      asInt_i32, i32_eq_intVal, rotateLeft_zero', rotateRight_zero', bool32_beq_zero,
      bool32_bne_zero, asInt_intVal_i32, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mod,
      BitVec.add_zero]))

/-- `rule_split`, then `rule_close` on what is left. -/
macro "rule_tac" : tactic => `(tactic| (rule_split <;> rule_close))

/-- The same for a rule whose only variable is the total variable `0`. -/
macro "rule_tac_t" : tactic => `(tactic| (
  intro ρ _ ht
  obtain ⟨_, h0⟩ := ht _ (List.mem_append_left _ List.mem_cons_self)
  dsimp only
  simp only [Pat.eval, unV, testV, binV, relV, Option.bind_none, Option.bind_some,
    Option.map_none, Option.map_some, asInt_intVal, intBinOp, intRelOp, intTestOp,
    Option.some.injEq, intVal_inj, imp_self, implies_true, forall_eq', reduceCtorEq,
    asInt_i32, i32_eq_intVal, asInt_intVal_i32, BitVec.toNat_ofNat, Nat.zero_mod,
    BitVec.add_zero, h0]
  all_goals rule_close))

set_option linter.unusedSimpArgs false

theorem addComm_sound (t : IntType) : (addComm t).Sound := by
  unfold addComm; cases t <;> rule_tac

theorem addAssoc_sound (t : IntType) : (addAssoc t).Sound := by
  unfold addAssoc; cases t <;> rule_tac

theorem mulComm_sound (t : IntType) : (mulComm t).Sound := by
  unfold mulComm; cases t <;> rule_tac

theorem mulAssoc_sound (t : IntType) : (mulAssoc t).Sound := by
  unfold mulAssoc; cases t <;> rule_tac

theorem andComm_sound (t : IntType) : (andComm t).Sound := by
  unfold andComm; cases t <;> rule_tac

theorem andAssoc_sound (t : IntType) : (andAssoc t).Sound := by
  unfold andAssoc; cases t <;> rule_tac

theorem orComm_sound (t : IntType) : (orComm t).Sound := by
  unfold orComm; cases t <;> rule_tac

theorem orAssoc_sound (t : IntType) : (orAssoc t).Sound := by
  unfold orAssoc; cases t <;> rule_tac

theorem xorComm_sound (t : IntType) : (xorComm t).Sound := by
  unfold xorComm; cases t <;> rule_tac

theorem xorAssoc_sound (t : IntType) : (xorAssoc t).Sound := by
  unfold xorAssoc; cases t <;> rule_tac

theorem addZero_sound (t : IntType) : (addZero t).Sound := by
  unfold addZero; cases t <;> rule_tac

theorem subZero_sound (t : IntType) : (subZero t).Sound := by
  unfold subZero; cases t <;> rule_tac

theorem mulOne_sound (t : IntType) : (mulOne t).Sound := by
  unfold mulOne; cases t <;> rule_tac

theorem orZero_sound (t : IntType) : (orZero t).Sound := by
  unfold orZero; cases t <;> rule_tac

theorem xorZero_sound (t : IntType) : (xorZero t).Sound := by
  unfold xorZero; cases t <;> rule_tac

theorem andOnes_sound (t : IntType) : (andOnes t).Sound := by
  unfold andOnes; cases t <;> rule_tac

theorem shlZero_sound (t : IntType) : (shlZero t).Sound := by
  unfold shlZero; cases t <;> rule_tac

theorem shruZero_sound (t : IntType) : (shruZero t).Sound := by
  unfold shruZero; cases t <;> rule_tac

theorem shrsZero_sound (t : IntType) : (shrsZero t).Sound := by
  unfold shrsZero; cases t <;> rule_tac

theorem rotlZero_sound (t : IntType) : (rotlZero t).Sound := by
  unfold rotlZero; cases t <;> rule_tac

theorem rotrZero_sound (t : IntType) : (rotrZero t).Sound := by
  unfold rotrZero; cases t <;> rule_tac

theorem mulAddDistrib_sound (t : IntType) : (mulAddDistrib t).Sound := by
  unfold mulAddDistrib; cases t <;> rule_tac

theorem subAddNeg_sound (t : IntType) : (subAddNeg t).Sound := by
  unfold subAddNeg; cases t <;> rule_tac

theorem negNeg_sound (t : IntType) : (negNeg t).Sound := by
  unfold negNeg; cases t <;> rule_tac

theorem addSelf_sound (t : IntType) : (addSelf t).Sound := by
  unfold addSelf; cases t <;> rule_tac

theorem mulTwoShl_sound (t : IntType) : (mulTwoShl t).Sound := by
  unfold mulTwoShl; cases t <;> rule_tac

theorem andSelf_sound (t : IntType) : (andSelf t).Sound := by
  unfold andSelf; cases t <;> rule_tac

theorem orSelf_sound (t : IntType) : (orSelf t).Sound := by
  unfold orSelf; cases t <;> rule_tac

theorem mulNegOne_sound (t : IntType) : (mulNegOne t).Sound := by
  unfold mulNegOne; cases t
  · rule_split; exact mul_ones_i32 _
  · rule_split; exact mul_ones_i64 _

theorem addSubAssoc_sound (t : IntType) : (addSubAssoc t).Sound := by
  unfold addSubAssoc; cases t <;> rule_tac

theorem eqzEq_sound (t : IntType) : (eqzEq t).Sound := by
  unfold eqzEq; cases t <;> rule_tac

theorem eqzEqz_sound (t : IntType) : (eqzEqz t).Sound := by
  intro ρ h _
  exact testV_testV (h (t, 0) (by simp [eqzEqz, Pat.vars]))

theorem eqzNeZero_sound (t : IntType) : (eqzNeZero t).Sound := by
  intro ρ h _
  exact relV_ne_testV (h (t, 0) (by simp [eqzNeZero, Pat.vars]))

theorem eqComm_sound (t : IntType) : (Silmaril.Wasm.Auto.Rules.eqComm t).Sound := by
  unfold Silmaril.Wasm.Auto.Rules.eqComm; cases t <;> rule_tac

theorem neComm_sound (t : IntType) : (neComm t).Sound := by
  unfold neComm; cases t <;> rule_tac

theorem ltsGts_sound (t : IntType) : (ltsGts t).Sound := by
  unfold ltsGts; cases t <;> rule_tac

theorem ltuGtu_sound (t : IntType) : (ltuGtu t).Sound := by
  unfold ltuGtu; cases t <;> rule_tac

theorem lesGes_sound (t : IntType) : (lesGes t).Sound := by
  unfold lesGes; cases t <;> rule_tac

theorem leuGeu_sound (t : IntType) : (leuGeu t).Sound := by
  unfold leuGeu; cases t <;> rule_tac

theorem subSelf_sound (t : IntType) : (subSelf t).Sound := by
  unfold subSelf; cases t <;> rule_tac

theorem xorSelf_sound (t : IntType) : (xorSelf t).Sound := by
  unfold xorSelf; cases t <;> rule_tac

theorem mulZero_sound (t : IntType) : (mulZero t).Sound := by
  unfold mulZero; cases t <;> rule_tac

theorem andZero_sound (t : IntType) : (andZero t).Sound := by
  unfold andZero; cases t <;> rule_tac

theorem addSubCancel_sound (t : IntType) : (addSubCancel t).Sound := by
  unfold addSubCancel; cases t <;> rule_tac

theorem divUOne_sound (t : IntType) : (divUOne t).Sound := by
  intro ρ h _
  rcases typed_cases (h (t, 0) (by simp [divUOne, Pat.vars])) with h0 | ⟨x, h0⟩
  · simp [divUOne, Pat.eval, binV, h0]
  · simp [divUOne, Pat.eval, binV, h0, intBinOp_divu_one]

theorem divSOne_sound (t : IntType) : (divSOne t).Sound := by
  intro ρ h _
  rcases typed_cases (h (t, 0) (by simp [divSOne, Pat.vars])) with h0 | ⟨x, h0⟩
  · simp [divSOne, Pat.eval, binV, h0]
  · simp [divSOne, Pat.eval, binV, h0, intBinOp_divs_one]

theorem shlWidth_sound (t : IntType) : (shlWidth t).Sound := by
  unfold shlWidth; cases t <;> rule_tac

theorem shruWidth_sound (t : IntType) : (shruWidth t).Sound := by
  unfold shruWidth; cases t <;> rule_tac

theorem shrsWidth_sound (t : IntType) : (shrsWidth t).Sound := by
  unfold shrsWidth; cases t <;> rule_tac

theorem negMul_sound (t : IntType) : (negMul t).Sound := by
  unfold negMul; cases t <;> rule_tac

theorem subSelfT_sound (t : IntType) : (subSelfT t).Sound := by
  unfold subSelfT; cases t <;> rule_tac_t

theorem xorSelfT_sound (t : IntType) : (xorSelfT t).Sound := by
  unfold xorSelfT; cases t <;> rule_tac_t

theorem mulZeroT_sound (t : IntType) : (mulZeroT t).Sound := by
  unfold mulZeroT; cases t <;> rule_tac_t

theorem andZeroT_sound (t : IntType) : (andZeroT t).Sound := by
  unfold andZeroT; cases t <;> rule_tac_t

theorem orOnesT_sound (t : IntType) : (orOnesT t).Sound := by
  intro ρ _ ht
  obtain ⟨x, h0⟩ := ht (t, 0) (by simp [orOnesT, Pat.tvars])
  simp [orOnesT, Pat.eval, binV, h0, intBinOp_or_ones]

theorem zeroShlT_sound (t : IntType) : (zeroShlT t).Sound := by
  unfold zeroShlT; cases t <;> rule_tac_t

theorem zeroShruT_sound (t : IntType) : (zeroShruT t).Sound := by
  unfold zeroShruT; cases t <;> rule_tac_t

theorem zeroShrsT_sound (t : IntType) : (zeroShrsT t).Sound := by
  unfold zeroShrsT; cases t <;> rule_tac_t

theorem remUOneT_sound (t : IntType) : (remUOneT t).Sound := by
  intro ρ _ ht
  obtain ⟨x, h0⟩ := ht (t, 0) (by simp [remUOneT, Pat.tvars])
  simp [remUOneT, Pat.eval, binV, h0, intBinOp_remu_one]

theorem eqSelfT_sound (t : IntType) : (eqSelfT t).Sound := by
  unfold eqSelfT; cases t <;> rule_tac_t

theorem neSelfT_sound (t : IntType) : (neSelfT t).Sound := by
  unfold neSelfT; cases t <;> rule_tac_t

theorem ltsSelfT_sound (t : IntType) : (ltsSelfT t).Sound := by
  unfold ltsSelfT; cases t <;> rule_tac_t

theorem ltuSelfT_sound (t : IntType) : (ltuSelfT t).Sound := by
  unfold ltuSelfT; cases t <;> rule_tac_t

theorem gtsSelfT_sound (t : IntType) : (gtsSelfT t).Sound := by
  unfold gtsSelfT; cases t <;> rule_tac_t

theorem gtuSelfT_sound (t : IntType) : (gtuSelfT t).Sound := by
  unfold gtuSelfT; cases t <;> rule_tac_t

theorem lesSelfT_sound (t : IntType) : (lesSelfT t).Sound := by
  unfold lesSelfT; cases t <;> rule_tac_t

theorem leuSelfT_sound (t : IntType) : (leuSelfT t).Sound := by
  unfold leuSelfT; cases t <;> rule_tac_t

theorem gesSelfT_sound (t : IntType) : (gesSelfT t).Sound := by
  unfold gesSelfT; cases t <;> rule_tac_t

theorem geuSelfT_sound (t : IntType) : (geuSelfT t).Sound := by
  unfold geuSelfT; cases t <;> rule_tac_t

theorem zeroGtuT_sound (t : IntType) : (zeroGtuT t).Sound := by
  unfold zeroGtuT; cases t <;> rule_tac_t

theorem ltuZeroT_sound (t : IntType) : (ltuZeroT t).Sound := by
  unfold ltuZeroT; cases t <;> rule_tac_t

theorem geuZeroT_sound (t : IntType) : (geuZeroT t).Sound := by
  unfold geuZeroT; cases t <;> rule_tac_t

theorem zeroLeuT_sound (t : IntType) : (zeroLeuT t).Sound := by
  unfold zeroLeuT; cases t <;> rule_tac_t

theorem addSubCancelT_sound (t : IntType) : (addSubCancelT t).Sound := by
  intro ρ h ht
  obtain ⟨y, h0⟩ := ht (t, 0) (by simp [addSubCancelT, Pat.tvars])
  rcases typed_cases (h (t, 1) (by simp [addSubCancelT, Pat.vars])) with h1 | ⟨x, h1⟩
  · simp [addSubCancelT, Pat.eval, binV, h0, h1]
  · simp [addSubCancelT, Pat.eval, binV, h0, h1, intBinOp]

/-- **Every schema is sound at every type.** -/
theorem schemas_sound : ∀ sch ∈ schemas, ∀ t, (sch t).Sound := by
  simp only [schemas, List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨
    addComm_sound, addAssoc_sound, mulComm_sound, mulAssoc_sound, andComm_sound,
    andAssoc_sound, orComm_sound, orAssoc_sound, xorComm_sound, xorAssoc_sound,
    addZero_sound, subZero_sound, mulOne_sound, orZero_sound, xorZero_sound, andOnes_sound,
    shlZero_sound, shruZero_sound, shrsZero_sound, rotlZero_sound, rotrZero_sound,
    mulAddDistrib_sound, subAddNeg_sound, negNeg_sound, addSelf_sound, mulTwoShl_sound,
    andSelf_sound, orSelf_sound, mulNegOne_sound, addSubAssoc_sound, eqzEq_sound,
    eqzEqz_sound, eqzNeZero_sound, eqComm_sound, neComm_sound, ltsGts_sound, ltuGtu_sound,
    lesGes_sound, leuGeu_sound, subSelf_sound, xorSelf_sound, mulZero_sound, andZero_sound,
    addSubCancel_sound, divUOne_sound, divSOne_sound, shlWidth_sound, shruWidth_sound,
    shrsWidth_sound, negMul_sound, subSelfT_sound, xorSelfT_sound, mulZeroT_sound,
    andZeroT_sound, orOnesT_sound, zeroShlT_sound, zeroShruT_sound, zeroShrsT_sound,
    remUOneT_sound, eqSelfT_sound, neSelfT_sound, ltsSelfT_sound, ltuSelfT_sound,
    gtsSelfT_sound, gtuSelfT_sound, lesSelfT_sound, leuSelfT_sound, gesSelfT_sound,
    geuSelfT_sound, zeroGtuT_sound, ltuZeroT_sound, geuZeroT_sound, zeroLeuT_sound,
    addSubCancelT_sound, by simp⟩

end Silmaril.Proofs.Wasm.Auto.Rules
