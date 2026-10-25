module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.PureRedex

@[expose] public section

/-! # Soundness, vector family

Preservation of `VectorStep` (a pure family: store and frame unchanged) and
progress for `VectorInstrOk`.

Statement change (progress): `VCONST V128 c` is typed by `VectorInstrOk` but is a
value, not a redex, so it does not reduce. Progress therefore assumes the
instruction is not a value (`(Admin.plain i).val? = none`), as for the numeric
family.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Inversion to the family, the principal type split, and the reduct typing. -/
local macro "vector_base" : tactic => `(tactic| (
  intro C A' tvs it xs₂ B hi hp hf D
  cases hi <;> rename_i hi <;> cases hi
  all_goals
    obtain ⟨e1, e2⟩ := params_split hp (by simp [← hf.length_eq])
    subst e1 e2
    first
      | exact AdminsOk.val_cons (w := .vec _) (.vec _) D
      | exact AdminsOk.val_cons (.num _) D
      | exact AdminsOk.val_cons (w := .num ⟨.int _, _⟩) (.num _) D
      | exact AdminsOk.trap_cons (ResultOk.nil' _) (ResultOk.vec1 _ _) D))

local macro "vector_len" : tactic => `(tactic| (
  intro C it hi
  cases hi <;> rename_i hi <;> cases hi <;> simp))

/-- **Preservation (vector).** A pure redex and its reduct have the same type. -/
theorem VectorStep.preservation {P : Profile} {s : Store H} {f : Frame} {C : Context}
    {is is' : List Admin} {it : InstrType} (_hst : StateOk s f C)
    (hty : AdminsOk s C is it) (h : VectorStep P is is') : AdminsOk s C is' it := by
  cases h with
  | vecUnOp op a =>
    exact AdminsOk.pure_redex (vs := [.vec a]) (i := .vecUnOp op)
      (by vector_len) (by vector_base) hty
  | vecBinOp op a b =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b]) (i := .vecBinOp op)
      (by vector_len) (by vector_base) hty
  | vecTernOp op a b c =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b, .vec c])
      (i := .vecTernOp op) (by vector_len) (by vector_base) hty
  | vecTestOp op a =>
    exact AdminsOk.pure_redex (vs := [.vec a]) (i := .vecTestOp op)
      (by vector_len) (by vector_base) hty
  | vecIntUnOp sh op a =>
    exact AdminsOk.pure_redex (vs := [.vec a]) (i := .vecIntUnOp sh op)
      (by vector_len) (by vector_base) hty
  | @vecFloatUnOp sh op a r _ =>
    exact AdminsOk.pure_redex (vs := [.vec a])
      (i := .vecFloatUnOp sh op) (by vector_len) (by vector_base) hty
  | @vecFloatUnOpTrap sh op a _ =>
    exact AdminsOk.pure_redex (vs := [.vec a])
      (i := .vecFloatUnOp sh op) (by vector_len) (by vector_base) hty
  | vecIntBinOp sh op a b =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecIntBinOp sh op) (by vector_len) (by vector_base) hty
  | @vecFloatBinOp sh op a b r _ =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecFloatBinOp sh op) (by vector_len) (by vector_base) hty
  | @vecFloatBinOpTrap sh op a b _ =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecFloatBinOp sh op) (by vector_len) (by vector_base) hty
  | vecIntTernOp sh op a b c =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b, .vec c])
      (i := .vecIntTernOp sh op) (by vector_len) (by vector_base) hty
  | @vecFloatTernOp sh op a b c r _ =>
    exact AdminsOk.pure_redex
      (vs := [.vec a, .vec b, .vec c]) (i := .vecFloatTernOp sh op)
      (by vector_len) (by vector_base) hty
  | @vecFloatTernOpTrap sh op a b c _ =>
    exact AdminsOk.pure_redex
      (vs := [.vec a, .vec b, .vec c]) (i := .vecFloatTernOp sh op)
      (by vector_len) (by vector_base) hty
  | vecAllTrue sh a =>
    exact AdminsOk.pure_redex (vs := [.vec a]) (i := .vecAllTrue sh)
      (by vector_len) (by vector_base) hty
  | vecIntRelOp sh op a b =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecIntRelOp sh op) (by vector_len) (by vector_base) hty
  | vecFloatRelOp sh op a b =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecFloatRelOp sh op) (by vector_len) (by vector_base) hty
  | vecShiftOp sh op a n =>
    exact AdminsOk.pure_redex (vs := [.vec a, Val.i32 n])
      (i := .vecShiftOp sh op) (by vector_len) (by vector_base) hty
  | vecBitmask sh a =>
    exact AdminsOk.pure_redex (vs := [.vec a]) (i := .vecBitmask sh)
      (by vector_len) (by vector_base) hty
  | vecSwizzle a b =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecSwizzle .swizzle) (by vector_len) (by vector_base) hty
  | vecRelaxedSwizzle a b =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecSwizzle .relaxedSwizzle) (by vector_len) (by vector_base) hty
  | vecShuffle idx a b _ =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecShuffle idx) (by vector_len) (by vector_base) hty
  | vecSplat sh x =>
    exact AdminsOk.pure_redex (vs := [.num ⟨sh.unpacked, x⟩])
      (i := .vecSplat sh) (by vector_len) (by vector_base) hty
  | vecExtractLane sh sx i a _ =>
    exact AdminsOk.pure_redex (vs := [.vec a])
      (i := .vecExtractLane sh sx i) (by vector_len) (by vector_base) hty
  | vecReplaceLane sh i a x _ =>
    exact AdminsOk.pure_redex
      (vs := [.vec a, .num ⟨sh.unpacked, x⟩]) (i := .vecReplaceLane sh i)
      (by vector_len) (by vector_base) hty
  | @vecExtUnOp sh₁ sh₂ op a r _ =>
    exact AdminsOk.pure_redex (vs := [.vec a])
      (i := .vecExtUnOp sh₁ sh₂ op) (by vector_len) (by vector_base) hty
  | @vecExtBinOp sh₁ sh₂ op a b r _ =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecExtBinOp sh₁ sh₂ op) (by vector_len) (by vector_base) hty
  | @vecExtTernOp sh₁ sh₂ op a b c r _ =>
    exact AdminsOk.pure_redex
      (vs := [.vec a, .vec b, .vec c]) (i := .vecExtTernOp sh₁ sh₂ op)
      (by vector_len) (by vector_base) hty
  | @vecNarrow sh₁ sh₂ sx a b r _ =>
    exact AdminsOk.pure_redex (vs := [.vec a, .vec b])
      (i := .vecNarrow sh₁ sh₂ sx) (by vector_len) (by vector_base) hty
  | @vecConvert sh₁ sh₂ op a r _ =>
    exact AdminsOk.pure_redex (vs := [.vec a])
      (i := .vecConvert sh₁ sh₂ op) (by vector_len) (by vector_base) hty

/-- **Progress (vector).** A well-typed instruction of this family, applied to
operands of its parameter types, reduces. `VCONST` is a value (see the module
doc for the added premise `hnv`). -/
theorem VectorInstrOk.progress {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val}
    (_hst : StateOk s f C) (hi : VectorInstrOk C i ⟨t₁, xs, t₂⟩)
    (hvs : List.Forall₂ (ValOk s) vs t₁) (hnv : (Admin.plain i).val? = none) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | vecConst => simp [Admin.val?] at hnv
  | vecUnOp op =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    exact ⟨_, .vector (.vecUnOp op a)⟩
  | vecBinOp op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    exact ⟨_, .vector (.vecBinOp op a b)⟩
  | vecTernOp op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    obtain ⟨c, rfl⟩ := ValOk.vec_inv h3
    exact ⟨_, .vector (.vecTernOp op a b c)⟩
  | vecTestOp op =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    exact ⟨_, .vector (.vecTestOp op a)⟩
  | vecIntUnOp _ =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    exact ⟨_, .vector (.vecIntUnOp _ _ a)⟩
  | vecFloatUnOp sh op =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨r, hr⟩ := VecFloatUnOpRel_nonempty P sh op a
    exact ⟨_, .vector (.vecFloatUnOp hr)⟩
  | vecIntBinOp _ =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    exact ⟨_, .vector (.vecIntBinOp _ _ a b)⟩
  | vecFloatBinOp sh op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    by_cases hr : ∃ r, VecFloatBinOpRel P sh op a b r
    · obtain ⟨r, hr⟩ := hr; exact ⟨_, .vector (.vecFloatBinOp hr)⟩
    · push Not at hr; exact ⟨_, .vector (.vecFloatBinOpTrap hr)⟩
  | vecIntTernOp sh op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    obtain ⟨c, rfl⟩ := ValOk.vec_inv h3
    exact ⟨_, .vector (.vecIntTernOp sh op a b c)⟩
  | vecFloatTernOp sh op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    obtain ⟨c, rfl⟩ := ValOk.vec_inv h3
    by_cases hr : ∃ r, VecFloatTernOpRel P sh op a b c r
    · obtain ⟨r, hr⟩ := hr; exact ⟨_, .vector (.vecFloatTernOp hr)⟩
    · push Not at hr; exact ⟨_, .vector (.vecFloatTernOpTrap hr)⟩
  | vecAllTrue sh =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    exact ⟨_, .vector (.vecAllTrue sh a)⟩
  | vecIntRelOp _ =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    exact ⟨_, .vector (.vecIntRelOp _ _ a b)⟩
  | vecFloatRelOp sh op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    exact ⟨_, .vector (.vecFloatRelOp sh op a b)⟩
  | vecShiftOp sh op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨n, rfl⟩ := ValOk.num_inv h2
    exact ⟨_, .vector (.vecShiftOp sh op a n)⟩
  | vecBitmask sh =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    exact ⟨_, .vector (.vecBitmask sh a)⟩
  | vecSwizzle op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    cases op
    · exact ⟨_, .vector (.vecSwizzle a b)⟩
    · exact ⟨_, .vector (.vecRelaxedSwizzle a b)⟩
  | vecShuffle _ hidx =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    exact ⟨_, .vector (.vecShuffle _ a b hidx)⟩
  | vecSplat sh =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    exact ⟨_, .vector (.vecSplat sh x)⟩
  | vecExtractLane hi _ =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    exact ⟨_, .vector (.vecExtractLane _ _ _ a hi)⟩
  | vecReplaceLane hi =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨x, rfl⟩ := ValOk.num_inv h2
    exact ⟨_, .vector (.vecReplaceLane _ _ a x hi)⟩
  | @vecExtUnOp sh₁ sh₂ op _ =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨r, hr⟩ := VecExtUnOpRel_nonempty sh₁ sh₂ op a
    exact ⟨_, .vector (.vecExtUnOp hr)⟩
  | @vecExtBinOp sh₁ sh₂ op _ =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    obtain ⟨r, hr⟩ := VecExtBinOpRel_nonempty P sh₁ sh₂ op a b
    exact ⟨_, .vector (.vecExtBinOp hr)⟩
  | @vecExtTernOp sh₁ sh₂ op _ =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    obtain ⟨c, rfl⟩ := ValOk.vec_inv h3
    obtain ⟨r, hr⟩ := VecExtTernOpRel_nonempty P sh₁ sh₂ op a b c
    exact ⟨_, .vector (.vecExtTernOp hr)⟩
  | @vecNarrow sh₁ sh₂ sx _ =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨b, rfl⟩ := ValOk.vec_inv h2
    obtain ⟨r, hr⟩ := VecNarrowRel_nonempty sh₁ sh₂ sx a b
    exact ⟨_, .vector (.vecNarrow hr)⟩
  | vecConvert h =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨a, rfl⟩ := ValOk.vec_inv h1
    obtain ⟨r, hr⟩ := VecConvertRel_nonempty P h a
    exact ⟨_, .vector (.vecConvert hr)⟩

end Silmaril.Wasm.Execution.Core
