module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneFNum

/-!
# The float vector `vbinop` and `vrelop` forward, under `VecNumAgree`

**`fwd_vecFloatBinOp20V`** (rule 36) and **`fwd_vecFloatRelOp20V`** (rule 40): every V2 pure step
from `v128.const c₁; v128.const c₂; sh.op` at a float shape is a firing of the rule in the
corrected script, from the image of the source to the image of V2's successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_four)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (famForm_vbinop famForm_vrelop findTyp_fam_simEnv20V)

variable {B : Builtins}

/-- The scope of rules 36 and 40. -/
abbrev scope2 (opx : IL.Id) (c₁ c₂ : BitVec 128) (sh op c : Value) : List (IL.Id × Value) :=
  [("c_1", pctV c₁.toNat), ("c_2", pctV c₂.toNat), ("sh", sh), (opx, op), ("c", c)]

/-- **Rule 36 fires** at a float shape, to every result of `$vbinop_` that V2 permits. -/
theorem fires_vbinopFloat {P : Profile} (hA : VecNumAgree (simEnv20V B) P) (s : FloatShape)
    (op : V2.VecFloatBinOp) (c₁ c₂ r : BitVec 128) (hr : VecFloatBinOpResult P s op c₁ c₂ r) :
    Fires (simEnv20V B) "Step_pure" 36 (.tuple [
      .list [adminToV (vconst c₁), adminToV (vconst c₂),
        .case "VBINOP" (.tuple [shapeV (.float s), vecFloatBinOpV op])],
      .list [adminToV (vconst r)]]) := by
  let σ := scope2 "vbinop" c₁ c₂ (shapeV (.float s)) (vecFloatBinOpV op) (pctV r.toNat)
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (pctV c₂.toNat) := rfl
  have fsh : (VarEnv.empty.bindVals σ).findVal? "sh" = some (shapeV (.float s)) := rfl
  have fop : (VarEnv.empty.bindVals σ).findVal? "vbinop" = some (vecFloatBinOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  obtain ⟨o, ho, hop⟩ := vecFloatBinOpV_mem op
  have hty : HasTyp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.varT "vbinop_" [.expA (.varE "sh")]) (vecFloatBinOpV op) := by
    rw [hop]
    exact hasTyp_famFloat famForm_vbinop (findTyp_fam_simEnv20V B).2.1 fsh ho
      (by decide)
  have hq : QuantsOk (simEnv20V B) (VarEnv.empty.bindVals σ)
      (match vbinopRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons f₁ (VecFix.typedV_vecV128_20V c₁ _ hρ) (QuantsOk.cons f₂
      (VecFix.typedV_vecV128_20V c₂ _ hρ) (QuantsOk.cons fsh (VecFix.typedV_shape20V _ _ hρ)
        (QuantsOk.cons fop hty (QuantsOk.cons fc (VecFix.typedV_vecV128_20V r _ hρ)
          QuantsOk.nil))))
  obtain ⟨vs, happ, hvs⟩ := hA.floatBin s op c₁ c₂
  have hcall : EvalExp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.callE "vbinop_" [.expA (.varE "sh"), .expA (.varE "vbinop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) (.list vs) :=
    evalExp_callE_iff.2 ((applies_iff_callDef (findDef_none_bindVals σ _)
      (evalArgs_four fsh fop f₁ f₂)).1 happ)
  have hm : memValue (pctV r.toNat) (.list vs) = .ok (.bool true) :=
    Pure.memValue_list_iff.2 ((hvs _).2 ⟨r, hr, rfl⟩)
  refine Pure.fires_of_ruleAt (hasRuleAt_vbinop20V B) σ hq
    (evalExp_tup2 (Pure.evalExp_list3 (evalExp_vconst f₁) (evalExp_vconst f₂)
      (evalExp_pairV fsh fop)) (evalExp_list1 (evalExp_vconst fc))) ?_
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (evalExp_memE_iff.2 ⟨_, _, evalExp_var fc, hcall, hm⟩)

/-- **Rule 40 fires** at a float shape, to the comparison V2 computes. -/
theorem fires_vrelopFloat {P : Profile} (hA : VecNumAgree (simEnv20V B) P) (s : FloatShape)
    (op : FloatRelOp) (c₁ c₂ : BitVec 128) :
    Fires (simEnv20V B) "Step_pure" 40 (.tuple [
      .list [adminToV (vconst c₁), adminToV (vconst c₂),
        .case "VRELOP" (.tuple [shapeV (.float s), floatRelOpV op])],
      .list [adminToV (vconst (VecFloatRelOp s op c₁ c₂))]]) := by
  let r := VecFloatRelOp s op c₁ c₂
  let σ := scope2 "vrelop" c₁ c₂ (shapeV (.float s)) (floatRelOpV op) (pctV r.toNat)
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (pctV c₂.toNat) := rfl
  have fsh : (VarEnv.empty.bindVals σ).findVal? "sh" = some (shapeV (.float s)) := rfl
  have fop : (VarEnv.empty.bindVals σ).findVal? "vrelop" = some (floatRelOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  obtain ⟨o, ho, hop⟩ := floatRelOpV_mem op
  have hty : HasTyp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.varT "vrelop_" [.expA (.varE "sh")]) (floatRelOpV op) := by
    rw [hop]
    exact hasTyp_famFloat famForm_vrelop (findTyp_fam_simEnv20V B).2.2 fsh ho
      (by decide)
  have hq : QuantsOk (simEnv20V B) (VarEnv.empty.bindVals σ)
      (match vrelopRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons f₁ (VecFix.typedV_vecV128_20V c₁ _ hρ) (QuantsOk.cons f₂
      (VecFix.typedV_vecV128_20V c₂ _ hρ) (QuantsOk.cons fsh (VecFix.typedV_shape20V _ _ hρ)
        (QuantsOk.cons fop hty (QuantsOk.cons fc (VecFix.typedV_vecV128_20V r _ hρ)
          QuantsOk.nil))))
  have hcall : EvalExp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.callE "vrelop_" [.expA (.varE "sh"), .expA (.varE "vrelop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) (pctV r.toNat) :=
    evalExp_callE_iff.2 ((applies_iff_callDef (findDef_none_bindVals σ _)
      (evalArgs_four fsh fop f₁ f₂)).1 (hA.floatRel s op c₁ c₂))
  refine Pure.fires_of_ruleAt (hasRuleAt_vrelop20V B) σ hq
    (evalExp_tup2 (Pure.evalExp_list3 (evalExp_vconst f₁) (evalExp_vconst f₂)
      (evalExp_pairV fsh fop)) (evalExp_list1 (evalExp_vconst fc))) ?_
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (Whole.evalExp_eqTrue hcall (evalExp_var fc))

/-- The V2 steps from `v128.const c₁; v128.const c₂; sh.op` at a float shape: the value step
only. -/
theorem pureStep_vecFloatBinOp_inv {P : Profile} {s : FloatShape} {op : V2.VecFloatBinOp}
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)] code') :
    ∃ r, VecFloatBinOpResult P s op c₁ c₂ r ∧ code' = [vconst r] := by
  generalize hl : [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecFloatBinOp s op)] = l at h
  cases h with
  | vecFloatBinOp hr =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecFloatBinOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, hr, rfl⟩
  | vecFloatBinOpTrap hn =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecFloatBinOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    obtain ⟨r, hr⟩ := VecFloatBinOpResult_nonempty P s op c₁ c₂
    exact absurd hr (hn r)
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecFloatBinOp s op)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- The only V2 step from `v128.const c₁; v128.const c₂; sh.relop` at a float shape. -/
theorem pureStep_vecFloatRelOp_inv {P : Profile} {s : FloatShape} {op : FloatRelOp}
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)] code') :
    code' = [vconst (VecFloatRelOp s op c₁ c₂)] := by
  generalize hl : [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecFloatRelOp s op)] = l at h
  cases h with
  | vecFloatRelOp =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecFloatRelOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    rfl
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecFloatRelOp s op)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- **The float `vbinop`s, forward** (rule 36 of the corrected script). -/
theorem fwd_vecFloatBinOp20V {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : FloatShape}
    {op : V2.VecFloatBinOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)] code') :
    Fires (simEnv20V B) "Step_pure" 36 (.tuple [.list (adminsToV [vconst c₁, vconst c₂,
      .plain (.vecFloatBinOp s op)]), .list (adminsToV code')]) := by
  obtain ⟨r, hr, rfl⟩ := pureStep_vecFloatBinOp_inv h
  exact fires_vbinopFloat hA s op c₁ c₂ r hr

/-- **The float `vrelop`s, forward** (rule 40 of the corrected script). -/
theorem fwd_vecFloatRelOp20V {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : FloatShape}
    {op : FloatRelOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)] code') :
    Fires (simEnv20V B) "Step_pure" 40 (.tuple [.list (adminsToV [vconst c₁, vconst c₂,
      .plain (.vecFloatRelOp s op)]), .list (adminsToV code')]) := by
  rw [pureStep_vecFloatRelOp_inv h]
  exact fires_vrelopFloat hA s op c₁ c₂

end Silmaril.Wasm.SpecTec.Sim20.VecLane
