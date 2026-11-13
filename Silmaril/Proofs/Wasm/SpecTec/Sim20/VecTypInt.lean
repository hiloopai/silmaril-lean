module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypFam

/-!
# The integer vector operators forward, under `VecNumAgree`

The integer counterparts 's `VecLane.fires_vunopFloat` and its siblings. The rules
`vunop` (34), `vbinop-val` (36) and `vrelop` (40) quantify the operator at the family, whose
integer instance has premises; the family typing is read off the typed instruction
(`hasTyp_famOf_typedA`), so each statement assumes the instruction typed in `simEnv20V B`.

* **`fires_vunopInt`**, `fires_vbinopInt`, `fires_vrelopInt`: the rule fires at an integer shape,
  to every result V2 permits (to V2's comparison for `vrelop`);
* `pureStep_vecIntUnOp_inv`, …: the V2 steps from those sources are the value steps only (the
  trap steps are vacuous: the integer results are functions);
* **`fwd_vecIntUnOp20V`**, `fwd_vecIntBinOp20V`, `fwd_vecIntRelOp20V`: every V2 pure step is a
  firing of the rule.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly QuantsOk evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecLane (VecNumAgree vunopRule vbinopRule vrelopRule
  hasRuleAt_vunop20V hasRuleAt_vbinop20V hasRuleAt_vrelop20V evalExp_vconst evalExp_pairV
  findDef_none_bindVals scope2)

variable {B : Builtins}

/-! ## The rules fire -/

/-- **Rule 34 fires** at an integer shape, to every result of `$vunop_` that V2 permits. -/
theorem fires_vunopInt {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : IntShape}
    {op : VecIntUnOp}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntUnOp s op)))
    (c r : BitVec 128) (hr : VecIntUnOpResult s op c r) :
    Fires (simEnv20V B) "Step_pure" 34 (.tuple [
      .list [adminToV (vconst c), .case "VUNOP" (.tuple [shapeV (.int s), vecIntUnOpV op])],
      .list [adminToV (vconst r)]]) := by
  let σ : List (IL.Id × Value) := [("c_1", pctV c.toNat), ("sh", shapeV (.int s)),
    ("vunop", vecIntUnOpV op), ("c", pctV r.toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c.toNat) := rfl
  have fsh : (VarEnv.empty.bindVals σ).findVal? "sh" = some (shapeV (.int s)) := rfl
  have fop : (VarEnv.empty.bindVals σ).findVal? "vunop" = some (vecIntUnOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  have hty : HasTyp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.varT "vunop_" [.expA (.varE "sh")]) (vecIntUnOpV op) :=
    hasTyp_famOf_typedA (Or.inl ⟨rfl, rfl⟩) hi fsh
  have hq : QuantsOk (simEnv20V B) (VarEnv.empty.bindVals σ)
      (match vunopRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons f₁ (VecFix.typedV_vecV128_20V c _ hρ) (QuantsOk.cons fsh
      (VecFix.typedV_shape20V _ _ hρ) (QuantsOk.cons fop hty
        (QuantsOk.cons fc (VecFix.typedV_vecV128_20V r _ hρ) QuantsOk.nil)))
  obtain ⟨vs, happ, hvs⟩ := hA.intUn s op c
  have hcall : EvalExp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.callE "vunop_" [.expA (.varE "sh"), .expA (.varE "vunop"), .expA (.varE "c_1")])
      (.list vs) :=
    evalExp_callE_iff.2 ((applies_iff_callDef (findDef_none_bindVals σ _)
      (evalArgs_three fsh fop f₁)).1 happ)
  have hm : memValue (pctV r.toNat) (.list vs) = .ok (.bool true) :=
    Pure.memValue_list_iff.2 ((hvs _).2 ⟨r, hr, rfl⟩)
  refine Pure.fires_of_ruleAt (hasRuleAt_vunop20V B) σ hq
    (evalExp_tup2 (Pure.evalExp_list2 (evalExp_vconst f₁) (evalExp_pairV fsh fop))
      (evalExp_list1 (evalExp_vconst fc))) ?_
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (evalExp_memE_iff.2 ⟨_, _, evalExp_var fc, hcall, hm⟩)

/-- **Rule 36 fires** at an integer shape, to every result of `$vbinop_` that V2 permits. -/
theorem fires_vbinopInt {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : IntShape}
    {op : V2.VecIntBinOp}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntBinOp s op)))
    (c₁ c₂ r : BitVec 128) (hr : VecIntBinOpResult P s op c₁ c₂ r) :
    Fires (simEnv20V B) "Step_pure" 36 (.tuple [
      .list [adminToV (vconst c₁), adminToV (vconst c₂),
        .case "VBINOP" (.tuple [shapeV (.int s), vecIntBinOpV op])],
      .list [adminToV (vconst r)]]) := by
  let σ := scope2 "vbinop" c₁ c₂ (shapeV (.int s)) (vecIntBinOpV op) (pctV r.toNat)
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (pctV c₂.toNat) := rfl
  have fsh : (VarEnv.empty.bindVals σ).findVal? "sh" = some (shapeV (.int s)) := rfl
  have fop : (VarEnv.empty.bindVals σ).findVal? "vbinop" = some (vecIntBinOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  have hty : HasTyp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.varT "vbinop_" [.expA (.varE "sh")]) (vecIntBinOpV op) :=
    hasTyp_famOf_typedA (Or.inr (Or.inl ⟨rfl, rfl⟩)) hi fsh
  have hq : QuantsOk (simEnv20V B) (VarEnv.empty.bindVals σ)
      (match vbinopRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons f₁ (VecFix.typedV_vecV128_20V c₁ _ hρ) (QuantsOk.cons f₂
      (VecFix.typedV_vecV128_20V c₂ _ hρ) (QuantsOk.cons fsh (VecFix.typedV_shape20V _ _ hρ)
        (QuantsOk.cons fop hty (QuantsOk.cons fc (VecFix.typedV_vecV128_20V r _ hρ)
          QuantsOk.nil))))
  obtain ⟨vs, happ, hvs⟩ := hA.intBin s op c₁ c₂
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

/-- **Rule 40 fires** at an integer shape, to the comparison V2 computes. -/
theorem fires_vrelopInt {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : IntShape}
    {op : IntRelOp}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntRelOp s op)))
    (c₁ c₂ : BitVec 128) :
    Fires (simEnv20V B) "Step_pure" 40 (.tuple [
      .list [adminToV (vconst c₁), adminToV (vconst c₂),
        .case "VRELOP" (.tuple [shapeV (.int s), vecIntRelOpV op])],
      .list [adminToV (vconst (VecIntRelOp s op c₁ c₂))]]) := by
  let r := VecIntRelOp s op c₁ c₂
  let σ := scope2 "vrelop" c₁ c₂ (shapeV (.int s)) (vecIntRelOpV op) (pctV r.toNat)
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c₁.toNat) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (pctV c₂.toNat) := rfl
  have fsh : (VarEnv.empty.bindVals σ).findVal? "sh" = some (shapeV (.int s)) := rfl
  have fop : (VarEnv.empty.bindVals σ).findVal? "vrelop" = some (vecIntRelOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  have hty : HasTyp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.varT "vrelop_" [.expA (.varE "sh")]) (vecIntRelOpV op) :=
    hasTyp_famOf_typedA (Or.inr (Or.inr ⟨rfl, rfl⟩)) hi fsh
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
      (evalArgs_four fsh fop f₁ f₂)).1 (hA.intRel s op c₁ c₂))
  refine Pure.fires_of_ruleAt (hasRuleAt_vrelop20V B) σ hq
    (evalExp_tup2 (Pure.evalExp_list3 (evalExp_vconst f₁) (evalExp_vconst f₂)
      (evalExp_pairV fsh fop)) (evalExp_list1 (evalExp_vconst fc))) ?_
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (Whole.evalExp_eqTrue hcall (evalExp_var fc))

/-! ## The V2 steps -/

/-- The V2 steps from `v128.const c; sh.op` at an integer shape: the value step only. -/
theorem pureStep_vecIntUnOp_inv {P : Profile} {s : IntShape} {op : VecIntUnOp} {c : BitVec 128}
    {code' : List Admin} (h : PureStep P [vconst c, .plain (.vecIntUnOp s op)] code') :
    ∃ r, VecIntUnOpResult s op c r ∧ code' = [vconst r] := by
  generalize hl : [vconst c, Admin.plain (V2.Instr.vecIntUnOp s op)] = l at h
  cases h with
  | vecIntUnOp hr =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecIntUnOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨_, hr, rfl⟩
  | vecIntUnOpTrap hn =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecIntUnOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact absurd rfl (hn _)
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c, Admin.plain (V2.Instr.vecIntUnOp s op)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- The V2 steps from `v128.const c₁; v128.const c₂; sh.op` at an integer shape: the value step
only. -/
theorem pureStep_vecIntBinOp_inv {P : Profile} {s : IntShape} {op : V2.VecIntBinOp}
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)] code') :
    ∃ r, VecIntBinOpResult P s op c₁ c₂ r ∧ code' = [vconst r] := by
  generalize hl : [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecIntBinOp s op)] = l at h
  cases h with
  | vecIntBinOp hr =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecIntBinOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, hr, rfl⟩
  | vecIntBinOpTrap hn =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecIntBinOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact absurd rfl (hn _)
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecIntBinOp s op)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- The only V2 step from `v128.const c₁; v128.const c₂; sh.relop` at an integer shape. -/
theorem pureStep_vecIntRelOp_inv {P : Profile} {s : IntShape} {op : IntRelOp}
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)] code') :
    code' = [vconst (VecIntRelOp s op c₁ c₂)] := by
  generalize hl : [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecIntRelOp s op)] = l at h
  cases h with
  | vecIntRelOp =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecIntRelOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    rfl
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c₁, vconst c₂, Admin.plain (V2.Instr.vecIntRelOp s op)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-! ## Forward -/

/-- **The integer `vunop`s, forward** (rule 34 of the corrected script). -/
theorem fwd_vecIntUnOp20V {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : IntShape}
    {op : VecIntUnOp} {c : BitVec 128} {code' : List Admin}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntUnOp s op)))
    (h : PureStep P [vconst c, .plain (.vecIntUnOp s op)] code') :
    Fires (simEnv20V B) "Step_pure" 34 (.tuple [.list (adminsToV [vconst c,
      .plain (.vecIntUnOp s op)]), .list (adminsToV code')]) := by
  obtain ⟨r, hr, rfl⟩ := pureStep_vecIntUnOp_inv h
  exact fires_vunopInt hA hi c r hr

/-- **The integer `vbinop`s, forward** (rule 36 of the corrected script). -/
theorem fwd_vecIntBinOp20V {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : IntShape}
    {op : V2.VecIntBinOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntBinOp s op)))
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)] code') :
    Fires (simEnv20V B) "Step_pure" 36 (.tuple [.list (adminsToV [vconst c₁, vconst c₂,
      .plain (.vecIntBinOp s op)]), .list (adminsToV code')]) := by
  obtain ⟨r, hr, rfl⟩ := pureStep_vecIntBinOp_inv h
  exact fires_vbinopInt hA hi c₁ c₂ r hr

/-- **The integer `vrelop`s, forward** (rule 40 of the corrected script). -/
theorem fwd_vecIntRelOp20V {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : IntShape}
    {op : IntRelOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntRelOp s op)))
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)] code') :
    Fires (simEnv20V B) "Step_pure" 40 (.tuple [.list (adminsToV [vconst c₁, vconst c₂,
      .plain (.vecIntRelOp s op)]), .list (adminsToV code')]) := by
  rw [pureStep_vecIntRelOp_inv h]
  exact fires_vrelopInt hA hi c₁ c₂

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
