module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneRules

/-!
# The float vector operators forward, under `VecNumAgree`

The fourteen float-only vector operators are untyped in `simEnv20T`, so no
`Step_pure` rule can fire on them there. In the corrected script they are typed
(`hasTyp_famFloat`), and with the vector numerics hypothesis `VecNumAgree` the rules `vunop`,
`vbinop-val` and `vrelop` match every V2 step at the float shapes:

* **`fwd_vecFloatUnOp20V`**, **`fwd_vecFloatBinOp20V`**, **`fwd_vecFloatRelOp20V`**: every V2 pure
  step from `v128.const c; f32x4.op` (and the binary forms, at both float shapes) is a firing of
  rule 34 (36, 40) of `simEnv20V B` from the image of the source to the image of V2's successor.
  The V2 trap steps of `vunop`/`vbinop` at float shapes are vacuous (the result sets are nonempty).
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
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (fNames famForm_vunop famForm_vbinop famForm_vrelop
  findTyp_fam_simEnv20V)

variable {B : Builtins}

theorem floatUnOpV_mem (op : FloatUnOp) : ∃ o ∈ fNames "vunop_", floatUnOpV op = caseNilV o := by
  cases op <;> exact ⟨_, by simp [fNames], rfl⟩

theorem vecFloatBinOpV_mem (op : V2.VecFloatBinOp) :
    ∃ o ∈ fNames "vbinop_", vecFloatBinOpV op = caseNilV o := by
  cases op <;> exact ⟨_, by simp [fNames], rfl⟩

theorem floatRelOpV_mem (op : FloatRelOp) : ∃ o ∈ fNames "vrelop_", floatRelOpV op = caseNilV o := by
  cases op <;> exact ⟨_, by simp [fNames], rfl⟩

/-- `VCONST V128 x`, evaluated. -/
theorem evalExp_vconst {env : Env} {ρ : VarEnv} {x : IL.Id} {c : BitVec 128}
    (h : ρ.findVal? x = some (pctV c.toNat)) : EvalExp env ρ (vconstE x) (adminToV (vconst c)) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_var h))

/-- `OP(x, y)` with two bound variables. -/
theorem evalExp_pairV {env : Env} {ρ : VarEnv} {op : MixopS} {x y : IL.Id} {a b : Value}
    (ha : ρ.findVal? x = some a) (hb : ρ.findVal? y = some b) :
    EvalExp env ρ (.caseE op (.tupE [.varE x, .varE y])) (.case op (.tuple [a, b])) :=
  evalExp_case (evalExp_tup2 (evalExp_var ha) (evalExp_var hb))

theorem findDef_none_bindVals (σ : List (IL.Id × Value)) (x : IL.Id) :
    (VarEnv.empty.bindVals σ).findDef? x = none := by
  simp [VarEnv.findDef?, VarEnv.bindVals, VarEnv.empty, Map.empty]

theorem typs_bindVals (σ : List (IL.Id × Value)) : (VarEnv.empty.bindVals σ).typs = [] := rfl

/-! ## `vunop` -/

/-- **Rule 34 fires** at a float shape, to every result of `$vunop_` that V2 permits. -/
theorem fires_vunopFloat {P : Profile} (hA : VecNumAgree (simEnv20V B) P) (s : FloatShape)
    (op : FloatUnOp) (c r : BitVec 128) (hr : VecFloatUnOpResult P s op c r) :
    Fires (simEnv20V B) "Step_pure" 34 (.tuple [
      .list [adminToV (vconst c), .case "VUNOP" (.tuple [shapeV (.float s), floatUnOpV op])],
      .list [adminToV (vconst r)]]) := by
  let σ : List (IL.Id × Value) := [("c_1", pctV c.toNat), ("sh", shapeV (.float s)),
    ("vunop", floatUnOpV op), ("c", pctV r.toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c.toNat) := rfl
  have fsh : (VarEnv.empty.bindVals σ).findVal? "sh" = some (shapeV (.float s)) := rfl
  have fop : (VarEnv.empty.bindVals σ).findVal? "vunop" = some (floatUnOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  obtain ⟨o, ho, hop⟩ := floatUnOpV_mem op
  have hty : HasTyp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.varT "vunop_" [.expA (.varE "sh")]) (floatUnOpV op) := by
    rw [hop]
    exact hasTyp_famFloat famForm_vunop (findTyp_fam_simEnv20V B).1 fsh ho
      (by decide)
  have hq : QuantsOk (simEnv20V B) (VarEnv.empty.bindVals σ)
      (match vunopRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons f₁ (VecFix.typedV_vecV128_20V c _ hρ) (QuantsOk.cons fsh
      (VecFix.typedV_shape20V _ _ hρ) (QuantsOk.cons fop hty
        (QuantsOk.cons fc (VecFix.typedV_vecV128_20V r _ hρ) QuantsOk.nil)))
  obtain ⟨vs, happ, hvs⟩ := hA.floatUn s op c
  have hcall : EvalExp (simEnv20V B) (VarEnv.empty.bindVals σ)
      (.callE "vunop_" [.expA (.varE "sh"), .expA (.varE "vunop"), .expA (.varE "c_1")]) (.list vs) :=
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

/-- The V2 steps from `v128.const c; sh.op` at a float shape: the value step only. -/
theorem pureStep_vecFloatUnOp_inv {P : Profile} {s : FloatShape} {op : FloatUnOp} {c : BitVec 128}
    {code' : List Admin} (h : PureStep P [vconst c, .plain (.vecFloatUnOp s op)] code') :
    ∃ r, VecFloatUnOpResult P s op c r ∧ code' = [vconst r] := by
  generalize hl : [vconst c, Admin.plain (V2.Instr.vecFloatUnOp s op)] = l at h
  cases h with
  | vecFloatUnOp hr =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecFloatUnOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨_, hr, rfl⟩
  | vecFloatUnOpTrap hn =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecFloatUnOp.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    obtain ⟨r, hr⟩ := VecFloatUnOpResult_nonempty P s op c
    exact absurd hr (hn r)
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c, Admin.plain (V2.Instr.vecFloatUnOp s op)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- **The float `vunop`s, forward**: every V2 pure step from `v128.const c; sh.op` at a float shape
is a firing of rule 34 in the corrected script. -/
theorem fwd_vecFloatUnOp20V {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {s : FloatShape}
    {op : FloatUnOp} {c : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecFloatUnOp s op)] code') :
    Fires (simEnv20V B) "Step_pure" 34 (.tuple [.list (adminsToV [vconst c,
      .plain (.vecFloatUnOp s op)]), .list (adminsToV code')]) := by
  obtain ⟨r, hr, rfl⟩ := pureStep_vecFloatUnOp_inv h
  exact fires_vunopFloat hA s op c r hr

end Silmaril.Wasm.SpecTec.Sim20.VecLane
