module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLeaf10T

/-!
# The forward leaves of `FwdLeafI32` in `simEnv10T`

`br_if` and `select` at `FwdAt10T`. Their redexes have no nested code, so the instruction
typings move back to `simEnv10` (`typedV_admin_back10T`), round 2's inversions apply, and the
quantifier typings grow again (`typedV10T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly evalExp_case evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one evalExp_caseNil evalExp_list0
  evalExp_sub evalExp_immCmp cmp_ne_zero cmp_eq_zero)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (goodT_of_all)

/-- **The payload of a `CONST I32 c` typed in `simEnv10T` is a `val_(I32)`.** -/
theorem typedV_valI32_of_const10T {c : BitVec 32}
    (h : TypedV (simEnv10T B) adminT10 (valV ⟨.int .i32, c⟩)) :
    TypedV (simEnv10T B) valI32T (pctV c.toNat) :=
  typedV10T (typedV_valI32_of_const10 (typedV_valAdmin_back10T h))

/-- The label of a `BR_IF l` typed in `simEnv10T` is a typed `labelidx`. -/
theorem typedV_labelidx_of_brIf10T {l : LabelIdx}
    (h : TypedV (simEnv10T B) adminT10 (.case "BR_IF" (idxV l))) :
    TypedV (simEnv10T B) (.varT "labelidx" []) (idxV l) := by
  obtain ⟨cs, htd, hc⟩ := findTyp_admininstr10_brIf (B := B)
  exact typedV10T (typedV_labelidx_of_brIf10
    (typedV_admin_back10T htd hc (by decide) (goodT_of_all (by decide)) h))

/-- The three operands of a `select` redex typed in `simEnv10T` are typed. -/
theorem select_typed10T {a b : Execution.Runtime.Value} {c : BitVec 32}
    (hc : TypedV (simEnv10T B) adminsT
      (.list (adminsToV [value a, value b, value (.int .i32 c), .source .select]))) :
    TypedV (simEnv10T B) (.varT "val" []) (valV a) ∧
      TypedV (simEnv10T B) (.varT "val" []) (valV b) ∧
      TypedV (simEnv10T B) valI32T (pctV c.toNat) := by
  rw [adminsToV_select10] at hc
  have ha : TypedV (simEnv10T B) adminT10 (valV a) := Sim.typedV_list_iff.1 hc _ (.head _)
  have hb : TypedV (simEnv10T B) adminT10 (valV b) :=
    Sim.typedV_list_iff.1 hc _ (.tail _ (.head _))
  have hi : TypedV (simEnv10T B) adminT10 (valV ⟨.int .i32, c⟩) :=
    Sim.typedV_list_iff.1 hc _ (.tail _ (.tail _ (.head _)))
  exact ⟨typedV_val_of_admin10T (w := .tuple [valTypeV a.type, numV a]) ha,
    typedV_val_of_admin10T (w := .tuple [valTypeV b.type, numV b]) hb,
    typedV_valI32_of_const10T hi⟩

/-- **`br_if-true` forward**: V1's `brIfNonzero`. -/
theorem fwdAt10T_brIfNonzero (s : Store H) (f : Frame) (l : LabelIdx) (c : BitVec 32) (hc0 : c ≠ 0) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 c), .source (.brIf l)]⟩ ⟨s, f, [.source (.br l)]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  have hci : TypedV (simEnv10T B) valI32T (pctV c.toNat) := typedV_valI32_of_const10T (by
    have h := typedV_head10T hc
    rwa [adminToV_value] at h)
  have hl : TypedV (simEnv10T B) (.varT "labelidx" []) (idxV l) :=
    typedV_labelidx_of_brIf10T (typedV_second10T hc)
  let σ : List (IL.Id × Value) := [("c", pctV c.toNat), ("l", idxV l)]
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have fl : (VarEnv.empty.bindVals σ).findVal? "l" = some (idxV l) := rfl
  rw [adminsToV_brIf10]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_brIfTrue B) σ
    (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fl (hl _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (Sim20.Pure.evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (evalExp_var fc))) (evalExp_case (evalExp_var fl)))
      (evalExp_list1 (evalExp_case (evalExp_var fl))))
    (prems_one (.ifPr (evalExp_immCmp fc (cmp_ne_zero hc0)))))

/-- **`br_if-false` forward**: V1's `brIfZero`. -/
theorem fwdAt10T_brIfZero (s : Store H) (f : Frame) (l : LabelIdx) :
    FwdAt10T B hn ⟨s, f, [value (.int .i32 0), .source (.brIf l)]⟩ ⟨s, f, []⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  have hci : TypedV (simEnv10T B) valI32T (pctV (0 : BitVec 32).toNat) :=
    typedV_valI32_of_const10T (by
      have h := typedV_head10T hc
      rwa [adminToV_value] at h)
  have hl : TypedV (simEnv10T B) (.varT "labelidx" []) (idxV l) :=
    typedV_labelidx_of_brIf10T (typedV_second10T hc)
  let σ : List (IL.Id × Value) := [("c", pctV (0 : BitVec 32).toNat), ("l", idxV l)]
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV (0 : BitVec 32).toNat) := rfl
  have fl : (VarEnv.empty.bindVals σ).findVal? "l" = some (idxV l) := rfl
  erw [adminsToV_brIf10 (0 : BitVec 32) l]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_brIfFalse B) σ
    (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fl (hl _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (Sim20.Pure.evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (evalExp_var fc))) (evalExp_case (evalExp_var fl))) evalExp_list0)
    (prems_one (.ifPr (evalExp_immCmp fc cmp_eq_zero))))

/-- **`select-true` forward**: V1's `selectNonzero`. -/
theorem fwdAt10T_selectNonzero (s : Store H) (f : Frame) (a b : Execution.Runtime.Value)
    (c : BitVec 32) (hc0 : c ≠ 0) :
    FwdAt10T B hn ⟨s, f, [value a, value b, value (.int .i32 c), .source .select]⟩
      ⟨s, f, [value a]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨ha, hb, hci⟩ := select_typed10T hc
  let σ : List (IL.Id × Value) := [("val_1", valV a), ("val_2", valV b), ("c", pctV c.toNat)]
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "val_1" = some (valV a) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "val_2" = some (valV b) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have hr : adminsToV [value a] = [valV a] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rw [adminsToV_select10, hr]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_selectTrue B) σ
    (QuantsOk.cons f₁ (ha _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons f₂ (hb _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (Sim20.Pure.evalExp_list4 (evalExp_sub (evalExp_var f₁))
      (evalExp_sub (evalExp_var f₂)) (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      evalExp_caseNil) (evalExp_list1 (evalExp_sub (evalExp_var f₁))))
    (prems_one (.ifPr (evalExp_immCmp fc (cmp_ne_zero hc0)))))

/-- **`select-false` forward**: V1's `selectZero`. -/
theorem fwdAt10T_selectZero (s : Store H) (f : Frame) (a b : Execution.Runtime.Value) :
    FwdAt10T B hn ⟨s, f, [value a, value b, value (.int .i32 0), .source .select]⟩
      ⟨s, f, [value b]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨ha, hb, hci⟩ := select_typed10T hc
  let σ : List (IL.Id × Value) :=
    [("val_1", valV a), ("val_2", valV b), ("c", pctV (0 : BitVec 32).toNat)]
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "val_1" = some (valV a) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "val_2" = some (valV b) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV (0 : BitVec 32).toNat) := rfl
  have hr : adminsToV [value b] = [valV b] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  erw [adminsToV_select10 a b (0 : BitVec 32), hr]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_selectFalse B) σ
    (QuantsOk.cons f₁ (ha _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons f₂ (hb _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (Sim20.Pure.evalExp_list4 (evalExp_sub (evalExp_var f₁))
      (evalExp_sub (evalExp_var f₂)) (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      evalExp_caseNil) (evalExp_list1 (evalExp_sub (evalExp_var f₂))))
    (prems_one (.ifPr (evalExp_immCmp fc cmp_eq_zero))))


end Silmaril.Wasm.SpecTec.Sim10.Whole
