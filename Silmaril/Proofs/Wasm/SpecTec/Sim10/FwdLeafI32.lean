module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLeaf

/-!
# The 1.0 script forward at the `i32`-guarded leaves: `br_if` and `select`

1.0's `br_if-*` and `select-*` quantify the condition `c : val_(I32)`. Its typing comes from the
code: `CONST I32 c` typed as `admininstr` types its payload `(I32, c)` at
`(valtype, val_(valtype))`, and `val_(valtype)` with `valtype := I32` is `val_(I32)` in every scope
(`typedV_valI32_of_const10`). The label `l : labelidx` of `BR_IF l` is typed by the `BR_IF` case.

* `fwdAt10_brIfZero`, `fwdAt10_brIfNonzero`: `Step_pure` 11 and 10;
* `fwdAt10_selectZero`, `fwdAt10_selectNonzero`: `Step_pure` 4 and 3.

All at every builtins, lifted by `Step/pure`.
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

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Typing the condition and the label -/

/-- **The payload of a typed `CONST I32 c` is a `val_(I32)`**, in every scope. -/
theorem typedV_valI32_of_const10 {c : BitVec 32}
    (h : TypedV (simEnv10 B) adminT10 (valV ⟨.int .i32, c⟩)) :
    TypedV (simEnv10 B) valI32T (pctV c.toNat) := by
  obtain ⟨cs, htd, hc, -, -⟩ := findTyp_admininstr10F (B := B)
  have hp : HasTyp (simEnv10 B) VarEnv.empty constT10 (.tuple [caseNilV "I32", pctV c.toNat]) :=
    hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  have hl : localTyp? (VarEnv.empty.bindVal "valtype" (caseNilV "I32")) "val_"
      [.expA (.varE "valtype")] = none := by simp [localTyp?]
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff hl).1 hy'
  have ha₁ : EvalArgs (simEnv10 B) (VarEnv.empty.bindVal "valtype" (caseNilV "I32"))
      [.expA (.varE "valtype")] [.val (caseNilV "I32")] := evalArgs_cons (evalExp_var rfl) evalArgs_nil
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.evalArgs_unique hargs ha₁
  intro ρ _
  have hl' : localTyp? ρ "val_" [.expA (.caseE "I32" (.tupE []))] = none := by simp [localTyp?]
  exact (hasTyp_varT_global_iff hl').2 ⟨td, _, htd', evalArgs_cons evalExp_caseNil evalArgs_nil, hi⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- 1.0's `admininstr` at `BR_IF`. -/
theorem findTyp_admininstr10_brIf : ∃ cs, (simEnv10 B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCase cs "BR_IF" = some (.varT "labelidx" [], []) :=
  ⟨_, rfl, rfl⟩

/-- The label of a typed `BR_IF l` is a typed `labelidx`. -/
theorem typedV_labelidx_of_brIf10 {l : LabelIdx}
    (h : TypedV (simEnv10 B) adminT10 (.case "BR_IF" (idxV l))) :
    TypedV (simEnv10 B) (.varT "labelidx" []) (idxV l) := by
  obtain ⟨cs, htd, hc⟩ := findTyp_admininstr10_brIf (B := B)
  exact typedV_of_scope valsOnly_empty
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc)

/-! ## `br_if` -/

/-- The image of `CONST I32 c; BR_IF l`. -/
theorem adminsToV_brIf10 (c : BitVec 32) (l : LabelIdx) :
    adminsToV [value (.int .i32 c), .source (.brIf l)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]), .case "BR_IF" (idxV l)] := by
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-- **`br_if-true` forward**: V1's `brIfNonzero`. -/
theorem fwdAt10_brIfNonzero (s : Store H) (f : Frame) (l : LabelIdx) (c : BitVec 32) (hc0 : c ≠ 0) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.brIf l)]⟩ ⟨s, f, [.source (.br l)]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  have hci : TypedV (simEnv10 B) valI32T (pctV c.toNat) := typedV_valI32_of_const10 (by
    have h := typedV_head10 hc
    rwa [adminToV_value] at h)
  have hl : TypedV (simEnv10 B) (.varT "labelidx" []) (idxV l) :=
    typedV_labelidx_of_brIf10 (typedV_second10 hc)
  let σ : List (IL.Id × Value) := [("c", pctV c.toNat), ("l", idxV l)]
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have fl : (VarEnv.empty.bindVals σ).findVal? "l" = some (idxV l) := rfl
  rw [adminsToV_brIf10]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_brIfTrue B) σ
    (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fl (hl _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (Sim20.Pure.evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (evalExp_var fc))) (evalExp_case (evalExp_var fl)))
      (evalExp_list1 (evalExp_case (evalExp_var fl))))
    (prems_one (.ifPr (evalExp_immCmp fc (cmp_ne_zero hc0)))))

/-- **`br_if-false` forward**: V1's `brIfZero`. -/
theorem fwdAt10_brIfZero (s : Store H) (f : Frame) (l : LabelIdx) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 0), .source (.brIf l)]⟩ ⟨s, f, []⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  have hci : TypedV (simEnv10 B) valI32T (pctV (0 : BitVec 32).toNat) :=
    typedV_valI32_of_const10 (by
      have h := typedV_head10 hc
      rwa [adminToV_value] at h)
  have hl : TypedV (simEnv10 B) (.varT "labelidx" []) (idxV l) :=
    typedV_labelidx_of_brIf10 (typedV_second10 hc)
  let σ : List (IL.Id × Value) := [("c", pctV (0 : BitVec 32).toNat), ("l", idxV l)]
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV (0 : BitVec 32).toNat) := rfl
  have fl : (VarEnv.empty.bindVals σ).findVal? "l" = some (idxV l) := rfl
  erw [adminsToV_brIf10 (0 : BitVec 32) l]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_brIfFalse B) σ
    (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fl (hl _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (Sim20.Pure.evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (evalExp_var fc))) (evalExp_case (evalExp_var fl))) evalExp_list0)
    (prems_one (.ifPr (evalExp_immCmp fc cmp_eq_zero))))

/-! ## `select` -/

/-- The image of `a b (CONST I32 c) SELECT`. -/
theorem adminsToV_select10 (a b : Execution.Runtime.Value) (c : BitVec 32) :
    adminsToV [value a, value b, value (.int .i32 c), .source .select] =
      [valV a, valV b, .case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
        caseNilV "SELECT"] := by
  rw [adminsToV_map10, List.map_cons, List.map_cons, List.map_cons, adminToV_value, adminToV_value,
    adminToV_value]
  rfl

/-- The three operands of a typed `select` redex are typed. -/
theorem select_typed10 {a b : Execution.Runtime.Value} {c : BitVec 32}
    (hc : TypedV (simEnv10 B) adminsT
      (.list (adminsToV [value a, value b, value (.int .i32 c), .source .select]))) :
    TypedV (simEnv10 B) (.varT "val" []) (valV a) ∧ TypedV (simEnv10 B) (.varT "val" []) (valV b) ∧
      TypedV (simEnv10 B) valI32T (pctV c.toNat) := by
  rw [adminsToV_select10] at hc
  have ha : TypedV (simEnv10 B) adminT10 (valV a) := Sim.typedV_list_iff.1 hc _ (.head _)
  have hb : TypedV (simEnv10 B) adminT10 (valV b) := Sim.typedV_list_iff.1 hc _ (.tail _ (.head _))
  have hi : TypedV (simEnv10 B) adminT10 (valV ⟨.int .i32, c⟩) :=
    Sim.typedV_list_iff.1 hc _ (.tail _ (.tail _ (.head _)))
  exact ⟨typedV_val_of_admin10 (w := .tuple [valTypeV a.type, numV a]) ha,
    typedV_val_of_admin10 (w := .tuple [valTypeV b.type, numV b]) hb, typedV_valI32_of_const10 hi⟩

/-- **`select-true` forward**: V1's `selectNonzero`. -/
theorem fwdAt10_selectNonzero (s : Store H) (f : Frame) (a b : Execution.Runtime.Value)
    (c : BitVec 32) (hc0 : c ≠ 0) :
    FwdAt10 B hn ⟨s, f, [value a, value b, value (.int .i32 c), .source .select]⟩
      ⟨s, f, [value a]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨ha, hb, hci⟩ := select_typed10 hc
  let σ : List (IL.Id × Value) := [("val_1", valV a), ("val_2", valV b), ("c", pctV c.toNat)]
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "val_1" = some (valV a) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "val_2" = some (valV b) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have hr : adminsToV [value a] = [valV a] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rw [adminsToV_select10, hr]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_selectTrue B) σ
    (QuantsOk.cons f₁ (ha _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons f₂ (hb _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (Sim20.Pure.evalExp_list4 (evalExp_sub (evalExp_var f₁))
      (evalExp_sub (evalExp_var f₂)) (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      evalExp_caseNil) (evalExp_list1 (evalExp_sub (evalExp_var f₁))))
    (prems_one (.ifPr (evalExp_immCmp fc (cmp_ne_zero hc0)))))

/-- **`select-false` forward**: V1's `selectZero`. -/
theorem fwdAt10_selectZero (s : Store H) (f : Frame) (a b : Execution.Runtime.Value) :
    FwdAt10 B hn ⟨s, f, [value a, value b, value (.int .i32 0), .source .select]⟩
      ⟨s, f, [value b]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨ha, hb, hci⟩ := select_typed10 hc
  let σ : List (IL.Id × Value) :=
    [("val_1", valV a), ("val_2", valV b), ("c", pctV (0 : BitVec 32).toNat)]
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "val_1" = some (valV a) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "val_2" = some (valV b) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV (0 : BitVec 32).toNat) := rfl
  have hr : adminsToV [value b] = [valV b] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  erw [adminsToV_select10 a b (0 : BitVec 32), hr]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_selectFalse B) σ
    (QuantsOk.cons f₁ (ha _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons f₂ (hb _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fc (hci _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (Sim20.Pure.evalExp_list4 (evalExp_sub (evalExp_var f₁))
      (evalExp_sub (evalExp_var f₂)) (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      evalExp_caseNil) (evalExp_list1 (evalExp_sub (evalExp_var f₂))))
    (prems_one (.ifPr (evalExp_immCmp fc cmp_eq_zero))))

end Silmaril.Wasm.SpecTec.Sim10.Whole
