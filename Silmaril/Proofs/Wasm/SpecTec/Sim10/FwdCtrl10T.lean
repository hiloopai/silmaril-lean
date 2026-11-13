module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLeafI32T

/-!
# The control leaves of `FwdCtrl` in `simEnv10T`

`br-zero`, `br-succ`, `return-label`, `return-frame` and `trap-vals` at `FwdAt10T`, at a plain
suffix. `instr` and `admininstr` are both corrected in `simEnv10T`, and `fixCase10` keeps every
case name, so `admininstr` is still `instr` followed by four administrative cases
(`findTyp_instrAdmin10T`), and an instruction typed as `admininstr` is typed as `instr`
(`typedV_instr_of_admin10T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression lowerLabel)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly instrsT nT frameT evalExp_case
  evalExp_tup2 evalExp_list1 evalExp_ne_nil evalExp_or typedV_list_iff typedV_list_append)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_nil prems_one eval_brZero eval_brSucc
  eval_returnLabel eval_returnFrame eval_trapVals)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

open Silmaril.Wasm.SpecTec.Sim10.StoreFix (fixCase10)

theorem caseName10_fixCase10 (c : TypCase) : caseName10 (fixCase10 c) = caseName10 c := by
  have e : ∀ d : TypCase, caseName10 d = Sim20.StoreAgree.caseOp d := fun d => by cases d; rfl
  rw [e, e]
  exact StoreAgree.caseOp_fixCase10 c

/-- **`admininstr` is still `instr` followed by four administrative cases in `simEnv10T`.** -/
theorem findTyp_instrAdmin10T : ∃ ci ex, (simEnv10T B).findTyp? "instr" =
      some ([], [.instD [] [] (.variantT ci)]) ∧
    (simEnv10T B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT (ci ++ ex))]) ∧
    ex.map caseName10 = ["CALL_ADDR", "LABEL_%{%}%", "FRAME_%{%}%", "TRAP"] := by
  obtain ⟨ci, ex, hi, ha, hex⟩ := findTyp_instrAdmin10 (B := B)
  refine ⟨ci.map fixCase10, ex.map fixCase10, instrT_lift hi, ?_, ?_⟩
  · rw [← List.map_append]
    exact adminT_lift ha
  · rw [List.map_map, ← hex]
    exact List.map_congr_left fun c _ => caseName10_fixCase10 c

/-- **An instruction typed as `admininstr` in `simEnv10T` is typed as `instr`.** -/
theorem typedV_instr_of_admin10T {i : V1.Instr} (h : TypedV (simEnv10T B) adminT10 (instrToV i)) :
    TypedV (simEnv10T B) (.varT "instr" []) (instrToV i) := by
  obtain ⟨ci, ex, hi, ha, hex⟩ := findTyp_instrAdmin10T (B := B)
  obtain ⟨u, hu⟩ := instrToV_case10 i
  rw [hu] at h ⊢
  obtain ⟨op, w, he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed ha (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  rcases hasTypCase_append_inv hc with hc' | hm
  · exact fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) hi
      Equiv.evalArgs_nil matchArgs_nil hc'
  · exact absurd (hex ▸ hm) (instrHead10_not_admin i)

/-- **Plain code typed as `admininstr*` in `simEnv10T` is a typed `instr*`.** -/
theorem typedV_instrs_of_admins10T {is : List V1.Instr}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV (is.map .source)))) :
    TypedV (simEnv10T B) instrsT (.list (adminsToV (is.map .source))) := by
  rw [adminsToV_map10, List.map_map] at h ⊢
  refine typedV_list_iff.2 fun u hu => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hu
  exact typedV_instr_of_admin10T (typedV_list_iff.1 h _ hu)

/-- Every V1 label index is a typed `labelidx` in `simEnv10T`. -/
theorem typedV_labelidx10T (l : LabelIdx) : TypedV (simEnv10T B) (.varT "labelidx" []) (idxV l) :=
  typedV10T (typedV_labelidx10 l)

/-- The typed pieces of a label body `val'* val* M instr*`, in `simEnv10T`. -/
theorem body_typed10T {extra vs : List Execution.Runtime.Value} {m : Admin} {is : List V1.Instr}
    (h : TypedV (simEnv10T B) adminsT
      (.list (adminsToV (values extra ++ values vs ++ [m] ++ is.map .source)))) :
    TypedV (simEnv10T B) valsTy10 (.list (adminsToV (values extra))) ∧
      TypedV (simEnv10T B) valsTy10 (.list (adminsToV (values vs))) ∧
      TypedV (simEnv10T B) instrsT (.list (adminsToV (is.map .source))) := by
  rw [adminsToV_body10] at h
  obtain ⟨h₁₂, hi⟩ := typedV_list_append.1 h
  obtain ⟨h₁₂', -⟩ := typedV_list_append.1 h₁₂
  obtain ⟨h₁, h₂⟩ := typedV_list_append.1 h₁₂'
  rw [adminsToV_values] at h₁ h₂ ⊢
  rw [adminsToV_values]
  exact ⟨typedV_vals_of_admins10T h₁, typedV_vals_of_admins10T h₂, typedV_instrs_of_admins10T hi⟩

/-- **`br-zero` forward**: V1's `labelBranch`, at a plain suffix. -/
theorem fwdAt10T_labelBranch (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (extra vs : List Execution.Runtime.Value) (is : List V1.Instr) (hlen : vs.length = n) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++
      is.map .source)]⟩ ⟨s, f, values vs ++ expression cont⟩ := by
  subst hlen
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨-, hcont, hb⟩ := label_inv10T (typedV_head10T hc)
  obtain ⟨he₁, hv, hi⟩ := body_typed10T hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN (adminsToV (values vs)).length)),
    ("instr'*", .list (instrsToV cont)), ("val'*", .list (adminsToV (values extra))),
    ("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (values vs)).length)) := rfl
  have he := eval_brZero (env := simEnv10 B) fn rfl rfl rfl rfl
  have hlen : (adminsToV (values vs)).length = vs.length := by
    rw [adminsToV_values, List.length_map]
  have hlhs : adminsToV [.label vs.length cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++
      is.map .source)] = [.case "LABEL_%{%}%" (.tuple [.num (.natN (adminsToV (values vs)).length),
        .list (instrsToV cont), .list (adminsToV (values extra) ++ adminsToV (values vs) ++
          [.case "BR" (pctV 0)] ++ adminsToV (is.map .source))])] := by
    rw [hlen, adminsToV_label10, adminsToV_body10]
    rfl
  have hrhs : adminsToV (values vs ++ expression cont) =
      adminsToV (values vs) ++ instrsToV cont := by
    rw [adminsToV_map10, List.map_append, ← adminsToV_map10, ← adminsToV_map10,
      adminsToV_expression]
  rw [hlhs, hrhs]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_brZero B) σ
    (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hcont _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (he₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))))
    he prems_nil)

/-- **`br-succ` forward**: V1's `labelBranchOuter`, at a plain suffix. -/
theorem fwdAt10T_labelBranchOuter (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (vs : List Execution.Runtime.Value) (is : List V1.Instr) (l : LabelIdx) (hl : l.toNat ≠ 0) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ is.map .source)]⟩
      ⟨s, f, values vs ++ [.source (.br (lowerLabel l))]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨hn', hcont, hb⟩ := label_inv10T (typedV_head10T hc)
  obtain ⟨-, hv, hi⟩ := body_typed10T (extra := []) hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (values vs))), ("l", idxV (lowerLabel l)),
    ("instr*", .list (adminsToV (is.map .source)))]
  have he := eval_brSucc (env := simEnv10 B) (ρ := VarEnv.empty.bindVals σ)
    (k := l.toNat - 1) rfl rfl rfl rfl rfl
  have hk : l.toNat - 1 + 1 = l.toNat := by omega
  rw [hk] at he
  have hlhs : adminsToV [.label n cont (values vs ++ [.source (.br l)] ++ is.map .source)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont),
        .list (adminsToV (values vs) ++ [.case "BR" (pctV l.toNat)] ++
          adminsToV (is.map .source))])] := by
    rw [adminsToV_label10]
    simp only [adminsToV_map10, List.map_append]
    rfl
  have hrhs : adminsToV (values vs ++ [.source (.br (lowerLabel l))]) =
      adminsToV (values vs) ++ [.case "BR" (pctV (l.toNat - 1))] := by
    rw [adminsToV_map10, List.map_append, ← adminsToV_map10]
    rfl
  rw [hlhs, hrhs]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_brSucc B) σ
    (QuantsOk.cons rfl (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hcont _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (typedV_labelidx10T _ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hi _ ⟨rfl, rfl, rfl⟩)
          QuantsOk.nil)))))
    he prems_nil)

/-- **`return-label` forward**: V1's `labelReturn`, at a plain suffix. -/
theorem fwdAt10T_labelReturn (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ is.map .source)]⟩
      ⟨s, f, values vs ++ [.source .return_]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨hn', hcont, hb⟩ := label_inv10T (typedV_head10T hc)
  obtain ⟨-, hv, hi⟩ := body_typed10T (extra := []) hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have he := eval_returnLabel (env := simEnv10 B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl
  have hlhs : adminsToV [.label n cont (values vs ++ [.source .return_] ++ is.map .source)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont),
        .list (adminsToV (values vs) ++ [caseNilV "RETURN"] ++ adminsToV (is.map .source))])] := by
    rw [adminsToV_label10]
    simp only [adminsToV_map10, List.map_append]
    rfl
  have hrhs : adminsToV (values vs ++ [.source .return_]) =
      adminsToV (values vs) ++ [caseNilV "RETURN"] := by
    rw [adminsToV_map10, List.map_append, ← adminsToV_map10]
    rfl
  rw [hlhs, hrhs]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_returnLabel B) σ
    (QuantsOk.cons rfl (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hcont _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (hi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    he prems_nil)

/-- **`return-frame` forward**: V1's `frameReturn`, at a plain suffix. -/
theorem fwdAt10T_frameReturn (s : Store H) (f : Frame) (n : Nat) (fr : Frame)
    (extra vs : List Execution.Runtime.Value) (is : List V1.Instr) (hlen : vs.length = n) :
    FwdAt10T B hn ⟨s, f, [.frame n fr (values extra ++ values vs ++ [.source .return_] ++
      is.map .source)]⟩ ⟨s, f, values vs⟩ := by
  subst hlen
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨-, hfr, hb⟩ := frame_inv10T (typedV_head10T hc)
  obtain ⟨he₁, hv, hi⟩ := body_typed10T hb
  let σ : List (IL.Id × Value) := [("n", .num (.natN (adminsToV (values vs)).length)),
    ("f", frameV fr), ("val'*", .list (adminsToV (values extra))),
    ("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (values vs)).length)) := rfl
  have he := eval_returnFrame (env := simEnv10 B) fn rfl rfl rfl rfl
  have hlen : (adminsToV (values vs)).length = vs.length := by
    rw [adminsToV_values, List.length_map]
  have hlhs : adminsToV [.frame vs.length fr (values extra ++ values vs ++ [.source .return_] ++
      is.map .source)] = [.case "FRAME_%{%}%" (.tuple [.num (.natN (adminsToV (values vs)).length),
        frameV fr, .list (adminsToV (values extra) ++ adminsToV (values vs) ++
          [caseNilV "RETURN"] ++ adminsToV (is.map .source))])] := by
    rw [hlen, adminsToV_frame10, adminsToV_body10]
    rfl
  rw [hlhs]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_returnFrame B) σ
    (QuantsOk.cons fn (typedV_n10T _ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
      (hfr _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (he₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
        (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))))
    he prems_nil)

/-- `trap-vals` at `val* TRAP instr*` with `val*` or `instr*` non-empty. -/
theorem fwdAt10T_trapVals (s : Store H) (f : Frame) (vs : List Execution.Runtime.Value)
    (is : List V1.Instr) (hne : vs ≠ [] ∨ is ≠ []) :
    FwdAt10T B hn ⟨s, f, values vs ++ [.trap] ++ is.map .source⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  have e : values vs ++ [.trap] ++ is.map .source =
      values [] ++ values vs ++ [.trap] ++ is.map .source := rfl
  obtain ⟨-, hv, hi⟩ := body_typed10T (e ▸ hc)
  let σ : List (IL.Id × Value) :=
    [("val*", .list (adminsToV (values vs))), ("instr*", .list (adminsToV (is.map .source)))]
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (adminsToV (values vs))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "instr*" =
      some (.list (adminsToV (is.map .source))) := rfl
  have he := eval_trapVals (env := simEnv10 B) fv fi
  have hne' : decide (adminsToV (values vs) ≠ [] ∨ adminsToV (is.map .source) ≠ []) = true := by
    rw [adminsToV_values, adminsToV_map10]
    simpa [List.map_eq_nil_iff] using hne
  have hpr : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "instr" "instr*") (.listE []))) (.bool true) :=
    hne' ▸ evalExp_or (evalExp_ne_nil (evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (evalExp_iterPat (by decide) fi))
  have hlhs : adminsToV (values vs ++ [.trap] ++ is.map .source) =
      adminsToV (values vs) ++ caseNilV "TRAP" :: adminsToV (is.map .source) := by
    simp only [adminsToV_map10, List.map_append, List.append_assoc, List.singleton_append]
    rfl
  rw [hlhs]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_trapVals B) σ
    (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hi _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil)) he (prems_one (.ifPr hpr)))

/-- **`trap-vals` forward**: V1's `trapValues`, at a plain suffix. -/
theorem fwdAt10T_trapValues (s : Store H) (f : Frame) (v : Execution.Runtime.Value)
    (vs : List Execution.Runtime.Value) (is : List V1.Instr) :
    FwdAt10T B hn ⟨s, f, values (v :: vs) ++ [.trap] ++ is.map .source⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10T_trapVals s f (v :: vs) is (.inl (List.cons_ne_nil _ _))

/-- **`trap-vals` forward**: V1's `trapTail`, at a plain suffix. -/
theorem fwdAt10T_trapTail (s : Store H) (f : Frame) (i : V1.Instr) (is : List V1.Instr) :
    FwdAt10T B hn ⟨s, f, .trap :: (i :: is).map .source⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10T_trapVals s f [] (i :: is) (.inr (List.cons_ne_nil _ _))


end Silmaril.Wasm.SpecTec.Sim10.Whole
