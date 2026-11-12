module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Forward

/-!
# Family C: `return_call_ref` out of a context, and `call_ref` on null

The three `Step_read` rules that unwind a `RETURN_CALL_REF` through a label, a handler, or a frame
whose callee is null (`return_call_ref-label`, `-handler`, `-frame-null`), and `Step/call_ref-null`,
constructed under the declarative reading and discharged as `Forward` fields. None of them calls a
SpecTec function, so no primitive of `B` is involved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV valsPat iterPat evalExp_iterPat evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecRead
  (returnCallRefLabelRule returnCallRefHandlerRule returnCallRefFrameNullRule)
open Silmaril.SpecTec.Equiv.ExecStepRules (callRefNullRule)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-! ## The constructions -/

/-- `Step_read/return_call_ref-label`. -/
theorem sread_returnCallRefLabel {env : Env}
    (h : HasRuleAt env "Step_read" "%~>%" 8 returnCallRefLabelRule)
    {z k yy : Value} {cont ws is : List Value} (hz : TypedV env stateT z) (hk : TypedV env nT k)
    (hc : TypedV env instrsT (.list cont)) (hw : TypedV env valsT (.list ws))
    (hy : TypedV env typeuseT yy) (his : TypedV env instrsT (.list is)) :
    SRead env (cfgV z [.case "LABEL_%{%}%" (.tuple [k, .list cont,
        .list (ws ++ [.case "RETURN_CALL_REF" yy] ++ is)])])
      (ws ++ [.case "RETURN_CALL_REF" yy]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("k", k), ("instr'*", .list cont), ("val*", .list ws),
    ("yy", yy), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fk : ρ.findVal? "k" = some k := rfl
  have fc : ρ.findVal? "instr'*" = some (.list cont) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  have er : EvalExp env ρ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fk (hk ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fy (hy ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fk) (evalExp_iterPat (by decide) fc)
          (evalExp_cat (evalExp_cat ev er) (evalExp_iterPat (by decide) fi)))))))
      (evalExp_cat ev er))
    (fun _ h => nomatch h)

/-- `Step_read/return_call_ref-handler`. -/
theorem sread_returnCallRefHandler {env : Env}
    (h : HasRuleAt env "Step_read" "%~>%" 9 returnCallRefHandlerRule)
    {z k yy : Value} {cs ws is : List Value} (hz : TypedV env stateT z) (hk : TypedV env nT k)
    (hc : TypedV env catchesT (.list cs)) (hw : TypedV env valsT (.list ws))
    (hy : TypedV env typeuseT yy) (his : TypedV env instrsT (.list is)) :
    SRead env (cfgV z [.case "HANDLER_%{%}%" (.tuple [k, .list cs,
        .list (ws ++ [.case "RETURN_CALL_REF" yy] ++ is)])])
      (ws ++ [.case "RETURN_CALL_REF" yy]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("k", k), ("catch*", .list cs), ("val*", .list ws),
    ("yy", yy), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fk : ρ.findVal? "k" = some k := rfl
  have fc : ρ.findVal? "catch*" = some (.list cs) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  have er : EvalExp env ρ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fk (hk ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fy (hy ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fk) (evalExp_iterPat (by decide) fc)
          (evalExp_cat (evalExp_cat ev er) (evalExp_iterPat (by decide) fi)))))))
      (evalExp_cat ev er))
    (fun _ h => nomatch h)

/-- `Step_read/return_call_ref-frame-null`. -/
theorem sread_returnCallRefFrameNull {env : Env}
    (h : HasRuleAt env "Step_read" "%~>%" 10 returnCallRefFrameNullRule)
    {z k f yy : Value} {ws is : List Value} (hz : TypedV env stateT z) (hk : TypedV env nT k)
    (hf : TypedV env frameT f) (hw : TypedV env valsT (.list ws))
    (hy : TypedV env typeuseT yy) (his : TypedV env instrsT (.list is)) :
    SRead env (cfgV z [.case "FRAME_%{%}%" (.tuple [k, f,
        .list (ws ++ [caseNilV "REF.NULL_ADDR"] ++ [.case "RETURN_CALL_REF" yy] ++ is)])])
      [caseNilV "TRAP"] := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("k", k), ("f", f), ("val*", .list ws),
    ("yy", yy), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fk : ρ.findVal? "k" = some k := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  have er : EvalExp env ρ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fk (hk ρ hρ) (QuantsOk.cons ff (hf ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fy (hy ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fk) (evalExp_var ff)
          (evalExp_cat (evalExp_cat (evalExp_cat ev (evalExp_list1 evalExp_caseNil)) er)
            (evalExp_iterPat (by decide) fi)))))))
      (evalExp_list1 evalExp_caseNil))
    (fun _ h => nomatch h)

/-- `Step/call_ref-null`. -/
theorem sstep_callRefNull {env : Env} (h : HasRuleAt env "Step" "%~>%" 6 callRefNullRule)
    {z yy : Value} (hz : TypedV env stateT z) (hy : TypedV env typeuseT yy) :
    SStep env (cfgV z [caseNilV "REF.NULL_ADDR", .case "CALL_REF" yy]) (cfgV z [caseNilV "TRAP"]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("yy", yy)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fy (hy ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list2 evalExp_caseNil (evalExp_case (evalExp_var fy)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 evalExp_caseNil))))
    (fun _ h => nomatch h)

/-! ## Call annotations -/

/-- A `RETURN_CALL_REF` in either representation is encoded as `RETURN_CALL_REF yy`. -/
theorem adminToV_of_isReturnCallRef {c : Admin} (hc : c.IsReturnCallRef) :
    ∃ yy, adminToV c = .case "RETURN_CALL_REF" yy := by
  match c, hc with
  | .plain (.returnCallRef _), _ => exact ⟨_, rfl⟩
  | .returnCallRefType _, _ => exact ⟨_, rfl⟩

/-- A `CALL_REF` in either representation is encoded as `CALL_REF yy`. -/
theorem adminToV_of_isCallRef {c : Admin} (hc : c.IsCallRef) :
    ∃ yy, adminToV c = .case "CALL_REF" yy := by
  match c, hc with
  | .plain (.callRef _), _ => exact ⟨_, rfl⟩
  | .callRefType _, _ => exact ⟨_, rfl⟩

/-! ## The forward fields -/

section Fwd

variable {H : Type} {hn : H → String}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Ty : CtrlTyping (simEnv B))

/-- The `Step_read` rules of `simEnv B`. -/
theorem simEnv_readRules (B : Builtins) : Equiv.ExecRead.HasReadRules (simEnv B) := by
  have h := Equiv.ExecRead.hasReadRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- `Step/read`, with access to the typing of the state and both code sequences. -/
theorem fwd_of_sread' {env : Env} (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 1 Equiv.ExecStepRules.readRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : TypedV env stateT (stateV hn s f) → TypedV env instrsT (.list (adminsToV is)) →
      SRead env (configV hn ⟨s, f, is⟩) (adminsToV is')) : FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨-, his'⟩ := (T.config _).1 hc'
  exact sstep_read hr hz his his' (h hz his)

include T Ty in
/-- `Forward.returnCallRefLabel`. -/
theorem fwd_returnCallRefLabel : ∀ {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {vs : List Val} {c : Admin} {rest : List Admin} (_ : c.IsReturnCallRef),
    FwdP (simEnv B) hn ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩ := by
  intro s f k cont vs c rest hc
  obtain ⟨yy, hyy⟩ := adminToV_of_isReturnCallRef hc
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz h => ?_
  obtain ⟨hk, hct, hb⟩ := T.label _ cont _ h
  have hb' : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, hcv⟩ := typedV_list_append.1 hab
  have hy : TypedV (simEnv B) typeuseT yy :=
    Ty.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have key := sread_returnCallRefLabel (simEnv_readRules B).returnCallRefLabel (z := stateV hn s f)
    (k := .num (.natN k)) (cont := instrsToV cont) (ws := adminsToV (vals vs))
    (is := adminsToV rest) hz hk hct (typedV_vals_prefix T (b := []) (by simpa using hv)) hy hrest
  simpa [configV, adminsToV_append, hyy] using key

include T Ty in
/-- `Forward.returnCallRefHandler`. -/
theorem fwd_returnCallRefHandler : ∀ {s : Store H} {f : Frame} {k : Nat} {cs : List Catch}
    {vs : List Val} {c : Admin} {rest : List Admin} (_ : c.IsReturnCallRef),
    FwdP (simEnv B) hn ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩ := by
  intro s f k cs vs c rest hc
  obtain ⟨yy, hyy⟩ := adminToV_of_isReturnCallRef hc
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz h => ?_
  obtain ⟨hk, hcs, hb⟩ := T.handler _ cs _ h
  have hb' : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, hcv⟩ := typedV_list_append.1 hab
  have hy : TypedV (simEnv B) typeuseT yy :=
    Ty.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have key := sread_returnCallRefHandler (simEnv_readRules B).returnCallRefHandler
    (z := stateV hn s f) (k := .num (.natN k)) (cs := cs.map Encode.toValue)
    (ws := adminsToV (vals vs)) (is := adminsToV rest) hz hk hcs
    (typedV_vals_prefix T (b := []) (by simpa using hv)) hy hrest
  simpa [configV, adminsToV_append, hyy] using key

include T Ty in
/-- `Forward.returnCallRefFrameNull`. -/
theorem fwd_returnCallRefFrameNull : ∀ {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val}
    {c : Admin} {rest : List Admin} (_ : c.IsReturnCallRef),
    FwdP (simEnv B) hn ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro s f fi k vs c rest hc
  obtain ⟨yy, hyy⟩ := adminToV_of_isReturnCallRef hc
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz h => ?_
  obtain ⟨hk, hfi, hb⟩ := T.frame _ fi _ h
  have hb' : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ [caseNilV "REF.NULL_ADDR"] ++ [adminToV c] ++
        adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨habc, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hab, hcv⟩ := typedV_list_append.1 habc
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have hy : TypedV (simEnv B) typeuseT yy :=
    Ty.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have key := sread_returnCallRefFrameNull (simEnv_readRules B).returnCallRefFrameNull
    (z := stateV hn s f) (k := .num (.natN k)) (f := frameV fi)
    (ws := adminsToV (vals vs)) (is := adminsToV rest) hz hk hfi
    (typedV_vals_prefix T (b := []) (by simpa using hv)) hy hrest
  simpa [configV, adminsToV_append, hyy] using key

include T Ty in
/-- `Forward.callRefNull`. -/
theorem fwd_callRefNull : ∀ {s : Store H} {f : Frame} {c : Admin} (_ : c.IsCallRef),
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩ := by
  intro s f c hc hcfg _
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, h⟩ := (T.config _).1 hcfg
  have hcv : TypedV (simEnv B) instrT (adminToV c) := typedV_code h c (by simp)
  have hy : TypedV (simEnv B) typeuseT yy := Ty.callRefInv yy (hyy ▸ hcv)
  have key := sstep_callRefNull (hasStepRules_simEnv B).callRefNull hz hy
  simpa [configV, hyy] using key

end Fwd

end Silmaril.Wasm.SpecTec.Sim
