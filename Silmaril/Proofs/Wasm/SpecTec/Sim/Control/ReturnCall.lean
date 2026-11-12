module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Call

/-!
# Family C: `return_call_ref` leaving a frame, and Core's annotation deviation

`Step_read/return_call_ref-frame-addr` turns `RETURN_CALL_REF yy` into `CALL_REF yy`, keeping the
annotation. Core's `Step.returnCallRefFrameAddr` instead produces `c.retToCallIn fi.module`, which
resolves an index annotation `y` against the exited frame's module. Both call rules ignore the
annotation, but the images differ, so the `Forward.returnCallRefFrameAddr` field is **false** as
stated whenever `c = RETURN_CALL_REF y` and `fi.module.types[y]? = some d`
(`adminToV_retToCallIn_ne`).

What is proved:

* `sread_returnCallRefFrameAddr`: the SpecTec rule, constructed declaratively;
* `fwd_returnCallRefFrameAddr_retToCall`: SpecTec steps to the image of Core's successor with
  `c.retToCall` (SpecTec's own result) in place of `c.retToCallIn fi.module`;
* `fwd_returnCallRefFrameAddr_of`: the `Forward` field itself, whenever the two agree
  (`c` already carries a defined type, or the index does not resolve);
* `retToCallIn_isCallRef`, `retToCall_isCallRef`: the two results differ only in a `CALL_REF`
  annotation, which every Core call rule ignores (`Admin.IsCallRef`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.Execution
  (pctV caseNilV valsPat valsNPat iterPat evalExp_iterPat evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecRead (returnCallRefFrameAddrRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)

/-- `FUNC %(t_1^n) -> %(t_2^m)`, evaluated. -/
theorem evalExp_funcTypePat {env : Env} {ρ : VarEnv} {T₁ T₂ : List Value}
    (fn : ρ.findVal? "n" = some (.num (.natN T₁.length)))
    (fm : ρ.findVal? "m" = some (.num (.natN T₂.length)))
    (f₁ : ρ.findVal? "t_1*" = some (.list T₁)) (f₂ : ρ.findVal? "t_2*" = some (.list T₂)) :
    EvalExp env ρ (.caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "n") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2")
        (.mk (.listN (.varE "m") none) [.mk "t_2" (.varE "t_2*")])])]))
      (.case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]), .case "%" (.tuple [.list T₂])])) :=
  evalExp_case (evalExp_tup2
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_iterNVar (by decide) fn f₁)
      evalExps_nil, rfl⟩))
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_iterNVar (by decide) fm f₂)
      evalExps_nil, rfl⟩)))

/-- `Step_read/return_call_ref-frame-addr`. -/
theorem sread_returnCallRefFrameAddr {env : Env}
    (h : HasRuleAt env "Step_read" "%~>%" 11 returnCallRefFrameAddrRule)
    {z k f yy fv ty : Value} {ws' ws is fs T₁ T₂ : List Value} {a : Nat}
    (hlen : ws.length = T₁.length)
    (hz : TypedV env stateT z) (hk : TypedV env nT k) (hf : TypedV env frameT f)
    (hw' : TypedV env valsT (.list ws')) (hn : TypedV env nT (.num (.natN T₁.length)))
    (hw : TypedV env valsT (.list ws)) (ha : TypedV env addrT (.num (.natN a)))
    (hy : TypedV env typeuseT yy) (his : TypedV env instrsT (.list is))
    (h₁ : TypedV env valtypesT (.list T₁)) (hm : TypedV env mT (.num (.natN T₂.length)))
    (h₂ : TypedV env valtypesT (.list T₂))
    (hfs : Applies env "funcinst" [.val z] (.list fs)) (hget : fs[a]? = some fv)
    (hty : fv.field? "TYPE" = some ty)
    (hex : DDerives env (otherwise env) "Expand" "%~~%" []
      (.tuple [ty, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])])) :
    SRead env (cfgV z [.case "FRAME_%{%}%" (.tuple [k, f,
        .list (ws' ++ ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a))] ++
          [.case "RETURN_CALL_REF" yy] ++ is)])])
      (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("k", k), ("f", f), ("val'*", .list ws'),
    ("n", .num (.natN T₁.length)), ("val*", .list ws), ("a", .num (.natN a)), ("yy", yy),
    ("instr*", .list is), ("t_1*", .list T₁), ("m", .num (.natN T₂.length)), ("t_2*", .list T₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fk : ρ.findVal? "k" = some k := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fv' : ρ.findVal? "val'*" = some (.list ws') := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN T₁.length)) := rfl
  have fw : ρ.findVal? "val*" = some (.list ws) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list T₁) := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN T₂.length)) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list T₂) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) (hlen ▸ fn) fw
  have era : EvalExp env ρ (.caseE "REF.FUNC_ADDR" (.varE "a"))
      (.case "REF.FUNC_ADDR" (.num (.natN a))) := evalExp_case (evalExp_var fa)
  have ety : EvalExp env ρ (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
      "TYPE") ty :=
    evalExp_dotE_iff.2 ⟨fv, evalExp_idxE_iff.2 ⟨_, a, evalExp_call1 rfl fz hfs,
      evalExp_var fa, by simpa [Value.idx?] using hget⟩, hty⟩
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fk (hk ρ hρ) (QuantsOk.cons ff (hf ρ hρ)
      (QuantsOk.cons fv' (hw' ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fw (hw ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fy (hy ρ hρ) (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons fm (hm ρ hρ)
      (QuantsOk.cons f₂ (h₂ ρ hρ) QuantsOk.nil))))))))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fk) (evalExp_var ff)
          (evalExp_cat (evalExp_cat (evalExp_cat (evalExp_cat
            (evalExp_valsPat (by decide) fv') evn) (evalExp_list1 era))
            (evalExp_list1 (evalExp_case (evalExp_var fy))))
            (evalExp_iterPat (by decide) fi)))))))
      (evalExp_cat evn (evalExp_list2 era (evalExp_case (evalExp_var fy)))))
    (prems_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup2 ety (evalExp_funcTypePat fn fm f₁ f₂)) hex))

section Fwd

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

/-! ## The annotation deviation -/

/-- Core's result is a `CALL_REF` in either representation. -/
theorem retToCallIn_isCallRef {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    (c.retToCallIn m).IsCallRef := by
  match c, hc with
  | .plain (.returnCallRef y), _ =>
      simp only [Admin.retToCallIn]
      split <;> trivial
  | .returnCallRefType _, _ => trivial

/-- So is SpecTec's. -/
theorem retToCall_isCallRef {c : Admin} (hc : c.IsReturnCallRef) : c.retToCall.IsCallRef := by
  match c, hc with
  | .plain (.returnCallRef _), _ => trivial
  | .returnCallRefType _, _ => trivial

/-- **The deviation is real.** An index annotation that resolves in the exited frame's module
gives a different image from SpecTec's `CALL_REF yy`. -/
theorem adminToV_retToCallIn_ne {m : ModuleInst} {y : TypeIdx} {d : DefType}
    (hd : m.types[y.toNat]? = some d) :
    adminToV ((Admin.plain (.returnCallRef y)).retToCallIn m) ≠
      adminToV (Admin.plain (.returnCallRef y)).retToCall := by
  simp only [Admin.retToCallIn, hd, Admin.retToCall]
  cases d with
  | defn g i =>
    intro h
    have h' : Value.case "CALL_REF" (.case "_DEF" (.tuple [tyV g, .num (.natN i)])) =
        .case "CALL_REF" (.case "_IDX" (Encode.toValue y)) := h
    simp at h'

/-- The image of `RETURN_CALL_REF yy` and of the `CALL_REF yy` SpecTec turns it into. -/
theorem adminToV_retToCall {c : Admin} (hc : c.IsReturnCallRef) :
    ∃ yy, adminToV c = .case "RETURN_CALL_REF" yy ∧ adminToV c.retToCall = .case "CALL_REF" yy := by
  match c, hc with
  | .plain (.returnCallRef _), _ => exact ⟨_, rfl, rfl⟩
  | .returnCallRefType _, _ => exact ⟨_, rfl, rfl⟩

/-! ## The forward step -/

variable {H : Type} {hn : H → String}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Tg : CtrlTyping (simEnv B))
  (S : CtrlState (simEnv B) hn) (C : CtrlCall (simEnv B))

include T Tg S C in
/-- `Step.returnCallRefFrameAddr` with SpecTec's result `c.retToCall`: the SpecTec rule steps to
the image of Core's successor up to the call annotation. -/
theorem fwd_returnCallRefFrameAddr_retToCall : ∀ {s : Store H} {f fi : Frame} {k : Nat}
    {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
    {ps rs : Ty (.list .val)} (_ : c.IsReturnCallRef) (_ : s.funcs[a]? = some fn)
    (_ : Expand fn.type (.func ps rs)) (_ : vs.length = ps.length),
    FwdP (simEnv B) hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩ := by
  intro s f fi k vs' vs a c rest fn ps rs hc hfn hex hlen
  obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz h => ?_
  obtain ⟨hk, hfi, hb⟩ := T.frame _ fi _ h
  have hb' : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs') ++ adminsToV (vals vs) ++ [adminToV (.ref (.func a))] ++
        [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨habcd, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨habc, hcv⟩ := typedV_list_append.1 habcd
  obtain ⟨hab, -⟩ := typedV_list_append.1 habc
  obtain ⟨hv', hv⟩ := typedV_list_append.1 hab
  have hy : TypedV (simEnv B) typeuseT yy :=
    Tg.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have key := sread_returnCallRefFrameAddr (simEnv_readRules B).returnCallRefFrameAddr
    (z := stateV hn s f) (k := .num (.natN k)) (f := frameV fi) (ws' := adminsToV (vals vs'))
    (is := adminsToV rest) (fs := s.funcs.map (funcInstV hn)) (fv := funcInstV hn fn)
    (ty := CT.defType fn.type) (a := a) hw hz hk hfi
    (typedV_vals_prefix T (b := []) (by simpa using hv')) (Tg.nat _)
    (typedV_vals_prefix T (b := []) (by simpa using hv)) (Tg.addr a) hy hrest
    (C.valtypes ps) (Tg.natM _) (C.valtypes rs) (S.funcinst s f) (funcs_getElem_map hfn) rfl
    (C.expand _ _ _ hex)
  simpa [configV, adminsToV_append, hyy, hyy'] using key

include T Tg S C in
/-- **`Forward.returnCallRefFrameAddr`, where Core and SpecTec agree**: whenever resolving the
annotation in the exited frame's module does not change its image (always for a `c` that already
carries a defined type). -/
theorem fwd_returnCallRefFrameAddr_of : ∀ {s : Store H} {f fi : Frame} {k : Nat}
    {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
    {ps rs : Ty (.list .val)} (_ : c.IsReturnCallRef) (_ : s.funcs[a]? = some fn)
    (_ : Expand fn.type (.func ps rs)) (_ : vs.length = ps.length)
    (_ : adminToV (c.retToCallIn fi.module) = adminToV c.retToCall),
    FwdP (simEnv B) hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  intro s f fi k vs' vs a c rest fn ps rs hc hfn hex hlen heq hc₁ hc₂
  have hc₂' : Typed (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩ := by
    simpa [Typed, configV, adminsToV_append, heq] using hc₂
  have key := fwd_returnCallRefFrameAddr_retToCall B T Tg S C hc hfn hex hlen hc₁ hc₂'
  simpa [configV, adminsToV_append, heq] using key

end Fwd

end Silmaril.Wasm.SpecTec.Sim
