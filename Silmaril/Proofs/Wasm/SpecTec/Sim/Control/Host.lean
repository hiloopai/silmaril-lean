module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.ReturnCall

/-!
# Family C: calling a host function

`Step/call_ref-hostfunc-res` and `Step/call_ref-hostfunc-div`, constructed under the declarative
reading, and the `Forward` fields `callRefHost` and `callRefHostDiv`. `$hostcall` is a primitive of
`B` (the script declares it without clauses); its interface is `CtrlHost`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV valsNPat)
open Silmaril.SpecTec.Equiv.ExecStepRules (callRefHostfuncResRule callRefHostfuncDivRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)

/-- A call whose arguments evaluate. -/
theorem evalExp_callArgs {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {ws : List ArgV}
    {v : Value} (hd : ρ.findDef? x = none) (ha : EvalArgs env ρ args ws)
    (h : Applies env x ws v) : EvalExp env ρ (.callE x args) v :=
  evalExp_callE_iff.2 ((applies_iff_callDef hd ha).1 h)

/-- `$funcinst(s; f)[a] = fi`. -/
theorem evalExp_funcinstEq {env : Env} {ρ : VarEnv} {s f fv : Value} {fs : List Value} {a : Nat}
    (hd : ρ.findDef? "funcinst" = none) (fs₀ : ρ.findVal? "s" = some s)
    (ff : ρ.findVal? "f" = some f) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (ffi : ρ.findVal? "fi" = some fv) (hfs : Applies env "funcinst" [.val (stV s f)] (.list fs))
    (hget : fs[a]? = some fv) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.idxE (.callE "funcinst"
      [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))]) (.varE "a")) (.varE "fi"))
      (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_idxE_iff.2 ⟨_, a, evalExp_callArgs hd
    (Equiv.evalArgs_cons (evalExp_case (evalExp_tup2 (evalExp_var fs₀) (evalExp_var ff)))
      (evalArgs_nil env ρ)) hfs, evalExp_var fa, by simpa [Value.idx?] using hget⟩,
    evalExp_var ffi, by simp [cmpValues]⟩

/-- `fi.CODE = _HOSTFUNC hf`. -/
theorem evalExp_hostCodeEq {env : Env} {ρ : VarEnv} {fv hf : Value}
    (ffi : ρ.findVal? "fi" = some fv) (fh : ρ.findVal? "hf" = some hf)
    (hcode : fv.field? "CODE" = some (.case "_HOSTFUNC" hf)) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "_HOSTFUNC" (.varE "hf")))
      (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_dotE_iff.2 ⟨fv, evalExp_var ffi, hcode⟩,
    evalExp_case (evalExp_var fh), by simp [cmpValues]⟩

/-- `Expand(fi.TYPE, FUNC t_1^n -> t_2^m)`, as a premise. -/
theorem dprem_expandFi {env : Env} {els : Prop} {ρ : VarEnv} {fv ty : Value} {T₁ T₂ : List Value}
    (ffi : ρ.findVal? "fi" = some fv) (hty : fv.field? "TYPE" = some ty)
    (fn : ρ.findVal? "n" = some (.num (.natN T₁.length)))
    (fm : ρ.findVal? "m" = some (.num (.natN T₂.length)))
    (f₁ : ρ.findVal? "t_1*" = some (.list T₁)) (f₂ : ρ.findVal? "t_2*" = some (.list T₂))
    (hex : DDerives env (otherwise env) "Expand" "%~~%" []
      (.tuple [ty, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])])) :
    DPrem env (otherwise env) els ρ (.rulePr "Expand" [] "%~~%" (.tupE [.dotE (.varE "fi") "TYPE",
      .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "n") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2")
        (.mk (.listN (.varE "m") none) [.mk "t_2" (.varE "t_2*")])])])])) :=
  .rulePr (evalArgs_nil _ _)
    (evalExp_tup2 (evalExp_dotE_iff.2 ⟨fv, evalExp_var ffi, hty⟩)
      (evalExp_funcTypePat fn fm f₁ f₂)) hex

/-- `o ∈ $hostcall(_HOSTFUNC hf, s, val^n)`. -/
theorem evalExp_hostcallMem {env : Env} {ρ : VarEnv} {o s hf : Value} {ws os : List Value}
    {oe : Exp} (hd : ρ.findDef? "hostcall" = none) (fs₀ : ρ.findVal? "s" = some s)
    (fh : ρ.findVal? "hf" = some hf) (fn : ρ.findVal? "n" = some (.num (.natN ws.length)))
    (fw : ρ.findVal? "val*" = some (.list ws)) (ho : EvalExp env ρ oe o)
    (hcall : Applies env "hostcall" [.val (.case "_HOSTFUNC" hf), .val s, .val (.list ws)]
      (.list os)) (hmem : o ∈ os) :
    EvalExp env ρ (.memE oe (.callE "hostcall" [.expA (.caseE "_HOSTFUNC" (.varE "hf")),
      .expA (.varE "s"), .expA (.iterE (.varE "val")
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))])) (.bool true) :=
  evalExp_memE_iff.2 ⟨_, _, ho, evalExp_callArgs hd
    (Equiv.evalArgs_cons (evalExp_case (evalExp_var fh))
      (Equiv.evalArgs_cons (evalExp_var fs₀)
        (Equiv.evalArgs_cons (evalExp_iterNVar (by decide) fn fw) (evalArgs_nil env ρ)))) hcall,
    by simp [memValue, hmem]⟩

/-- `Step/call_ref-hostfunc-res`. -/
theorem sstep_callRefHostRes {env : Env} (h : HasRuleAt env "Step" "%~>%" 8 callRefHostfuncResRule)
    {s f yy s' r fv ty hf : Value} {ws fs T₁ T₂ os R : List Value} {a : Nat}
    (hlen : ws.length = T₁.length)
    (hs : TypedV env storeT s) (hf₀ : TypedV env frameT f)
    (hn : TypedV env nT (.num (.natN T₁.length))) (hw : TypedV env valsT (.list ws))
    (ha : TypedV env addrT (.num (.natN a))) (hy : TypedV env typeuseT yy)
    (hs' : TypedV env storeT s') (hr : TypedV env resultT r) (hfi : TypedV env funcinstT fv)
    (h₁ : TypedV env valtypesT (.list T₁)) (hm : TypedV env mT (.num (.natN T₂.length)))
    (h₂ : TypedV env valtypesT (.list T₂)) (hhf : TypedV env .textT hf)
    (hfs : Applies env "funcinst" [.val (stV s f)] (.list fs)) (hget : fs[a]? = some fv)
    (hty : fv.field? "TYPE" = some ty) (hcode : fv.field? "CODE" = some (.case "_HOSTFUNC" hf))
    (hex : DDerives env (otherwise env) "Expand" "%~~%" []
      (.tuple [ty, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])]))
    (hcall : Applies env "hostcall" [.val (.case "_HOSTFUNC" hf), .val s, .val (.list ws)]
      (.list os)) (hmem : .case "RES" (.tuple [s', r]) ∈ os)
    (hlift : Applies env "lift_result" [.val r] (.list R)) :
    SStep env (cfgV (stV s f) (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy]))
      (cfgV (stV s' f) R) := by
  let ρ := VarEnv.empty.bindVals [("s", s), ("f", f), ("n", .num (.natN T₁.length)),
    ("val*", .list ws), ("a", .num (.natN a)), ("yy", yy), ("s'", s'), ("result", r), ("fi", fv),
    ("t_1*", .list T₁), ("m", .num (.natN T₂.length)), ("t_2*", .list T₂), ("hf", hf)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fs₀ : ρ.findVal? "s" = some s := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN T₁.length)) := rfl
  have fw : ρ.findVal? "val*" = some (.list ws) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have fs' : ρ.findVal? "s'" = some s' := rfl
  have fr : ρ.findVal? "result" = some r := rfl
  have ffi : ρ.findVal? "fi" = some fv := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list T₁) := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN T₂.length)) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list T₂) := rfl
  have fh : ρ.findVal? "hf" = some hf := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) (hlen ▸ fn) fw
  have ehost : EvalExp env ρ (.memE (.caseE "RES" (.tupE [.varE "s'", .varE "result"]))
      (.callE "hostcall" [.expA (.caseE "_HOSTFUNC" (.varE "hf")), .expA (.varE "s"),
        .expA (.iterE (.varE "val") (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))]))
      (.bool true) :=
    evalExp_hostcallMem rfl fs₀ fh (hlen ▸ fn) fw
      (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var fr))) hcall hmem
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fs₀ (hs ρ hρ) (QuantsOk.cons ff (hf₀ ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons fw (hw ρ hρ) (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fy (hy ρ hρ)
      (QuantsOk.cons fs' (hs' ρ hρ) (QuantsOk.cons fr (hr ρ hρ) (QuantsOk.cons ffi (hfi ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons fm (hm ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ)
      (QuantsOk.cons fh (hhf ρ hρ) QuantsOk.nil)))))))))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs₀) (evalExp_var ff)))
        (evalExp_cat evn (evalExp_list2 (evalExp_case (evalExp_var fa))
          (evalExp_case (evalExp_var fy))))))
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff)))
        (evalExp_call1 rfl fr hlift))))
    (fun pr hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl | rfl
      · exact .ifPr (evalExp_funcinstEq rfl fs₀ ff fa ffi hfs hget)
      · exact dprem_expandFi ffi hty fn fm f₁ f₂ hex
      · exact .ifPr (evalExp_hostCodeEq ffi fh hcode)
      · exact .ifPr ehost)

/-- `Step/call_ref-hostfunc-div`. -/
theorem sstep_callRefHostDiv {env : Env} (h : HasRuleAt env "Step" "%~>%" 9 callRefHostfuncDivRule)
    {s f yy fv ty hf : Value} {ws fs T₁ T₂ os : List Value} {a : Nat}
    (hlen : ws.length = T₁.length)
    (hs : TypedV env storeT s) (hf₀ : TypedV env frameT f)
    (hn : TypedV env nT (.num (.natN T₁.length))) (hw : TypedV env valsT (.list ws))
    (ha : TypedV env addrT (.num (.natN a))) (hy : TypedV env typeuseT yy)
    (hfi : TypedV env funcinstT fv)
    (h₁ : TypedV env valtypesT (.list T₁)) (hm : TypedV env mT (.num (.natN T₂.length)))
    (h₂ : TypedV env valtypesT (.list T₂)) (hhf : TypedV env .textT hf)
    (hfs : Applies env "funcinst" [.val (stV s f)] (.list fs)) (hget : fs[a]? = some fv)
    (hty : fv.field? "TYPE" = some ty) (hcode : fv.field? "CODE" = some (.case "_HOSTFUNC" hf))
    (hex : DDerives env (otherwise env) "Expand" "%~~%" []
      (.tuple [ty, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])]))
    (hcall : Applies env "hostcall" [.val (.case "_HOSTFUNC" hf), .val s, .val (.list ws)]
      (.list os)) (hmem : .case "BOT" (.tuple []) ∈ os) :
    SStep env (cfgV (stV s f) (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy]))
      (cfgV (stV s f) (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy])) := by
  let ρ := VarEnv.empty.bindVals [("s", s), ("f", f), ("n", .num (.natN T₁.length)),
    ("val*", .list ws), ("a", .num (.natN a)), ("yy", yy), ("fi", fv),
    ("t_1*", .list T₁), ("m", .num (.natN T₂.length)), ("t_2*", .list T₂), ("hf", hf)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fs₀ : ρ.findVal? "s" = some s := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN T₁.length)) := rfl
  have fw : ρ.findVal? "val*" = some (.list ws) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have ffi : ρ.findVal? "fi" = some fv := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list T₁) := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN T₂.length)) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list T₂) := rfl
  have fh : ρ.findVal? "hf" = some hf := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) (hlen ▸ fn) fw
  have elhs : EvalExp env ρ (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]),
      .catE (valsNPat "val" "val*" "n") (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"),
        .caseE "CALL_REF" (.varE "yy")])]))
      (cfgV (stV s f) (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy])) :=
    evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs₀) (evalExp_var ff)))
      (evalExp_cat evn (evalExp_list2 (evalExp_case (evalExp_var fa))
        (evalExp_case (evalExp_var fy)))))
  have ehost : EvalExp env ρ (.memE (.caseE "BOT" (.tupE []))
      (.callE "hostcall" [.expA (.caseE "_HOSTFUNC" (.varE "hf")), .expA (.varE "s"),
        .expA (.iterE (.varE "val") (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))]))
      (.bool true) :=
    evalExp_hostcallMem rfl fs₀ fh (hlen ▸ fn) fw evalExp_caseNil hcall hmem
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fs₀ (hs ρ hρ) (QuantsOk.cons ff (hf₀ ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons fw (hw ρ hρ) (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fy (hy ρ hρ)
      (QuantsOk.cons ffi (hfi ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons fm (hm ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ)
      (QuantsOk.cons fh (hhf ρ hρ) QuantsOk.nil)))))))))))
    (evalExp_tup2 elhs elhs)
    (fun pr hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl | rfl
      · exact .ifPr (evalExp_funcinstEq rfl fs₀ ff fa ffi hfs hget)
      · exact dprem_expandFi ffi hty fn fm f₁ f₂ hex
      · exact .ifPr (evalExp_hostCodeEq ffi fh hcode)
      · exact .ifPr ehost)

/-- A text is a `text`. -/
theorem typedV_text {env : Env} (x : String) : TypedV env .textT (.text x) :=
  fun _ _ => ⟨1, by simp [hasTyp, Value.asText?]⟩

section Fwd

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {host : HostSemantics H}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Tg : CtrlTyping (simEnv B))
  (S : CtrlState (simEnv B) hn) (C : CtrlCall (simEnv B)) (Hs : CtrlHost (simEnv B) hn host)

/-- The code field of a host function instance. -/
theorem funcInstV_code_host {fi : FuncInst H} {h : H} (hc : fi.code = .host h) :
    (funcInstV hn fi).field? "CODE" = some (.case "_HOSTFUNC" (.text (hn h))) := by
  simp [funcInstV, Value.field?, hc]

include T Tg S C Hs in
/-- `Forward.callRefHost`. -/
theorem fwd_callRefHost : ∀ {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result} (_ : c.IsCallRef)
    (_ : s.funcs[a]? = some fi) (_ : Expand fi.type (.func ps rs)) (_ : vs.length = ps.length)
    (_ : fi.code = .host h) (_ : host h s vs (.returned s' r)),
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ := by
  intro s s' f c vs a fi ps rs h r hc hfa hex hlen hcode hhost hc₁ hc₂
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨hz', hres⟩ := (T.config _).1 hc₂
  obtain ⟨hst, hfr⟩ := (T.state _ _).1 hz
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  obtain ⟨os, hcall, hall⟩ := Hs.hostcall h s vs
  have hcv : TypedV (simEnv B) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv B) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv B) "hostcall" [.val (.case "_HOSTFUNC" (.text (hn h))),
      .val (storeV hn s), .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostRes (hasStepRules_simEnv B).callRefHostfuncRes
    (fs := s.funcs.map (funcInstV hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy hst' (Hs.result r hres) (Hs.funcinst s a fi hst hfa)
    (C.valtypes ps) (Tg.natM _) (C.valtypes rs) (typedV_text (hn h)) (S.funcinst s f)
    (funcs_getElem_map hfa) rfl (funcInstV_code_host hcode) (C.expand _ _ _ hex) hcall'
    (hall _ hhost) (Hs.liftResult r)
  simpa [configV, stateV, adminsToV_append, hyy] using key

include T Tg S C Hs in
/-- `Forward.callRefHostDiv`. -/
theorem fwd_callRefHostDiv : ∀ {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} (_ : c.IsCallRef)
    (_ : s.funcs[a]? = some fi) (_ : Expand fi.type (.func ps rs)) (_ : vs.length = ps.length)
    (_ : fi.code = .host h) (_ : host h s vs .diverged),
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ := by
  intro s f c vs a fi ps rs h hc hfa hex hlen hcode hhost hc₁ _
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨hst, hfr⟩ := (T.state _ _).1 hz
  obtain ⟨os, hcall, hall⟩ := Hs.hostcall h s vs
  have hcv : TypedV (simEnv B) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv B) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv B) "hostcall" [.val (.case "_HOSTFUNC" (.text (hn h))),
      .val (storeV hn s), .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostDiv (hasStepRules_simEnv B).callRefHostfuncDiv
    (fs := s.funcs.map (funcInstV hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (Hs.funcinst s a fi hst hfa)
    (C.valtypes ps) (Tg.natM _) (C.valtypes rs) (typedV_text (hn h)) (S.funcinst s f)
    (funcs_getElem_map hfa) rfl (funcInstV_code_host hcode) (C.expand _ _ _ hex) hcall'
    (hall _ hhost)
  simpa [configV, stateV, adminsToV_append, hyy] using key

end Fwd

end Silmaril.Wasm.SpecTec.Sim
