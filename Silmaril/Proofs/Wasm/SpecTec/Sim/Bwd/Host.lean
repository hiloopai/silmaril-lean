module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.CallFunc

/-!
# Host calls (`Step` 8, 9)

`bwd_callRefHost` and `bwd_callRefHostDiv` are the `Backward.step 8`/`9` fields. On top of what
`call_ref-func` needs, the host premise `RES s' result ∈ $hostcall(…)` (resp. `BOT ∈ …`) is read
back through `HostInv` (`$hostcall` returns only outcomes the host allows; assumed, it is the
soundness half of the primitive `B` must provide), and `$lift_result` through family C's
`CtrlHost.liftResult` (taken as `CtrlLift`, to which `CtrlHost` coerces).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- `(s; f); e`, read back. -/
theorem cfgSt_inv {env : Env} {ρ : VarEnv} {xs xf : IL.Id} {e : Exp} {sv fv v : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE xs, .varE xf]), e])) v)
    (fs : ρ.findVal? xs = some sv) (ff : ρ.findVal? xf = some fv) :
    ∃ x, EvalExp env ρ e x ∧ v = .case "%;%" (.tuple [stV sv fv, x]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨w₁, w₂, h₁, h₂, rfl⟩ := tup2_inv hu
  have e₁ : w₁ = stV sv fv :=
    EvalExp.unique h₁ (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff)))
  exact ⟨w₂, h₂, by rw [e₁]⟩

variable (B : Builtins)

/-- `$funcinst(e)[a] = fi`, read back, for an argument expression `e` denoting a state. -/
theorem funcinst_of_eval' (S : CtrlReads (simEnv B) hn) {s : Store H} {f : Frame} {ρ : VarEnv}
    {ez : Exp} {addr : Nat} {fv : Value} (hd : ρ.findDef? "funcinst" = none)
    (hz : EvalExp (simEnv B) ρ ez (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN addr))) (ffi : ρ.findVal? "fi" = some fv)
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.idxE (.callE "funcinst" [.expA ez]) (.varE "a")) (.varE "fi")) (.bool true)) :
    ∃ fn, s.funcs[addr]? = some fn ∧ fv = funcInstV hn fn := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have ev : v = fv := EvalExp.unique h₂ (evalExp_var ffi)
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 h₁
  have hap : Applies (simEnv B) "funcinst" [.val (stateV hn s f)] wl :=
    (applies_iff_callDef hd (Equiv.evalArgs_cons hz (evalArgs_nil _ ρ))).2 (evalExp_callE_iff.1 hwl)
  have ewl : wl = .list (s.funcs.map (funcInstV hn)) :=
    Equiv.ExecNumeric.Applies.unique hap (S.funcinst s f)
  have ei : Value.num (.natN i) = .num (.natN addr) := EvalExp.unique hi (evalExp_var fa)
  have hget : (s.funcs.map (funcInstV hn))[addr]? = some v := by
    rw [← natN_inj ei]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fn, hfn, hfv⟩ := Option.map_eq_some_iff.1 hget
  exact ⟨fn, hfn, by rw [← ev, ← hfv]⟩

/-- `fi.CODE = _HOSTFUNC hf`, read back at the image of a function instance. -/
theorem hostCode_of_eval {env : Env} {ρ : VarEnv} {fn : FuncInst H} {hfv : Value}
    (ffi : ρ.findVal? "fi" = some (funcInstV hn fn)) (fh : ρ.findVal? "hf" = some hfv)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE")
      (.caseE "_HOSTFUNC" (.varE "hf"))) (.bool true)) :
    ∃ hh, fn.code = .host hh ∧ hfv = .text (hn hh) := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have e₂ : v = .case "_HOSTFUNC" hfv := EvalExp.unique h₂ (evalExp_case (evalExp_var fh))
  obtain ⟨fv, hfv', hfld⟩ := evalExp_dotE_iff.1 h₁
  have efv : fv = funcInstV hn fn := EvalExp.unique hfv' (evalExp_var ffi)
  rw [efv, e₂] at hfld
  cases hc : fn.code with
  | wasm code => simp [funcInstV, Value.field?, hc] at hfld
  | host hh =>
    simp only [funcInstV, Value.field?, hc] at hfld
    simp only [List.find?] at hfld
    exact ⟨hh, rfl, (Value.case.inj (Option.some.inj hfld)).2.symm⟩

/-- `o ∈ $hostcall(_HOSTFUNC hf, s, val^n)`, read back through `HostInv`. -/
theorem hostMem_of_eval (Hi : HostInv (simEnv B) hn host) {ρ : VarEnv} {s₀ : Store H} {hh : H}
    {vs : List Val} {oe : Exp} {o : Value} (hd : ρ.findDef? "hostcall" = none)
    (fs : ρ.findVal? "s" = some (storeV hn s₀)) (fh : ρ.findVal? "hf" = some (.text (hn hh)))
    (fn : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (fw : ρ.findVal? "val*" = some (.list (vs.map valV))) (ho : EvalExp (simEnv B) ρ oe o)
    (h : EvalExp (simEnv B) ρ (.memE oe (.callE "hostcall" [.expA (.caseE "_HOSTFUNC" (.varE "hf")),
      .expA (.varE "s"), .expA (.iterE (.varE "val")
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))])) (.bool true)) :
    ∃ out, host hh s₀ vs out ∧ o = outcomeV hn out := by
  obtain ⟨v₁, v₂, h₁, h₂, hm⟩ := evalExp_memE_iff.1 h
  have e₁ : v₁ = o := EvalExp.unique h₁ ho
  have hap : Applies (simEnv B) "hostcall" [.val (.case "_HOSTFUNC" (.text (hn hh))),
      .val (storeV hn s₀), .val (.list (vs.map valV))] v₂ :=
    (applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_case (evalExp_var fh))
      (Equiv.evalArgs_cons (evalExp_var fs) (Equiv.evalArgs_cons
        (evalExp_iterNVar (by decide) fn fw) (evalArgs_nil _ ρ))))).2 (evalExp_callE_iff.1 h₂)
  exact Hi.hostcall hh s₀ vs v₂ o hap (e₁ ▸ hm)

/-- The parts of the host calls' left-hand side, read back. -/
structure HostLhs (s : Store H) (f : Frame) (code : List Admin) (ρ : VarEnv) : Prop where
  /-- The code is `vals vs ++ [REF.FUNC_ADDR a, c]`. -/
  shape : ∃ vs addr c, code = vals vs ++ [.ref (.func addr), c] ∧ c.IsCallRef ∧
    ρ.findVal? "a" = some (.num (.natN addr)) ∧
    ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)) ∧
    ρ.findVal? "val*" = some (.list (vs.map valV))
  /-- The state variables. -/
  state : ρ.findVal? "s" = some (storeV hn s) ∧ ρ.findVal? "f" = some (frameV f)

/-- The left-hand side `(s; f); val^n (REF.FUNC_ADDR a) (CALL_REF yy)` of the host-call rules,
decoded. -/
theorem hostLhs_of {env : Env} (D : CtrlDecode env) {σ : List (IL.Id × Value)} {s : Store H}
    {f : Frame} {code : List Admin} {sv fv av yy : Value}
    (fs : (VarEnv.empty.bindVals σ).findVal? "s" = some sv)
    (ff : (VarEnv.empty.bindVals σ).findVal? "f" = some fv)
    (fa : (VarEnv.empty.bindVals σ).findVal? "a" = some av)
    (fy : (VarEnv.empty.bindVals σ).findVal? "yy" = some yy)
    (htv : ∀ ws, (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) →
      HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws))
    (hl : EvalExp env (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.caseE "%;%"
      (.tupE [.varE "s", .varE "f"]), .catE (valsNPat "val" "val*" "n")
        (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"), .caseE "CALL_REF" (.varE "yy")])]))
      (configV hn ⟨s, f, code⟩)) :
    HostLhs (hn := hn) s f code (VarEnv.empty.bindVals σ) := by
  obtain ⟨x, hx, hc⟩ := cfgSt_inv hl fs ff
  have e₀ : stateV hn s f = stV sv fv ∧ Value.list (adminsToV code) = x :=
    tuple2_inj (Value.case.inj hc).2
  have es : storeV hn s = sv ∧ frameV f = fv := stV_inj (stateV_eq hn s f ▸ e₀.1)
  obtain ⟨ws, fw, fn, hcode⟩ := valsN_cat (e₀.2.symm ▸ hx)
    (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fy)))
  obtain ⟨l₀, rest, rfl, h₀, hrest⟩ := Exn.adminsToV_eq_append (Value.list.inj hcode)
  obtain ⟨vs, rfl, -⟩ := decode_vals D h₀ (htv ws fw)
  obtain ⟨b, c₀, rfl, hb, hc₀⟩ := adminsToV_eq_pair hrest
  obtain ⟨addr, rfl, hav⟩ := decode_refFuncAddr hb
  have hws : ws = vs.map valV := by rw [← h₀, adminsToV_vals]
  exact ⟨⟨vs, addr, c₀, rfl, D.callRef c₀ _ hc₀, hav ▸ fa, hws ▸ fn, hws ▸ fw⟩,
    es.1.symm ▸ fs, es.2.symm ▸ ff⟩

section Bwd

variable (D : CtrlDecode (simEnv B)) (S : CtrlReads (simEnv B) hn)
  (Hs : CtrlLift (simEnv B)) (Hi : HostInv (simEnv B) hn host) (Ci : CallInv (simEnv B))

/-- The `val*` quantifier is typed at whatever list it is bound to. -/
theorem valsTyped_of {env : Env} {ρ : VarEnv} {qs : List Param}
    (hq : QuantsOk env ρ qs) (hm : Param.expP "val*" (.iterT (.varT "val" []) .list) ∈ qs) :
    ∀ ws, ρ.findVal? "val*" = some (.list ws) → HasTyp env ρ valsT (.list ws) := fun ws hw => by
  obtain ⟨ws', fv', ht⟩ := quant_list hq hm
  have e : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans hw))
  exact e ▸ ht

/-- An outcome image headed `RES`. -/
theorem outcome_res {out : Execution.Host.Outcome (Store H) Result} {sv rv : Value}
    (h : Value.case "RES" (.tuple [sv, rv]) = outcomeV hn out) :
    ∃ s₂ r, out = .returned s₂ r ∧ sv = storeV hn s₂ ∧ rv = resultV r := by
  cases out with
  | returned s₂ r =>
    have e := tuple2_inj (Value.case.inj h).2
    exact ⟨s₂, r, rfl, e.1, e.2⟩
  | diverged => exact absurd (Value.case.inj h).1 (by decide)

/-- An outcome image headed `BOT`. -/
theorem outcome_bot {out : Execution.Host.Outcome (Store H) Result}
    (h : caseNilV "BOT" = outcomeV hn out) : out = .diverged := by
  cases out with
  | returned s₂ r => exact absurd (Value.case.inj h).1 (by decide)
  | diverged => rfl

include S Ci in
/-- The first three premises of the host-call rules, read back. -/
theorem hostPrems {D' : Interp} {els : Prop} {ρ : VarEnv} {s : Store H} {f : Frame}
    {addr : Nat} {vs : List Val} {fiv hfv : Value} (hd : ρ.findDef? "funcinst" = none)
    (fs : ρ.findVal? "s" = some (storeV hn s)) (ff : ρ.findVal? "f" = some (frameV f))
    (fa : ρ.findVal? "a" = some (.num (.natN addr))) (ffi : ρ.findVal? "fi" = some fiv)
    (fh : ρ.findVal? "hf" = some hfv)
    (fn : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (h₁ : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.idxE (.callE "funcinst"
      [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))]) (.varE "a")) (.varE "fi")) (.bool true))
    (h₂ : PremW (simEnv B) D' els ρ (.rulePr "Expand" [] "%~~%" (.tupE [.dotE (.varE "fi") "TYPE",
      .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "n") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2")
        (.mk (.listN (.varE "m") none) [.mk "t_2" (.varE "t_2*")])])])])))
    (hexp : ∀ w, D' "Expand" "%~~%" [] w → DDerives (simEnv B) (otherwise (simEnv B))
      "Expand" "%~~%" [] w)
    (h₃ : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE")
      (.caseE "_HOSTFUNC" (.varE "hf"))) (.bool true)) :
    ∃ fn₀ ps rs hh, s.funcs[addr]? = some fn₀ ∧ fiv = funcInstV hn fn₀ ∧
      Expand fn₀.type (.func ps rs) ∧ vs.length = ps.length ∧ fn₀.code = .host hh ∧
      hfv = .text (hn hh) := by
  have hz : EvalExp (simEnv B) ρ (.caseE "%;%" (.tupE [.varE "s", .varE "f"])) (stateV hn s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  obtain ⟨fn₀, hfn, rfl⟩ := funcinst_of_eval' B S hd hz fa ffi h₁
  obtain ⟨w', hw', hd'⟩ := rulePrem_inv h₂
  obtain ⟨ty, ftv, hty, hft, rfl⟩ := tup2_inv hw'
  obtain ⟨T₁, T₂, fn₁, -, rfl⟩ := funcTypePat_inv hft
  have hE : DDerives (simEnv B) (otherwise (simEnv B)) "Expand" "%~~%" []
      (.tuple [CT.defType fn₀.type, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])]) := funcInstV_type_of_eval ffi hty ▸ hexp _ hd'
  obtain ⟨ps, rs, hex, hl₁, -⟩ := Ci.expand fn₀.type T₁ T₂ hE
  obtain ⟨hh, hcode₀, rfl⟩ := hostCode_of_eval ffi fh h₃
  have hnl : vs.length = ps.length := by
    rw [← hl₁, ← List.length_map (f := valV)]
    exact natN_inj (Option.some.inj (fn.symm.trans fn₁))
  exact ⟨fn₀, ps, rs, hh, hfn, rfl, hex, hnl, hcode₀, rfl⟩

include D S Hs Hi Ci in
/-- **`Backward.step 8`** (`call_ref-hostfunc-res`). -/
theorem bwd_callRefHost : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step" 8 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (hasStepRules_simEnv B).callRefHostfuncRes hf)
  obtain ⟨sv, fs, -⟩ := quant_of (x := "s") (t := storeT) hq (.head _)
  obtain ⟨fv, ff, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := addrT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hlr := Exn.evalExp_tup2_inv he
  have hL : HostLhs (hn := hn) s f code (VarEnv.empty.bindVals σ) :=
    hostLhs_of D fs ff fa fy (valsTyped_of hq (.tail _ (.tail _ (.tail _ (.head _))))) hlr.1
  obtain ⟨⟨vs, addr, c₀, rfl, hcr, fa', fn, fw⟩, fs', ff'⟩ := hL
  obtain ⟨s'v, fs'', -⟩ := quant_of (x := "s'") (t := storeT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨rv, fr, -⟩ := quant_of (x := "result") (t := resultT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  obtain ⟨fiv, ffi, -⟩ := quant_of (x := "fi") (t := funcinstT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
  obtain ⟨hfv, fh, -⟩ := quant_of (x := "hf") (t := .textT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
  obtain ⟨fn₀, ps, rs, hh, hfn, -, hex, hnl, hcode₀, hhv⟩ := hostPrems B S Ci rfl fs' ff' fa'
    ffi fh fn (ifPrem (hp _ (.head _))) (hp _ (.tail _ (.head _))) (fun _ h => h) (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have hres : EvalExp (simEnv B) _ (.caseE "RES" (.tupE [.varE "s'", .varE "result"]))
      (.case "RES" (.tuple [s'v, rv])) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs'') (evalExp_var fr))
  obtain ⟨out, hhost, hout⟩ :=
    hostMem_of_eval B Hi rfl fs' (hhv ▸ fh) fn fw hres (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨s₂, r, rfl, hs₂, hr₂⟩ := outcome_res hout
  obtain ⟨x, hx, hw⟩ := cfgSt_inv hlr.2 fs'' ff'
  have hx' : x = .list (adminsToV r.toAdmin) :=
    Equiv.ExecNumeric.Applies.unique (applies_of_call1 rfl fr hx) (hr₂ ▸ Hs.liftResult r)
  have hw' : w = configV hn ⟨s₂, f, r.toAdmin⟩ := by
    rw [hw, hx', hs₂]
    rfl
  exact ⟨_, hw', .callRefHost hcr hfn hex hnl hcode₀ hhost⟩

include D S Hi Ci in
/-- **`Backward.step 9`** (`call_ref-hostfunc-div`). -/
theorem bwd_callRefHostDiv : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step" 9 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (hasStepRules_simEnv B).callRefHostfuncDiv hf)
  obtain ⟨sv, fs, -⟩ := quant_of (x := "s") (t := storeT) hq (.head _)
  obtain ⟨fv, ff, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := addrT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hlr := Exn.evalExp_tup2_inv he
  have hw : w = configV hn ⟨s, f, code⟩ := EvalExp.unique hlr.2 hlr.1
  have hL : HostLhs (hn := hn) s f code (VarEnv.empty.bindVals σ) :=
    hostLhs_of D fs ff fa fy (valsTyped_of hq (.tail _ (.tail _ (.tail _ (.head _))))) hlr.1
  obtain ⟨⟨vs, addr, c₀, rfl, hcr, fa', fn, fw⟩, fs', ff'⟩ := hL
  obtain ⟨fiv, ffi, -⟩ := quant_of (x := "fi") (t := funcinstT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨hfv, fh, -⟩ := quant_of (x := "hf") (t := .textT) hq (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))
  obtain ⟨fn₀, ps, rs, hh, hfn, -, hex, hnl, hcode₀, hhv⟩ := hostPrems B S Ci rfl fs' ff' fa'
    ffi fh fn (ifPrem (hp _ (.head _))) (hp _ (.tail _ (.head _))) (fun _ h => h) (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have hbot := hostMem_of_eval B Hi rfl fs' (hhv ▸ fh) fn fw evalExp_caseNil (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨out, hhost, hout⟩ := hbot
  have hdiv : out = .diverged := outcome_bot hout
  exact ⟨_, hw, .callRefHostDiv hcr hfn hex hnl hcode₀ (hdiv ▸ hhost)⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Bwd
