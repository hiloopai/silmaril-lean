module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.HostT

/-!
# Round 5, pass 2, track fwdref: the host-call rules, forward and backward, from `HostRespectsT`

Copies of `fwd_callRefHost5`/`fwd_callRefHostDiv5` and track backward's
`bwd_callRefHost`/`bwd_callRefHostDiv` (and `hostMem_of_eval`), with `$hostcall` read at the one
call each rule makes (`hostcall_typed`, `hostInv_typed`) instead of through `CtrlHost.hostcall`
or `Bwd.HostInv`, which quantify over every call. The store image of that call is typed: the
source configuration is `Typed` in both directions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (tyBnd)
open Round4Int (BI)
open Round5.Fwd (TypesB callTypesB)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Forward -/

/-- `call_ref` into a host function that returns, for a bounded callee type
(`Round5.Fwd.fwd_callRefHost5` from `HostRespectsT`). -/
theorem fwd_callRefHostT (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) {s s' : Store H} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .host h)
    (hhost : host h s vs (.returned s' r)) (hd : tyBnd fi.type = true) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ := by
  intro hc₁ hc₂
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨hps, hrs, hexp⟩ := callTypesB TB hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨hz', hres⟩ := (T.config _).1 hc₂
  obtain ⟨hst, hfr⟩ := (T.state _ _).1 hz
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  obtain ⟨os, hcall, hall⟩ := hostcall_typed hf hr h s vs hst
  have hcv : TypedV (simEnv (BI P hn host)) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BI P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv (BI P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s),
        .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostRes (hasStepRules_simEnv _).callRefHostfuncRes
    (fs := s.funcs.map (funcInstV hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy hst' (ConfigOk.typedV_result r)
    (ConfigOk.funcinst_of_store hn s a fi hst hfa) hps (Tg.natM _) hrs (typedV_text (hn h))
    (Prims.applies_funcinst (Prims.projDefs_simEnv _) hn s f)
    (funcs_getElem_map hfa) rfl (funcInstV_code_host hcode) hexp hcall'
    (hall _ hhost) (Prims.applies_liftResult _ r)
  simpa [configV, stateV, adminsToV_append, hyy] using key

/-- `call_ref` into a host function that diverges, for a bounded callee type
(`Round5.Fwd.fwd_callRefHostDiv5` from `HostRespectsT`). -/
theorem fwd_callRefHostDivT (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) {s : Store H} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged)
    (hd : tyBnd fi.type = true) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ := by
  intro hc₁ _
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨hps, hrs, hexp⟩ := callTypesB TB hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨hst, hfr⟩ := (T.state _ _).1 hz
  obtain ⟨os, hcall, hall⟩ := hostcall_typed hf hr h s vs hst
  have hcv : TypedV (simEnv (BI P hn host)) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BI P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv (BI P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s),
        .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostDiv (hasStepRules_simEnv _).callRefHostfuncDiv
    (fs := s.funcs.map (funcInstV hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (ConfigOk.funcinst_of_store hn s a fi hst hfa)
    hps (Tg.natM _) hrs (typedV_text (hn h))
    (Prims.applies_funcinst (Prims.projDefs_simEnv _) hn s f)
    (funcs_getElem_map hfa) rfl (funcInstV_code_host hcode) hexp hcall' (hall _ hhost)
  simpa [configV, stateV, adminsToV_append, hyy] using key

/-! ## Backward -/

/-- `o ∈ $hostcall(_HOSTFUNC hf, s, val^n)` on a typed store image, read back
(`Bwd.hostMem_of_eval` from `HostRespectsT`). -/
theorem hostMem_of_evalT (hf : HostFinite host) (hr : HostRespectsT (simEnv (BI P hn host)) hn host)
    {ρ : VarEnv} {s₀ : Store H} {hh : H} {vs : List Val} {oe : Exp} {o : Value}
    (hst : TypedV (simEnv (BI P hn host)) storeT (storeV hn s₀)) (hd : ρ.findDef? "hostcall" = none)
    (fs : ρ.findVal? "s" = some (storeV hn s₀)) (fh : ρ.findVal? "hf" = some (.text (hn hh)))
    (fn : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (fw : ρ.findVal? "val*" = some (.list (vs.map valV)))
    (ho : EvalExp (simEnv (BI P hn host)) ρ oe o)
    (h : EvalExp (simEnv (BI P hn host)) ρ (.memE oe (.callE "hostcall"
      [.expA (.caseE "_HOSTFUNC" (.varE "hf")), .expA (.varE "s"), .expA (.iterE (.varE "val")
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))])) (.bool true)) :
    ∃ out, host hh s₀ vs out ∧ o = outcomeV hn out := by
  obtain ⟨v₁, v₂, h₁, h₂, hm⟩ := evalExp_memE_iff.1 h
  have e₁ : v₁ = o := EvalExp.unique h₁ ho
  have hap : Applies (simEnv (BI P hn host)) "hostcall" [.val (.case "_HOSTFUNC" (.text (hn hh))),
      .val (storeV hn s₀), .val (.list (vs.map valV))] v₂ :=
    (applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_case (evalExp_var fh))
      (Equiv.evalArgs_cons (evalExp_var fs) (Equiv.evalArgs_cons
        (evalExp_iterNVar (by decide) fn fw) (evalArgs_nil _ ρ))))).2 (evalExp_callE_iff.1 h₂)
  exact hostInv_typed hf hr hst hap (e₁ ▸ hm)

open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd in
/-- **`Backward.step 8`** (`call_ref-hostfunc-res`), from `HostRespectsT`
(`Bwd.bwd_callRefHost`). -/
theorem bwd_callRefHostT (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) :
    ∀ (c : Config H) (w : Value), Typed (simEnv (BI P hn host)) hn c →
      Fires (simEnv (BI P hn host)) "Step" 8 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  rintro ⟨s, f, code⟩ w ht hfi
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  have S : CtrlReads (simEnv (BI P hn host)) hn := Round5.Bwd.ctrlReads_builtins
  have Hs : CtrlLift (simEnv (BI P hn host)) := Round5.Bwd.ctrlLift_builtins
  have Ci : CallInv (simEnv (BI P hn host)) := Integrate.callInv_concrete
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have hst : TypedV (simEnv (BI P hn host)) storeT (storeV hn s) :=
    ((T.state _ _).1 ((T.config _).1 ht).1).1
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (hasStepRules_simEnv _).callRefHostfuncRes hfi)
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
  obtain ⟨fn₀, ps, rs, hh, hfn, -, hex, hnl, hcode₀, hhv⟩ := hostPrems _ S Ci rfl fs' ff' fa'
    ffi fh fn (ifPrem (hp _ (.head _))) (hp _ (.tail _ (.head _))) (fun _ h => h) (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have hres : EvalExp (simEnv (BI P hn host)) _ (.caseE "RES" (.tupE [.varE "s'", .varE "result"]))
      (.case "RES" (.tuple [s'v, rv])) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs'') (evalExp_var fr))
  obtain ⟨out, hhost, hout⟩ :=
    hostMem_of_evalT hf hr hst rfl fs' (hhv ▸ fh) fn fw hres (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨s₂, r, rfl, hs₂, hr₂⟩ := outcome_res hout
  obtain ⟨x, hx, hw⟩ := cfgSt_inv hlr.2 fs'' ff'
  have hx' : x = .list (adminsToV r.toAdmin) :=
    Equiv.ExecNumeric.Applies.unique (applies_of_call1 rfl fr hx) (hr₂ ▸ Hs.liftResult r)
  have hw' : w = configV hn ⟨s₂, f, r.toAdmin⟩ := by
    rw [hw, hx', hs₂]
    rfl
  exact ⟨_, hw', .callRefHost hcr hfn hex hnl hcode₀ hhost⟩

open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd in
/-- **`Backward.step 9`** (`call_ref-hostfunc-div`), from `HostRespectsT`
(`Bwd.bwd_callRefHostDiv`). -/
theorem bwd_callRefHostDivT (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) :
    ∀ (c : Config H) (w : Value), Typed (simEnv (BI P hn host)) hn c →
      Fires (simEnv (BI P hn host)) "Step" 9 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  rintro ⟨s, f, code⟩ w ht hfi
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  have S : CtrlReads (simEnv (BI P hn host)) hn := Round5.Bwd.ctrlReads_builtins
  have Ci : CallInv (simEnv (BI P hn host)) := Integrate.callInv_concrete
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have hst : TypedV (simEnv (BI P hn host)) storeT (storeV hn s) :=
    ((T.state _ _).1 ((T.config _).1 ht).1).1
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (hasStepRules_simEnv _).callRefHostfuncDiv hfi)
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
  obtain ⟨fn₀, ps, rs, hh, hfn, -, hex, hnl, hcode₀, hhv⟩ := hostPrems _ S Ci rfl fs' ff' fa'
    ffi fh fn (ifPrem (hp _ (.head _))) (hp _ (.tail _ (.head _))) (fun _ h => h) (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨out, hhost, hout⟩ := hostMem_of_evalT hf hr hst rfl fs' (hhv ▸ fh) fn fw evalExp_caseNil
    (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hdiv : out = .diverged := outcome_bot hout
  exact ⟨_, hw, .callRefHostDiv hcr hfn hex hnl hcode₀ (hdiv ▸ hhost)⟩

/-- **`Bwd.HostStepsV` from `HostRespectsT`** (`Round5.Bwd.hostStepsV_of_hostInv`). -/
theorem hostStepsV_of_T (hf : HostFinite host) (hr : HostRespectsT (simEnv (BI P hn host)) hn host) :
    Round5.Bwd.HostStepsV (simEnv (BI P hn host)) hn P host := by
  intro i hi c w _ hc hfi
  refine Bwd.step_upTo ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  · exact bwd_callRefHostT hf hr c w hc hfi
  · exact bwd_callRefHostDivT hf hr c w hc hfi

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef
