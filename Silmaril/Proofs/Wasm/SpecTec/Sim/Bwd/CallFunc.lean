module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Otherwise

/-!
# Track backward: `call_ref-func` (`Step` 7)

`bwd_callRefFunc` is the `Backward.step 7` field: a SpecTec `call_ref-func` step from the image
of a configuration is the image of Core's `callRefFunc` step. The four premises are read back in
turn: `$funcinst(z)[a] = fi` names a store function (`funcinst_of_eval`); `Expand` on its type
gives Core's `Expand` with the arities (`CallInv`, assumed); `fi.CODE = FUNC x (LOCAL t)* instr*`
makes it a Wasm function whose locals and body are `t*` and `instr*` (`code_of_eval`); and the
new frame `f` is the image of `Frame.forCall` (`frame_of_eval`, through family C's
`frameV_forCall` and `CtrlCall.default`).

Hypotheses: family C's `CtrlDecode`, `CtrlReads` (`CtrlState` without `blocktype`),
`CtrlDefault` (`CtrlCall.default`), and `CallInv`. All four hold for `Prims.builtins`
(round 5: `Round5.Bwd.famBwdV_of_hostSteps`); the full `CtrlState`/`CtrlCall` coerce to them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins) (D : CtrlDecode (simEnv B)) (S : CtrlReads (simEnv B) hn)
  (C : CtrlDefault (simEnv B)) (Ci : CallInv (simEnv B))

/-- An equality test, read back. -/
theorem eq_of_cmp {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.cmpE .eqOp .boolT e₁ e₂) (.bool true)) :
    ∃ v, EvalExp env ρ e₁ v ∧ EvalExp env ρ e₂ v := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e : v₁ = v₂ := by simpa [cmpValues] using hc
  exact ⟨v₁, h₁, e ▸ h₂⟩

include S in
/-- `$funcinst(z)[a] = fi`, read back: `fi` is the image of a store function. -/
theorem funcinst_of_eval {s : Store H} {f : Frame} {ρ : VarEnv} {addr : Nat} {fv : Value}
    (hd : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN addr))) (ffi : ρ.findVal? "fi" = some fv)
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) (.varE "fi")) (.bool true)) :
    ∃ fn, s.funcs[addr]? = some fn ∧ fv = funcInstV hn fn := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have ev : v = fv := EvalExp.unique h₂ (evalExp_var ffi)
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 h₁
  have ewl : wl = .list (s.funcs.map (funcInstV hn)) :=
    Equiv.ExecNumeric.Applies.unique (applies_of_call1 hd fz hwl) (S.funcinst s f)
  have ei : Value.num (.natN i) = .num (.natN addr) := EvalExp.unique hi (evalExp_var fa)
  have hget : (s.funcs.map (funcInstV hn))[addr]? = some v := by
    rw [← natN_inj ei]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fn, hfn, hfv⟩ := Option.map_eq_some_iff.1 hget
  exact ⟨fn, hfn, by rw [← ev, ← hfv]⟩

/-- `fi.CODE = FUNC x (LOCAL t)* instr*`, read back at the image of a function instance. -/
theorem code_of_eval {env : Env} {ρ : VarEnv} {fn : FuncInst H} {xv : Value}
    {ts is : List Value} (ffi : ρ.findVal? "fi" = some (funcInstV hn fn))
    (fx : ρ.findVal? "x" = some xv) (ft : ρ.findVal? "t*" = some (.list ts))
    (fi : ρ.findVal? "instr*" = some (.list is))
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "FUNC" (.tupE
      [.varE "x", .iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]),
      iterPat "instr" "instr*"]))) (.bool true)) :
    ∃ code, fn.code = .wasm code ∧ ts = code.locals.map Encode.toValue ∧
      is = instrsToV code.body := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have el : EvalExp env ρ (.iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]))
      (.list (ts.map (.case "LOCAL"))) :=
    evalExp_iterMap ft fun _ _ => evalExp_case (evalExp_var (findVal_bind1 (by decide)))
  have e₂ : v = .case "FUNC" (.tuple [xv, .list (ts.map (.case "LOCAL")), .list is]) :=
    EvalExp.unique h₂ (evalExp_case (evalExp_tup3 (evalExp_var fx) el (evalExp_iterPat (by decide) fi)))
  obtain ⟨fv, hfv, hfld⟩ := evalExp_dotE_iff.1 h₁
  have efv : fv = funcInstV hn fn := EvalExp.unique hfv (evalExp_var ffi)
  rw [efv, e₂] at hfld
  cases hc : fn.code with
  | host h' => simp [funcInstV, Value.field?, hc] at hfld
  | wasm code =>
    have hf' := hfld.symm.trans (funcInstV_code_wasm hc)
    simp only [Option.some.injEq, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, true_and, and_true] at hf'
    refine ⟨code, rfl, ?_, hf'.2.2⟩
    exact List.map_injective_iff.2 (fun _ _ h => (Value.case.inj h).2) hf'.2.1

include C in
/-- `f = {LOCALS val^n ++ $default_(t)*, MODULE fi.MODULE}`, read back: `f` is the image of the
new frame. -/
theorem frame_of_eval {ρ : VarEnv} {fn : FuncInst H} {fv₀ : Value} {vs : List Val}
    {ts : List ValType} (hd : ρ.findDef? "default_" = none) (ff : ρ.findVal? "f" = some fv₀)
    (ffi : ρ.findVal? "fi" = some (funcInstV hn fn))
    (fn' : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (fw : ρ.findVal? "val*" = some (.list (vs.map valV)))
    (ft : ρ.findVal? "t*" = some (.list (ts.map Encode.toValue)))
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.varE "f") (.strE [.mk "LOCALS" (.catE
      (.iterE (.optE (some (.varE "val"))) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
      (.iterE (.callE "default_" [.expA (.varE "t")]) (.mk .list [.mk "t" (.varE "t*")]))),
      .mk "MODULE" (.dotE (.varE "fi") "MODULE")])) (.bool true)) :
    fv₀ = frameV (Frame.forCall fn.module vs ts) := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have e₁ : EvalExp (simEnv B) ρ (.iterE (.optE (some (.varE "val")))
      (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
      (.list ((vs.map valV).map fun w => .opt (some w))) :=
    evalExp_iterNMap fn' fw fun _ _ =>
      evalExp_optE_some_iff.2 ⟨_, evalExp_var (findVal_bind1 (by decide)), rfl⟩
  have hdef : ∀ t ∈ ts.map Encode.toValue,
      Applies (simEnv B) "default_" [.val t] (defaultFn (simEnv B) t) := fun t ht => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
    exact (defaultFn_eq (C.default fn.module l)) ▸ C.default fn.module l
  have e₂ : EvalExp (simEnv B) ρ (.iterE (.callE "default_" [.expA (.varE "t")])
      (.mk .list [.mk "t" (.varE "t*")])) (.list ((ts.map Encode.toValue).map (defaultFn _))) :=
    evalExp_iterMap ft fun t ht =>
      evalExp_call1 (findDef_bind1 hd) (findVal_bind1 (by decide)) (hdef t ht)
  have hmod : (funcInstV hn fn).field? "MODULE" =
      some (Equiv.RuntimeBridge.moduleInstToValue CT fn.module) := by
    simp [funcInstV, Value.field?]
  have e₃ := evalExp_str2 (a₁ := "LOCALS") (a₂ := "MODULE") (evalExp_cat e₁ e₂)
    (evalExp_dotE_iff.2 ⟨_, evalExp_var ffi, hmod⟩)
  have ev : v = fv₀ := EvalExp.unique h₁ (evalExp_var ff)
  rw [frameV_forCall (simEnv B) C fn.module vs ts, ← ev]
  exact EvalExp.unique h₂ e₃

/-- The image of a call frame. -/
theorem adminsToV_callFrame (m : Nat) (F : Frame) (body : List Instr) :
    adminsToV [.frame m F [.label m [] (expression body)]] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN m), frameV F,
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN m), .list [],
          .list (instrsToV body)])]])] := by
  simp only [adminsToV, adminToV_frame, adminToV_label, Exn.adminsToV_expression, instrsToV_nil]

/-- The `TYPE` of the image of a function instance. -/
theorem funcInstV_type_of_eval {env : Env} {ρ : VarEnv} {fn : FuncInst H} {ty : Value}
    (ffi : ρ.findVal? "fi" = some (funcInstV hn fn))
    (h : EvalExp env ρ (.dotE (.varE "fi") "TYPE") ty) : ty = CT.defType fn.type := by
  obtain ⟨fv, hfv, hfld⟩ := evalExp_dotE_iff.1 h
  have efv : fv = funcInstV hn fn := EvalExp.unique hfv (evalExp_var ffi)
  rw [efv] at hfld
  simp [funcInstV, Value.field?] at hfld
  exact hfld.symm

include D S C Ci in
/-- **`Backward.step 7`** (`call_ref-func`). -/
theorem bwd_callRefFunc : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step" 7 (.tuple [configV hn c, w]) → BwdP hn P host c w := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (hasStepRules_simEnv B).callRefFunc hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := addrT) hq (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have ex : EvalExp (simEnv B) _ (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"),
      .caseE "CALL_REF" (.varE "yy")]) (.list [.case "REF.FUNC_ADDR" av, .case "CALL_REF" yy]) :=
    evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fy))
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  have hl₀ := cfg_inv (configV_eq hn ⟨s, f, code⟩ ▸ hl) fz
  obtain ⟨ws, fv, fn, hcode⟩ := valsN_cat hl₀.2 ex
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨l₀, rest, rfl, h₀, hrest⟩ := Exn.adminsToV_eq_append (Value.list.inj hcode)
  obtain ⟨vs, rfl, hlen⟩ := decode_vals D h₀ (ew ▸ htv)
  obtain ⟨b, c₀, rfl, hb, hc₀⟩ := adminsToV_eq_pair hrest
  obtain ⟨addr, rfl, hav⟩ := decode_refFuncAddr hb
  have hcr : c₀.IsCallRef := D.callRef c₀ _ hc₀
  obtain ⟨fv₀, ff, -⟩ := quant_of (x := "f") (t := frameT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  obtain ⟨fiv, ffi, -⟩ := quant_of (x := "fi") (t := funcinstT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
  obtain ⟨xv, fx, -⟩ := quant_of (x := "x") (t := idxT) hq (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
  obtain ⟨ts, ft, -⟩ := quant_list (x := "t*") (t := .varT "valtype" []) hq (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.head _)))))))))))))
  have fz' : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := hl₀.1 ▸ fz
  obtain ⟨fn₀, hfn, rfl⟩ :=
    funcinst_of_eval B S rfl fz' (hav ▸ fa) ffi (ifPrem (hp _ (.head _)))
  obtain ⟨w', hw', hexp⟩ := rulePrem_inv (hp _ (.tail _ (.head _)))
  obtain ⟨ty, ftv, hty, hft, rfl⟩ := tup2_inv hw'
  have ety : ty = CT.defType fn₀.type := funcInstV_type_of_eval ffi hty
  obtain ⟨T₁, T₂, fn₁, fm₂, rfl⟩ := funcTypePat_inv hft
  obtain ⟨ps, rs, hex, hl₁, hl₂⟩ := Ci.expand fn₀.type T₁ T₂ (ety ▸ hexp)
  obtain ⟨code₀, hcode₀, hts, his⟩ :=
    code_of_eval ffi fx ft fi (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have hws : ws = vs.map valV := by rw [← h₀, adminsToV_vals]
  have hF : fv₀ = frameV (Frame.forCall fn₀.module vs code₀.locals) :=
    frame_of_eval B C rfl ff ffi (hws ▸ fn) (hws ▸ fv) (hts ▸ ft)
      (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hnl : vs.length = ps.length := by
    rw [← hlen, ← hl₁]
    exact natN_inj (Option.some.inj (fn.symm.trans fn₁))
  have hr' : w = cfgV z [.case "FRAME_%{%}%" (.tuple [.num (.natN T₂.length), fv₀,
      .list [.case "LABEL_%{%}%" (.tuple [.num (.natN T₂.length), .list [], .list is])]])] :=
    EvalExp.unique hr (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
      (evalExp_tup3 (evalExp_var fm₂) (evalExp_var ff) (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fm₂) evalExp_listNil (evalExp_iterPat (by decide) fi)))))))))
  have hw : w = configV hn ⟨s, f, [.frame rs.length (Frame.forCall fn₀.module vs code₀.locals)
      [.label rs.length [] (expression code₀.body)]]⟩ := by
    rw [hr', hl₀.1, hF, his, hl₂, configV_eq, adminsToV_callFrame]
  exact ⟨_, hw, .callRefFunc hcr hfn hex hnl hcode₀⟩

end Silmaril.Wasm.SpecTec.Sim.Bwd
