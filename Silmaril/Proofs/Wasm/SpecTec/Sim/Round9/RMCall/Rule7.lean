module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.Thms
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Integrate.Thms

/-!
# Round 9, rm: `Step` rule 7 (`call_ref-func`) backward at `configVD`

Round 6's `Bwd.bwd_callRefFunc` reads a firing of `Step` rule 7 from a `configV` image back as
Core's `callRefFunc` step. Here the same is done from a `configVD` image, for every store and
code, memory SIMD instructions included, in every `simEnv B` with `Bwd.CallInv`:

* `codeD_of_eval`: `fi.CODE = FUNC x (LOCAL t)* instr*` at a `funcInstVD` image gives a Wasm
  function whose body's `instrToVD` image is `instr*`;
* `frameD_of_eval`: the new frame, read back at a `funcInstVD` image;
* `lhs7D_of`: the left-hand side `z; val^n (REF.FUNC_ADDR a) (CALL_REF yy)` decoded from a
  `configVD` image;
* `bwd_callRefFuncD`: **the rule backward**, up to nothing (the successor's image is the
  right-hand side itself).

The callee's body is moved as data: the rule copies `instr*` into the new frame, and
`adminsToVD (expression body) = instrsToVD body`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMCall

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (AdminMS AdminsMS)
open Round7.MemSimd (storeVD stateVD configVD funcInstVD adminsToVD adminToVD instrsToVD TypedD
  BwdUpToD adminsToVD_eq_map adminToVD_case vals_of_typedD adminsToVD_expression)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- `fi.CODE = FUNC x (LOCAL t)* instr*`, read back at a `funcInstVD` image. -/
theorem codeD_of_eval {env : Env} {ρ : VarEnv} {fn : FuncInst H} {xv : Value}
    {ts is : List Value} (ffi : ρ.findVal? "fi" = some (funcInstVD hn fn))
    (fx : ρ.findVal? "x" = some xv) (ft : ρ.findVal? "t*" = some (.list ts))
    (fi : ρ.findVal? "instr*" = some (.list is))
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "FUNC" (.tupE
      [.varE "x", .iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]),
      iterPat "instr" "instr*"]))) (.bool true)) :
    ∃ code, fn.code = .wasm code ∧ ts = code.locals.map Encode.toValue ∧
      is = instrsToVD code.body := by
  obtain ⟨v, h₁, h₂⟩ := Bwd.eq_of_cmp h
  have el : EvalExp env ρ (.iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]))
      (.list (ts.map (.case "LOCAL"))) :=
    evalExp_iterMap ft fun _ _ => evalExp_case (evalExp_var (findVal_bind1 (by decide)))
  have e₂ : v = .case "FUNC" (.tuple [xv, .list (ts.map (.case "LOCAL")), .list is]) :=
    EvalExp.unique h₂
      (evalExp_case (evalExp_tup3 (evalExp_var fx) el (evalExp_iterPat (by decide) fi)))
  obtain ⟨fv, hfv, hfld⟩ := evalExp_dotE_iff.1 h₁
  have efv : fv = funcInstVD hn fn := EvalExp.unique hfv (evalExp_var ffi)
  rw [efv, e₂] at hfld
  cases hc : fn.code with
  | host h' => simp [funcInstVD, Value.field?, hc] at hfld
  | wasm code =>
    have hf' := hfld.symm.trans (Round7.HCtx.funcInstVD_code_wasm hc)
    simp only [Option.some.injEq, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, true_and, and_true] at hf'
    refine ⟨code, rfl, ?_, hf'.2.2⟩
    exact List.map_injective_iff.2 (fun _ _ h => (Value.case.inj h).2) hf'.2.1


/-- `f = {LOCALS val^n ++ $default_(t)*, MODULE fi.MODULE}`, read back at a `funcInstVD` image:
`f` is the image of the new frame. -/
theorem frameD_of_eval (B : Builtins) {ρ : VarEnv} {fn : FuncInst H} {fv₀ : Value}
    {vs : List Val} {ts : List ValType} (hd : ρ.findDef? "default_" = none)
    (ff : ρ.findVal? "f" = some fv₀) (ffi : ρ.findVal? "fi" = some (funcInstVD hn fn))
    (fn' : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (fw : ρ.findVal? "val*" = some (.list (vs.map valV)))
    (ft : ρ.findVal? "t*" = some (.list (ts.map Encode.toValue)))
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.varE "f") (.strE [.mk "LOCALS" (.catE
      (.iterE (.optE (some (.varE "val"))) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
      (.iterE (.callE "default_" [.expA (.varE "t")]) (.mk .list [.mk "t" (.varE "t*")]))),
      .mk "MODULE" (.dotE (.varE "fi") "MODULE")])) (.bool true)) :
    fv₀ = frameV (Frame.forCall fn.module vs ts) := by
  have C : CtrlDefault (simEnv B) := ⟨Integrate.ctrlCallDefault_simEnv B⟩
  obtain ⟨v, h₁, h₂⟩ := Bwd.eq_of_cmp h
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
  have hmod : (funcInstVD hn fn).field? "MODULE" =
      some (Equiv.RuntimeBridge.moduleInstToValue CT fn.module) := by
    simp [funcInstVD, Value.field?]
  have e₃ := evalExp_str2 (a₁ := "LOCALS") (a₂ := "MODULE") (evalExp_cat e₁ e₂)
    (evalExp_dotE_iff.2 ⟨_, evalExp_var ffi, hmod⟩)
  have ev : v = fv₀ := EvalExp.unique h₁ (evalExp_var ff)
  rw [frameV_forCall (simEnv B) C fn.module vs ts, ← ev]
  exact EvalExp.unique h₂ e₃

/-- The `configVD` image of a call frame. -/
theorem adminsToVD_callFrame (m : Nat) (F : Frame) (body : List Instr) :
    adminsToVD [.frame m F [.label m [] (expression body)]] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN m), frameV F,
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN m), .list [],
          .list (instrsToVD body)])]])] := by
  simp only [adminsToVD, Round7.MemSimd.adminToVD, adminsToVD_expression, Round7.MemSimd.instrsToVD]

/-- A list whose `adminToVD` image has two elements. -/
theorem map_eq_pair : ∀ {l : List Admin} {x y : Value}, l.map adminToVD = [x, y] →
    ∃ b c, l = [b, c] ∧ adminToVD b = x ∧ adminToVD c = y
  | [b, c], _, _, h => by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨b, c, rfl, h.1, h.2⟩
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | _ :: _ :: _ :: _, _, _, h => by simp at h

/-- **The code `val^n (REF.FUNC_ADDR a) (CALL_REF yy)`, decoded from its `adminsToVD` image**,
when the prefix is typed as `val*`. -/
theorem code7D_of {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {code : List Admin}
    {ws : List Value} {av yy : Value} (htv : HasTyp (simEnv B) ρ valsT (.list ws))
    (hcode : adminsToVD code = ws ++ [.case "REF.FUNC_ADDR" av, .case "CALL_REF" yy]) :
    ∃ vs addr c, code = vals vs ++ [.ref (.func addr), c] ∧ c.IsCallRef ∧
      av = .num (.natN addr) ∧ ws = vs.map valV := by
  have hmap : code.map adminToVD = ws ++ [.case "REF.FUNC_ADDR" av, .case "CALL_REF" yy] := by
    rw [← adminsToVD_eq_map]; exact hcode
  obtain ⟨l₀, rest, rfl, h₀, hrest⟩ := List.map_eq_append_iff.1 hmap
  have hws : adminsToVD l₀ = ws := by rw [adminsToVD_eq_map]; exact h₀
  obtain ⟨vs, rfl⟩ := vals_of_typedD (B := B) hρ (hws ▸ htv)
  obtain ⟨b, c₀, hr, hb, hc₀⟩ := map_eq_pair hrest
  obtain ⟨-, -, hbv⟩ := Round7.HostRulesD.adminToVD_val hb (by simp [Typing.valHeads])
  obtain ⟨addr, hv, hav⟩ := Bwd.decode_refFuncAddr hbv
  have hcr : c₀.IsCallRef := Typing.head_callRef (adminToVD_case hc₀).symm
  have hws' : ws = vs.map valV := by
    rw [← hws, Round7.MemSimd.adminsToVD_vals, adminsToV_vals]
  exact ⟨vs, addr, c₀, by rw [hr, hv], hcr, hav, hws'⟩

/-- **The left-hand side `z; val^n (REF.FUNC_ADDR a) (CALL_REF yy)` of `call_ref-func`,
decoded from a `configVD` image.** -/
theorem lhs7D_of {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {code : List Admin} {z av yy : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some z)
    (fa : (VarEnv.empty.bindVals σ).findVal? "a" = some av)
    (fy : (VarEnv.empty.bindVals σ).findVal? "yy" = some yy)
    (htv : ∀ ws, (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) →
      HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws))
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .catE (valsNPat "val" "val*" "n")
        (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"), .caseE "CALL_REF" (.varE "yy")])]))
      (configVD hn ⟨s, f, code⟩)) :
    z = stateVD hn s f ∧ ∃ vs addr c, code = vals vs ++ [.ref (.func addr), c] ∧ c.IsCallRef ∧
      (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN addr)) ∧
      (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN (vs.map valV).length)) ∧
      (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (vs.map valV)) := by
  have hl₀ := Bwd.cfg_inv (Round7.MemSimd.configVD_eq hn ⟨s, f, code⟩ ▸ hl) fz
  obtain ⟨ws, fw, fn, hcode⟩ := Bwd.valsN_cat hl₀.2
    (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fy)))
  obtain ⟨vs, addr, c₀, hc, hcr, hav, hws⟩ :=
    code7D_of (B := B) ⟨rfl, rfl, rfl⟩ (htv ws fw) (Value.list.inj hcode)
  exact ⟨hl₀.1, vs, addr, c₀, hc, hcr, hav ▸ fa, hws ▸ fn, hws ▸ fw⟩

/-- **`Step` rule 7 (`call_ref-func`) backward, at `configVD`**: in every `simEnv B` with
`Bwd.CallInv`, a firing from the `configVD` image of any configuration (memory SIMD code in the
code or the store included) is the image of Core's `callRefFunc` step. No typing hypothesis is
needed. -/
theorem bwd_callRefFuncD (B : Builtins) (Ci : Bwd.CallInv (simEnv B)) (c : Config H) (w : Value)
    (hf : Fires (simEnv B) "Step" 7 (.tuple [configVD hn c, w])) : BwdUpToD hn P host c w := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (hasStepRules_simEnv B).callRefFunc hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := addrT) hq (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨hz, vs, addr, c₀, rfl, hcr, fa', fn, fw⟩ :=
    lhs7D_of fz fa fy (Bwd.valsTyped_of hq (.tail _ (.tail _ (.head _)))) hl
  have hzv : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.varE "z") (stateVD hn s f) :=
    hz ▸ evalExp_var fz
  obtain ⟨fv₀, ff, -⟩ := quant_of (x := "f") (t := frameT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨fiv, ffi, -⟩ := quant_of (x := "fi") (t := funcinstT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
  obtain ⟨fn₀, hfn, rfl⟩ :=
    Round7.HostRulesD.funcinstD_of_eval rfl hzv fa' ffi (ifPrem (hp _ (.head _)))
  obtain ⟨w', hw', hexp⟩ := Bwd.rulePrem_inv (hp _ (.tail _ (.head _)))
  obtain ⟨ty, ftv, hty, hft, rfl⟩ := Bwd.tup2_inv hw'
  have ety : ty = CT.defType fn₀.type := Round7.HostRulesD.funcInstVD_type_of_eval ffi hty
  obtain ⟨T₁, T₂, fn₁, fm₂, rfl⟩ := Bwd.funcTypePat_inv hft
  obtain ⟨ps, rs, hex, hl₁, hl₂⟩ := Ci.expand fn₀.type T₁ T₂ (ety ▸ hexp)
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  obtain ⟨xv, fx, -⟩ := quant_of (x := "x") (t := idxT) hq (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
  obtain ⟨ts, ft, -⟩ := quant_list (x := "t*") (t := .varT "valtype" []) hq (.tail _ (.tail _
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.tail _ (.head _)))))))))))))
  obtain ⟨code₀, hcode₀, hts, his⟩ :=
    codeD_of_eval ffi fx ft fi (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have hF : fv₀ = frameV (Frame.forCall fn₀.module vs code₀.locals) :=
    frameD_of_eval B rfl ff ffi fn fw (hts ▸ ft)
      (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hnl : vs.length = ps.length := by
    rw [← hl₁, ← List.length_map (f := valV)]
    exact Bwd.natN_inj (Option.some.inj (fn.symm.trans fn₁))
  have hr' : w = cfgV z [.case "FRAME_%{%}%" (.tuple [.num (.natN T₂.length), fv₀,
      .list [.case "LABEL_%{%}%" (.tuple [.num (.natN T₂.length), .list [], .list is])]])] :=
    EvalExp.unique hr (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case
      (evalExp_tup3 (evalExp_var fm₂) (evalExp_var ff) (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fm₂) evalExp_listNil (evalExp_iterPat (by decide) fi)))))))))
  have hw : w = configVD hn ⟨s, f, [.frame rs.length (Frame.forCall fn₀.module vs code₀.locals)
      [.label rs.length [] (expression code₀.body)]]⟩ := by
    rw [hr', hz, hF, his, hl₂, Round7.MemSimd.configVD_eq, adminsToVD_callFrame]
    rfl
  exact ⟨_, _, Bwd.ConfigEq.refl _, hw, .callRefFunc hcr hfn hex hnl hcode₀⟩

/-- **Rule 7 at the concrete primitives** `Prims.builtins P hn host`. -/
theorem bwd_callRefFuncD_builtins (c : Config H) (w : Value)
    (hf : Fires (simEnv (Prims.builtins P hn host)) "Step" 7 (.tuple [configVD hn c, w])) :
    BwdUpToD hn P host c w :=
  bwd_callRefFuncD _ Integrate.callInv_concrete c w hf

end Silmaril.Wasm.SpecTec.Sim.Round9.RMCall
