module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Host

/-!
# Family C: calling a Wasm function (`Step/call_ref-func`)

The rule matches the callee's code against `FUNC x (LOCAL t)* instr*` and builds the new frame
`{LOCALS val?^n ++ $default_(t)*, MODULE fi.MODULE}`; both are iterations whose body is not a bare
variable, so this file first proves the general iteration lemmas `evalExp_iterMap` (a `*`
iteration) and `evalExp_iterNMap` (a `^n` iteration) for any body that evaluates pointwise.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV valsNPat iterPat evalExp_iterPat iterRows_singleton)
open Silmaril.SpecTec.Equiv.ExecStepRules (callRefFuncRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)

/-! ## Iterations with a pointwise body -/

/-- A pointwise evaluation has one fuel level for all elements. -/
theorem uniform_fuel {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {g : Value → Value} :
    ∀ ws : List Value, (∀ w ∈ ws, EvalExp env (ρ.bindVals [(x, w)]) b (g w)) →
      ∃ N, ∀ w ∈ ws, evalExp N env (ρ.bindVals [(x, w)]) b = .ok (g w)
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | w :: ws, h => by
      obtain ⟨n, hn⟩ := h w (List.mem_cons_self ..)
      obtain ⟨N, hN⟩ := uniform_fuel ws fun u hu => h u (List.mem_cons_of_mem _ hu)
      refine ⟨max n N, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact evalExp_ok_of_le (by omega) hn
      · exact evalExp_ok_of_le (by omega) (hN u hu)

/-- The rounds of a pointwise body. -/
theorem mapM_rounds_map {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {g : Value → Value}
    {N : Nat} : ∀ ws : List Value, (∀ w ∈ ws, evalExp N env (ρ.bindVals [(x, w)]) b = .ok (g w)) →
      (ws.map fun w => [(x, w)]).mapM (fun r => evalExp N env (ρ.bindVals r) b) = .ok (ws.map g)
  | [], _ => rfl
  | w :: ws, h => by
      have hw : evalExp N env (ρ.bindVals [(x, w)]) b = .ok (g w) := h w (List.mem_cons_self ..)
      have ih := mapM_rounds_map ws fun u hu => h u (List.mem_cons_of_mem _ hu)
      simp only [List.map_cons, List.mapM_cons, hw, ih]
      rfl

/-- `evalIterList` over one domain, with a pointwise body. -/
theorem evalIterList_map {env : Env} {ρ : VarEnv} {b : Exp} {x : IL.Id} {g : Value → Value}
    {N : Nat} {ws : List Value}
    (h : ∀ w ∈ ws, evalExp N env (ρ.bindVals [(x, w)]) b = .ok (g w)) :
    evalIterList (N + 2) env ρ b [(x, Value.list ws)] none ws.length = .ok (.list (ws.map g)) := by
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
  refine ⟨[(x, ws)], by simp [Value.asList?], by simp, ws.map g, ?_, rfl⟩
  rw [iterRows_singleton, evalRounds]
  exact mapM_rounds_map ws h

/-- **A `*` iteration with a pointwise body** denotes the pointwise image of its domain. -/
theorem evalExp_iterMap {env : Env} {ρ : VarEnv} {b : Exp} {x y : IL.Id} {ws : List Value}
    {g : Value → Value} (hy : ρ.findVal? y = some (.list ws))
    (hb : ∀ w ∈ ws, EvalExp env (ρ.bindVals [(x, w)]) b (g w)) :
    EvalExp env ρ (.iterE b (.mk .list [.mk x (.varE y)])) (.list (ws.map g)) := by
  obtain ⟨N, hN⟩ := uniform_fuel ws hb
  have hdoms : evalDoms (N + 3) env ρ [.mk x (.varE y)] = .ok [(x, Value.list ws)] := by
    simp [evalDoms, domVar, domSrc, evalExp, hy]
  have hl : evalIterList (N + 3) env ρ b [(x, Value.list ws)] none ws.length =
      .ok (.list (ws.map g)) :=
    evalIterList_map fun w hw => evalExp_ok_of_le (by omega) (hN w hw)
  refine evalExp_iterE_iff.mpr ⟨N + 4, ?_⟩
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  exact ⟨[(x, Value.list ws)], rfl, trivial, ws.length, rfl, hl⟩

/-- **A `^n` iteration with a pointwise body**, the counter bound to the domain's length. -/
theorem evalExp_iterNMap {env : Env} {ρ : VarEnv} {b : Exp} {x y c : IL.Id} {ws : List Value}
    {g : Value → Value} (hc : ρ.findVal? c = some (.num (.natN ws.length)))
    (hy : ρ.findVal? y = some (.list ws))
    (hb : ∀ w ∈ ws, EvalExp env (ρ.bindVals [(x, w)]) b (g w)) :
    EvalExp env ρ (.iterE b (.mk (.listN (.varE c) none) [.mk x (.varE y)])) (.list (ws.map g)) := by
  obtain ⟨N, hN⟩ := uniform_fuel ws hb
  have hdoms : evalDoms (N + 3) env ρ [.mk x (.varE y)] = .ok [(x, Value.list ws)] := by
    simp [evalDoms, domVar, domSrc, evalExp, hy]
  have hcount : evalExp (N + 3) env ρ (.varE c) = .ok (.num (.natN ws.length)) := by
    simp [evalExp, hc]
  have hl : evalIterList (N + 3) env ρ b [(x, Value.list ws)] none ws.length =
      .ok (.list (ws.map g)) :=
    evalIterList_map fun w hw => evalExp_ok_of_le (by omega) (hN w hw)
  refine evalExp_iterE_iff.mpr ⟨N + 4, ?_⟩
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  exact ⟨_, rfl, _, rfl, ws.length, rfl, hl⟩

/-- A record of two fields. -/
theorem evalExp_str2 {env : Env} {ρ : VarEnv} {a₁ a₂ : AtomS} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.strE [.mk a₁ e₁, .mk a₂ e₂]) (.struct [(a₁, v₁), (a₂, v₂)]) := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have g₁ : evalExp (max n₁ n₂) env ρ e₁ = .ok v₁ := evalExp_ok_of_le (by omega) h₁
  have g₂ : evalExp (max n₁ n₂) env ρ e₂ = .ok v₂ := evalExp_ok_of_le (by omega) h₂
  refine evalExp_strE_iff.2 ⟨_, ⟨max n₁ n₂ + 1, ?_⟩, rfl⟩
  simp [evalExpFields, g₁, g₂]

/-- The round variable of a one-row binding. -/
theorem findVal_bind1 {ρ : VarEnv} {x : IL.Id} {w : Value} (hx : x ≠ "_") :
    (ρ.bindVals [(x, w)]).findVal? x = some w := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx]

/-- A one-row binding binds no definition. -/
theorem findDef_bind1 {ρ : VarEnv} {x y : IL.Id} {w : Value} (h : ρ.findDef? y = none) :
    (ρ.bindVals [(x, w)]).findDef? y = none := h

/-! ## The construction -/

/-- `fi.CODE = FUNC x (LOCAL t)* instr*`. -/
theorem evalExp_funcCodeEq {env : Env} {ρ : VarEnv} {fv xv : Value} {ts is : List Value}
    (ffi : ρ.findVal? "fi" = some fv) (fx : ρ.findVal? "x" = some xv)
    (ft : ρ.findVal? "t*" = some (.list ts)) (fi : ρ.findVal? "instr*" = some (.list is))
    (hcode : fv.field? "CODE" = some (.case "FUNC" (.tuple [xv, .list (ts.map (.case "LOCAL")),
      .list is]))) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "FUNC" (.tupE [.varE "x",
      .iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]),
      iterPat "instr" "instr*"]))) (.bool true) := by
  have el : EvalExp env ρ (.iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]))
      (.list (ts.map (.case "LOCAL"))) :=
    evalExp_iterMap ft fun _ _ => evalExp_case (evalExp_var (findVal_bind1 (by decide)))
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_dotE_iff.2 ⟨fv, evalExp_var ffi, hcode⟩,
    evalExp_case (evalExp_tup3 (evalExp_var fx) el (evalExp_iterPat (by decide) fi)),
    by simp [cmpValues]⟩

/-- `f = {LOCALS val?^n ++ $default_(t)*, MODULE fi.MODULE}`. -/
theorem evalExp_frameEq {env : Env} {ρ : VarEnv} {f fv mv : Value} {ws ts : List Value}
    {D : Value → Value} (hd : ρ.findDef? "default_" = none) (ff : ρ.findVal? "f" = some f)
    (ffi : ρ.findVal? "fi" = some fv) (fn : ρ.findVal? "n" = some (.num (.natN ws.length)))
    (fw : ρ.findVal? "val*" = some (.list ws)) (ft : ρ.findVal? "t*" = some (.list ts))
    (hmod : fv.field? "MODULE" = some mv)
    (hdef : ∀ t ∈ ts, Applies env "default_" [.val t] (D t))
    (hf : f = .struct [("LOCALS", .list (ws.map (fun w => .opt (some w)) ++ ts.map D)),
      ("MODULE", mv)]) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.varE "f") (.strE [.mk "LOCALS" (.catE
      (.iterE (.optE (some (.varE "val"))) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
      (.iterE (.callE "default_" [.expA (.varE "t")]) (.mk .list [.mk "t" (.varE "t*")]))),
      .mk "MODULE" (.dotE (.varE "fi") "MODULE")])) (.bool true) := by
  have e₁ : EvalExp env ρ (.iterE (.optE (some (.varE "val")))
      (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
      (.list (ws.map fun w => .opt (some w))) :=
    evalExp_iterNMap fn fw fun _ _ => evalExp_optE_some_iff.2 ⟨_, evalExp_var (findVal_bind1 (by decide)), rfl⟩
  have e₂ : EvalExp env ρ (.iterE (.callE "default_" [.expA (.varE "t")])
      (.mk .list [.mk "t" (.varE "t*")])) (.list (ts.map D)) :=
    evalExp_iterMap ft fun t ht => evalExp_call1 (findDef_bind1 hd) (findVal_bind1 (by decide)) (hdef t ht)
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var ff,
    evalExp_str2 (evalExp_cat e₁ e₂) (evalExp_dotE_iff.2 ⟨fv, evalExp_var ffi, hmod⟩),
    by simp [cmpValues, hf]⟩

/-- `$funcinst(z)[a] = fi`, with the state a variable. -/
theorem evalExp_funcinstVarEq {env : Env} {ρ : VarEnv} {z fv : Value} {fs : List Value} {a : Nat}
    (hd : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some z)
    (fa : ρ.findVal? "a" = some (.num (.natN a))) (ffi : ρ.findVal? "fi" = some fv)
    (hfs : Applies env "funcinst" [.val z] (.list fs)) (hget : fs[a]? = some fv) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
      (.varE "fi")) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_idxE_iff.2 ⟨_, a, evalExp_call1 hd fz hfs,
    evalExp_var fa, by simpa [Value.idx?] using hget⟩, evalExp_var ffi, by simp [cmpValues]⟩

/-- `Step/call_ref-func`. -/
theorem sstep_callRefFunc {env : Env} (h : HasRuleAt env "Step" "%~>%" 7 callRefFuncRule)
    {z yy f fv ty mv xv : Value} {ws fs T₁ T₂ ts is : List Value} {D : Value → Value} {a : Nat}
    (hlen : ws.length = T₁.length)
    (hz : TypedV env stateT z) (hn : TypedV env nT (.num (.natN T₁.length)))
    (hw : TypedV env valsT (.list ws)) (ha : TypedV env addrT (.num (.natN a)))
    (hy : TypedV env typeuseT yy) (hm : TypedV env mT (.num (.natN T₂.length)))
    (hf : TypedV env frameT f) (his : TypedV env instrsT (.list is))
    (hfi : TypedV env funcinstT fv) (h₁ : TypedV env valtypesT (.list T₁))
    (h₂ : TypedV env valtypesT (.list T₂)) (hx : TypedV env idxT xv)
    (hts : TypedV env valtypesT (.list ts))
    (hfs : Applies env "funcinst" [.val z] (.list fs)) (hget : fs[a]? = some fv)
    (hty : fv.field? "TYPE" = some ty)
    (hex : DDerives env (otherwise env) "Expand" "%~~%" []
      (.tuple [ty, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])]))
    (hcode : fv.field? "CODE" = some (.case "FUNC" (.tuple [xv, .list (ts.map (.case "LOCAL")),
      .list is])))
    (hmod : fv.field? "MODULE" = some mv)
    (hdef : ∀ t ∈ ts, Applies env "default_" [.val t] (D t))
    (hfeq : f = .struct [("LOCALS", .list (ws.map (fun w => .opt (some w)) ++ ts.map D)),
      ("MODULE", mv)]) :
    SStep env (cfgV z (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy]))
      (cfgV z [.case "FRAME_%{%}%" (.tuple [.num (.natN T₂.length), f,
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN T₂.length), .list [], .list is])]])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", .num (.natN T₁.length)), ("val*", .list ws),
    ("a", .num (.natN a)), ("yy", yy), ("m", .num (.natN T₂.length)), ("f", f),
    ("instr*", .list is), ("fi", fv), ("t_1*", .list T₁), ("t_2*", .list T₂), ("x", xv),
    ("t*", .list ts)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN T₁.length)) := rfl
  have fw : ρ.findVal? "val*" = some (.list ws) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN T₂.length)) := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ffi : ρ.findVal? "fi" = some fv := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list T₁) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list T₂) := rfl
  have fx : ρ.findVal? "x" = some xv := rfl
  have ft : ρ.findVal? "t*" = some (.list ts) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) (hlen ▸ fn) fw
  have elhs : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .catE (valsNPat "val" "val*" "n")
      (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"), .caseE "CALL_REF" (.varE "yy")])]))
      (cfgV z (ws ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy])) :=
    evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_cat evn
      (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fy)))))
  have erhs : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "FRAME_%{%}%"
      (.tupE [.varE "m", .varE "f", .listE [.caseE "LABEL_%{%}%" (.tupE [.varE "m", .listE [],
        iterPat "instr" "instr*"])]])]]))
      (cfgV z [.case "FRAME_%{%}%" (.tuple [.num (.natN T₂.length), f,
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN T₂.length), .list [], .list is])]])]) :=
    evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup3
      (evalExp_var fm) (evalExp_var ff) (evalExp_list1 (evalExp_case (evalExp_tup3
        (evalExp_var fm) evalExp_listNil (evalExp_iterPat (by decide) fi))))))))
  have hfn : ρ.findVal? "n" = some (.num (.natN ws.length)) := hlen ▸ fn
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fw (hw ρ hρ)
      (QuantsOk.cons fa (ha ρ hρ) (QuantsOk.cons fy (hy ρ hρ) (QuantsOk.cons fm (hm ρ hρ)
      (QuantsOk.cons ff (hf ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons ffi (hfi ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons ft (hts ρ hρ) QuantsOk.nil)))))))))))))
    (evalExp_tup2 elhs erhs)
    (fun pr hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl | rfl
      · exact .ifPr (evalExp_funcinstVarEq rfl fz fa ffi hfs hget)
      · exact dprem_expandFi ffi hty fn fm f₁ f₂ hex
      · exact .ifPr (evalExp_funcCodeEq ffi fx ft fi hcode)
      · exact .ifPr (evalExp_frameEq rfl ff ffi hfn fw ft hmod hdef hfeq))

/-! ## The forward field -/

section Fwd

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {host : HostSemantics H}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Tg : CtrlTyping (simEnv B))
  (S : CtrlState (simEnv B) hn) (C : CtrlCall (simEnv B)) (Hs : CtrlHost (simEnv B) hn host)

/-- The empty body. -/
@[simp] theorem instrsToV_nil : instrsToV [] = [] := rfl

/-- `$default_`, read as a function: some value it returns, where it returns one. -/
noncomputable def defaultFn (env : Env) (v : Value) : Value :=
  Classical.epsilon fun r => Applies env "default_" [.val v] r

/-- `defaultFn` is the value `$default_` returns. -/
theorem defaultFn_eq {env : Env} {v r : Value} (h : Applies env "default_" [.val v] r) :
    defaultFn env v = r :=
  Equiv.ExecNumeric.Applies.unique (Classical.epsilon_spec ⟨r, h⟩) h

/-- The code field of a Wasm function instance. -/
theorem funcInstV_code_wasm {fi : FuncInst H} {code : Func} (hc : fi.code = .wasm code) :
    (funcInstV hn fi).field? "CODE" = some (.case "FUNC" (.tuple [pctV code.type.toNat,
      .list ((code.locals.map Encode.toValue).map (.case "LOCAL")), .list (instrsToV code.body)])) := by
  simp [funcInstV, Value.field?, hc, List.map_map, Function.comp_def]

/-- The new frame of a call, encoded. -/
theorem frameV_forCall (env : Env) (C : CtrlDefault env) (m : ModuleInst) (vs : List Val)
    (ts : List ValType) :
    frameV (Frame.forCall m vs ts) = .struct [("LOCALS", .list
      ((vs.map valV).map (fun w => .opt (some w)) ++ (ts.map Encode.toValue).map (defaultFn env))),
      ("MODULE", Equiv.RuntimeBridge.moduleInstToValue CT m)] := by
  have hd : ∀ t ∈ ts, defaultFn env (Encode.toValue t) =
      .opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV) :=
    fun t _ => defaultFn_eq (C.default m t)
  have hmap : (ts.map Encode.toValue).map (defaultFn env) =
      ts.map fun t => .opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV) := by
    rw [List.map_map]
    exact List.map_congr_left fun t ht => hd t ht
  rw [hmap]
  simp [frameV, Frame.forCall, List.map_map, Function.comp_def]

include T Tg S C Hs in
/-- `Forward.callRefFunc`. -/
theorem fwd_callRefFunc : ∀ {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func} (_ : c.IsCallRef)
    (_ : s.funcs[a]? = some fi) (_ : Expand fi.type (.func ps rs)) (_ : vs.length = ps.length)
    (_ : fi.code = .wasm code),
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  intro s f c vs a fi ps rs code hc hfa hex hlen hcode hc₁ hc₂
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨-, hcode₂⟩ := (T.config _).1 hc₂
  obtain ⟨hst, -⟩ := (T.state _ _).1 hz
  obtain ⟨-, hF, hbody⟩ := T.frame _ _ _ hcode₂
  obtain ⟨-, -, hbody'⟩ := T.label _ _ _ hbody
  have his : TypedV (simEnv B) instrsT (.list (instrsToV code.body)) := by
    simpa [adminsToV_expression] using hbody'
  have hcv : TypedV (simEnv B) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv B) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hF' := frameV_forCall (simEnv B) C fi.module vs code.locals
  have key := sstep_callRefFunc (hasStepRules_simEnv B).callRefFunc (z := stateV hn s f)
    (fs := s.funcs.map (funcInstV hn)) (a := a) (D := defaultFn (simEnv B))
    (f := frameV (Frame.forCall fi.module vs code.locals)) hw hz (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (Tg.natM _) hF his (Hs.funcinst s a fi hst hfa)
    (C.valtypes ps) (C.valtypes rs) (Tg.idx code.type) (C.locals code.locals) (S.funcinst s f)
    (funcs_getElem_map hfa) rfl (C.expand _ _ _ hex) (funcInstV_code_wasm hcode) rfl
    (fun t ht => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
      exact (defaultFn_eq (C.default fi.module l)) ▸ C.default fi.module l)
    (by rw [hF', adminsToV_vals])
  simpa [configV, adminsToV_append, hyy, adminsToV_expression, Ty.length] using key

end Fwd

end Silmaril.Wasm.SpecTec.Sim
