module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdMem
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRed

/-!
# The 1.0 script forward at `call_addr` of a Wasm function

`Step_read/call_addr` (5, round 2's `callAddrRule10`) opens the callee's frame and its body's
label in one step, as V1's `invokeWasm` does. Forward, its thirteen quantifiers are bound to the
images of V1's pieces and typed:

* `z` from the typed state, `k`, `n`, `a`, `x` and the three `valtype*` from their shapes;
* `val*` from the typed code (each argument is a typed `val`, `typedV_vals_of_code10`);
* `f` and `instr*` from the typed successor code: the new frame is the `FRAME_`'s frame, and the
  body the `LABEL_`'s (`frame_inv10`, `label_inv10`, then `typedV_instrs_of_admins10`);
* `mm` from the new frame's `MODULE` field, and `func` from the typed store: the callee's
  `funcinst` has `CODE func` (`typedV_funcV_of_store10`).

The three premises are evaluated at the images: `$funcinst(z)[a]` is the callee's record
(`premCA1`), `func = FUNC x (LOCAL t)* instr*` (`premCA2`), and the new frame is
`{LOCALS val^k ($default_(t))*, MODULE mm}` (`premCA3`, through round 2's `evalExp_default10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value values expression)
open Silmaril.Wasm.Execution.Runtime (Frame FuncInst FuncAddr ModuleInst)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV PremW ValsOnly stateT storeT frameT instrsT
  evalExp_case evalExp_tup2 evalExp_tup3 evalExp_cat evalExp_iterMap evalExp_iterNMap evalExp_str2
  findVal_bind1 typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Evaluation helpers -/

/-- A three-field record, evaluated. -/
theorem evalExp_str3 {env : Env} {ρ : VarEnv} {a₁ a₂ a₃ : AtomS} {e₁ e₂ e₃ : Exp}
    {v₁ v₂ v₃ : Value} (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂)
    (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.strE [.mk a₁ e₁, .mk a₂ e₂, .mk a₃ e₃])
      (.struct [(a₁, v₁), (a₂, v₂), (a₃, v₃)]) := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨n₃, h₃⟩ := h₃
  have g₁ : evalExp (max n₁ (max n₂ n₃)) env ρ e₁ = .ok v₁ := evalExp_ok_of_le (by omega) h₁
  have g₂ : evalExp (max n₁ (max n₂ n₃)) env ρ e₂ = .ok v₂ := evalExp_ok_of_le (by omega) h₂
  have g₃ : evalExp (max n₁ (max n₂ n₃)) env ρ e₃ = .ok v₃ := evalExp_ok_of_le (by omega) h₃
  refine evalExp_strE_iff.2 ⟨_, ⟨max n₁ (max n₂ n₃) + 1, ?_⟩, rfl⟩
  simp [evalExpFields, g₁, g₂, g₃]

/-- `x^c` over a bound list, evaluated. -/
theorem evalExp_iterNVar {env : Env} {ρ : VarEnv} {x y c : IL.Id} {ws : List Value}
    (hx : x ≠ "_") (hc : ρ.findVal? c = some (.num (.natN ws.length)))
    (hy : ρ.findVal? y = some (.list ws)) :
    EvalExp env ρ (.iterE (.varE x) (.mk (.listN (.varE c) none) [.mk x (.varE y)])) (.list ws) := by
  have h := evalExp_iterNMap (env := env) (b := .varE x) (g := id) hc hy fun _ _ =>
    Sim.evalExp_var (findVal_bind1 hx)
  simpa using h

/-- The image of `values args ++ [CALL_ADDR a]`. -/
theorem adminsToV_invoke10 (args : List Execution.Runtime.Value) (a : FuncAddr) :
    adminsToV (values args ++ [.invoke a]) =
      args.map valV ++ [.case "CALL_ADDR" (.num (.natN a.value))] := by
  rw [adminsToV_map10, List.map_append, ← adminsToV_map10, adminsToV_values]
  rfl

/-! ## The quantifier typings -/

set_option maxRecDepth 8000000 in
theorem findTyp_funcinstG10 : ∃ t₁ t₂, (simEnv10 B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" t₁ [] [], .mk "MODULE" t₂ [] [], .mk "CODE" (.varT "func" []) [] []])]) :=
  ⟨_, _, rfl⟩

/-- A store function of a typed store is a typed `funcinst`. -/
theorem hasTyp_funcinst_of_store10 {s : Store H} (hst : TypedV (simEnv10 B) storeT (storeV hn s))
    {i : Nat} {fi : FuncInst V1.Func H} (hfi : s.funcs[i]? = some fi) :
    HasTyp (simEnv10 B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn fi) := by
  obtain ⟨rest, htd⟩ := findTyp_store10 (B := B)
  have hfs : HasTypFields (simEnv10 B) VarEnv.empty _ _ :=
    Sim20.Whole.hasTypFields_of_closed htd hst
  obtain ⟨w, gs', he, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs
  have ew : w = .list (s.funcs.map (funcInstV hn)) := ((Prod.mk.inj (List.cons.inj he).1).2).symm
  subst ew
  obtain ⟨us, hus, hl⟩ := hasTyp_iterT_list_iff.1 hw
  have eus : us = s.funcs.map (funcInstV hn) := (Value.list.inj hus).symm
  subst eus
  exact hasTypList_iff.1 hl _ (List.mem_map_of_mem (List.mem_of_getElem? hfi))

/-- **The code of a typed Wasm `funcinst` is a typed `func`.** -/
theorem typedV_funcV_of_inst10 {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hi : HasTyp (simEnv10 B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.wasm ft m fn))) :
    TypedV (simEnv10 B) (.varT "func" []) (funcV fn) := by
  obtain ⟨t₁, t₂, htd'⟩ := findTyp_funcinstG10 (B := B)
  obtain ⟨gs, hg, hfs'⟩ := hasTypDef_structT_iff.1 (Sim20.Whole.hasTypDef_of_closed htd' hi)
  have egs : gs = [("TYPE", funcTypeV ft), ("MODULE", moduleInstV m), ("CODE", funcV fn)] :=
    (Value.struct.inj hg).symm
  subst egs
  obtain ⟨w₁, gs₁, he₁, -, -, hfs₁⟩ := hasTypFields_cons_iff.1 hfs'
  have e₁ : gs₁ = [("MODULE", moduleInstV m), ("CODE", funcV fn)] := (List.cons.inj he₁).2.symm
  subst e₁
  obtain ⟨w₂, gs₂, he₂, -, -, hfs₂⟩ := hasTypFields_cons_iff.1 hfs₁
  have e₂ : gs₂ = [("CODE", funcV fn)] := (List.cons.inj he₂).2.symm
  subst e₂
  obtain ⟨w₃, gs₃, he₃, hw₃, -, -⟩ := hasTypFields_cons_iff.1 hfs₂
  have e₃ : w₃ = funcV fn := ((Prod.mk.inj (List.cons.inj he₃).1).2).symm
  subst e₃
  exact Sim20.Whole.typedV_of_empty20 hw₃

/-- **The code of a store function is a typed `func`.** -/
theorem typedV_funcV_of_store10 {s : Store H} (hst : TypedV (simEnv10 B) storeT (storeV hn s))
    {i : Nat} {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hfi : s.funcs[i]? = some (.wasm ft m fn)) : TypedV (simEnv10 B) (.varT "func" []) (funcV fn) :=
  typedV_funcV_of_inst10 (hasTyp_funcinst_of_store10 hst hfi)

/-- The arguments of typed code `values args ++ rest` are typed values. -/
theorem typedV_vals_of_code10 {args : List Execution.Runtime.Value} {rest : List Admin}
    (hc : TypedV (simEnv10 B) adminsT (.list (adminsToV (values args ++ rest)))) :
    TypedV (simEnv10 B) (.iterT (.varT "val" []) .list) (.list (args.map valV)) := by
  refine typedV_list_iff.2 fun u hu => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
  have hmem : value v ∈ values args ++ rest :=
    List.mem_append_left _ (List.mem_map_of_mem hv)
  have ha := typedV_admin_of_mem10 hc hmem
  rw [adminToV_value] at ha
  exact typedV_val_of_admin10 (w := .tuple [valTypeV v.type, numV v]) ha

/-- Every list of V1 value types is a typed `valtype*`. -/
theorem typedV_valtypes10 (ts : List V1.ValType) :
    TypedV (simEnv10 B) (.iterT (.varT "valtype" []) .list) (.list (ts.map valTypeV)) :=
  typedV_list_iff.2 fun _ hu => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_valtype10 t

/-- The new frame and the body, typed from the successor code. -/
theorem typed_callFrame10 {len : Nat} {F : Frame} {body : V1.Expr}
    (hc' : TypedV (simEnv10 B) adminsT
      (.list (adminsToV [.frame len F [.label len [] (expression body)]]))) :
    TypedV (simEnv10 B) frameT (frameV F) ∧
      TypedV (simEnv10 B) instrsT (.list (instrsToV body)) := by
  rw [adminsToV_callFrame10] at hc'
  obtain ⟨-, hF, hb⟩ := frame_inv10 (typedV_list_iff.1 hc' _ (.head _))
  obtain ⟨-, -, hbody⟩ := label_inv10 (typedV_list_iff.1 hb _ (.head _))
  have hb' : TypedV (simEnv10 B) adminsT (.list (adminsToV (expression body))) := by
    rwa [adminsToV_expression]
  have hi := typedV_instrs_of_admins10 (is := body) hb'
  change TypedV _ _ (.list (adminsToV (expression body))) at hi
  rw [adminsToV_expression] at hi
  exact ⟨hF, hi⟩

/-! ## The scope -/

/-- The scope of `call_addr` at V1's `invokeWasm`. -/
abbrev callAddrScope (z : Value) (args : List Execution.Runtime.Value) (a : FuncAddr)
    (ft : V1.FuncType) (m : ModuleInst) (fn : V1.Func) : List (IL.Id × Value) :=
  [("z", z), ("k", .num (.natN args.length)), ("val*", .list (args.map valV)),
    ("a", .num (.natN a.value)), ("n", .num (.natN ft.results.length)),
    ("f", frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩),
    ("instr*", .list (instrsToV fn.body)), ("t_1*", .list (ft.params.map valTypeV)),
    ("t_2*", .list (ft.results.map valTypeV)), ("mm", moduleInstV m), ("func", funcV fn),
    ("x", idxV fn.type), ("t*", .list (fn.locals.map valTypeV))]

/-- The typings `call_addr`'s quantifiers need. -/
structure CallAddrTyped (B : Builtins) (z : Value) (args : List Execution.Runtime.Value)
    (m : ModuleInst) (fn : V1.Func) : Prop where
  hz : TypedV (simEnv10 B) stateT z
  hargs : TypedV (simEnv10 B) (.iterT (.varT "val" []) .list) (.list (args.map valV))
  hF : TypedV (simEnv10 B) frameT (frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩)
  hbody : TypedV (simEnv10 B) instrsT (.list (instrsToV fn.body))
  hfunc : TypedV (simEnv10 B) (.varT "func" []) (funcV fn)

/-- **The quantifiers of `call_addr` are typed in its scope.** -/
theorem callAddr_quantsOk {z : Value} {args : List Execution.Runtime.Value} {a : FuncAddr}
    {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func} (T : CallAddrTyped B z args m fn) :
    QuantsOk (simEnv10 B) (VarEnv.empty.bindVals (callAddrScope z args a ft m fn))
      callAddrRule10Qs := by
  have hρ := Sim20.Pure.valsOnly_bindVals (callAddrScope z args a ft m fn)
  have hmm : TypedV (simEnv10 B) (.varT "moduleinst" []) (moduleInstV m) :=
    Sim20.Whole.typedV_of_empty20 (Sim20.Whole.hasTyp_struct2_snd findTyp_frame10 T.hF)
  exact QuantsOk.cons rfl (T.hz _ hρ) (QuantsOk.cons rfl (Sim20.Whole.hasTyp_nat _ _ _)
    (QuantsOk.cons rfl (T.hargs _ hρ) (QuantsOk.cons rfl (typedV_addr10 _ _ hρ)
    (QuantsOk.cons rfl (typedV_n10 _ _ hρ) (QuantsOk.cons rfl (T.hF _ hρ)
    (QuantsOk.cons rfl (T.hbody _ hρ) (QuantsOk.cons rfl (typedV_valtypes10 _ _ hρ)
    (QuantsOk.cons rfl (typedV_valtypes10 _ _ hρ) (QuantsOk.cons rfl (hmm _ hρ)
    (QuantsOk.cons rfl (T.hfunc _ hρ) (QuantsOk.cons rfl (typedV_idxAll10 _ _ hρ)
    (QuantsOk.cons rfl (typedV_valtypes10 _ _ hρ) QuantsOk.nil))))))))))))

/-! ## The premises, forward -/

section Prems

variable {s : Store H} {f : Frame} {args : List Execution.Runtime.Value} {a : FuncAddr}
  {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}

/-- `funcTypeE`, at the callee's type. -/
theorem evalExp_funcTypeE10 (harity : args.length = ft.params.length) :
    EvalExp (simEnv10 B)
      (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)) funcTypeE
      (funcTypeV ft) := by
  have fk : (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)).findVal? "k" =
      some (.num (.natN (ft.params.map valTypeV).length)) := by
    rw [List.length_map, ← harity]
    rfl
  have fn' : (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)).findVal? "n" =
      some (.num (.natN (ft.results.map valTypeV).length)) := by
    rw [List.length_map]
    rfl
  exact evalExp_case (evalExp_tup2 (evalExp_iterNVar (by decide) fk rfl)
    (evalExp_iterNVar (by decide) fn' rfl))

/-- **The first premise**: `$funcinst(z)[a]` is the callee's record. -/
theorem premCA1 (hfi : s.funcs[a.value]? = some (.wasm ft m fn))
    (harity : args.length = ft.params.length) :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
        (.strE [.mk "TYPE" funcTypeE, .mk "MODULE" (.varE "mm"), .mk "CODE" (.varE "func")]))
      (.bool true) := by
  have h₁ : EvalExp (simEnv10 B)
      (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) (funcInstV hn (.wasm ft m fn)) :=
    evalExp_idxE_iff.2 ⟨_, a.value, evalExp_funcinst10 rfl rfl, Sim.evalExp_var rfl,
      by simp [Value.idx?, List.getElem?_map, hfi]⟩
  have h₂ := evalExp_str3 (a₁ := "TYPE") (a₂ := "MODULE") (a₃ := "CODE")
    (evalExp_funcTypeE10 (B := B) (hn := hn) (s := s) (f := f) (a := a) (m := m) (fn := fn) harity)
    (Sim.evalExp_var (x := "mm") (v := moduleInstV m) rfl)
    (Sim.evalExp_var (x := "func") (v := funcV fn) rfl)
  exact evalExp_cmpE_iff.2 ⟨_, _, h₁, h₂, cmpValues_eq_true_iff.2 rfl⟩

/-- **The second premise**: `func = FUNC x (LOCAL t)* instr*`. -/
theorem premCA2 :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.cmpE .eqOp .boolT (.varE "func") funcE) (.bool true) := by
  have hl : EvalExp (simEnv10 B)
      (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]))
      (.list ((fn.locals.map valTypeV).map (.case "LOCAL"))) :=
    evalExp_iterMap rfl fun _ _ => evalExp_case (Sim.evalExp_var (findVal_bind1 (by decide)))
  have h₂ : EvalExp (simEnv10 B)
      (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)) funcE (funcV fn) := by
    have h := evalExp_case (op := "FUNC") (evalExp_tup3
      (Sim.evalExp_var (x := "x") (v := idxV fn.type) rfl) hl
      (Sim20.Pure.evalExp_iter (x := "instr") (y := "instr*") (by decide)
        (vs := instrsToV fn.body) rfl))
    simpa [funcV, List.map_map, Function.comp_def] using h
  exact evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var (x := "func") rfl, h₂,
    cmpValues_eq_true_iff.2 rfl⟩

/-- **The third premise**: the new frame is `{LOCALS val^k ($default_(t))*, MODULE mm}`. -/
theorem premCA3 :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.cmpE .eqOp .boolT (.varE "f") frameE) (.bool true) := by
  have fk : (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)).findVal? "k" =
      some (.num (.natN (args.map valV).length)) := by
    rw [List.length_map]
    rfl
  have e₁ := evalExp_iterNVar (env := simEnv10 B) (x := "val") (y := "val*") (by decide) fk rfl
  have e₂ : EvalExp (simEnv10 B)
      (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.iterE (.callE "default_" [.expA (.varE "t")]) (.mk .list [.mk "t" (.varE "t*")]))
      (.list ((fn.locals.map valTypeV).map fun w => valV (Execution.Runtime.Value.zero (vtOf w)))) :=
    evalExp_iterMap rfl fun w hw => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hw
      rw [vtOf_valTypeV]
      exact evalExp_default10 t rfl (Sim.evalExp_var (findVal_bind1 (by decide)))
  have e₃ := evalExp_str2 (a₁ := "LOCALS") (a₂ := "MODULE") (evalExp_cat e₁ e₂)
    (Sim.evalExp_var (x := "mm") (v := moduleInstV m) rfl)
  have hv : Value.struct [("LOCALS", .list (args.map valV ++ (fn.locals.map valTypeV).map
      fun w => valV (Execution.Runtime.Value.zero (vtOf w)))), ("MODULE", moduleInstV m)] =
      frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩ := by
    simp [frameV, List.map_map, Function.comp_def, vtOf_valTypeV]
  exact evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var (x := "f") rfl, e₃,
    cmpValues_eq_true_iff.2 hv.symm⟩

/-- The left-hand side `z; val^k (CALL_ADDR a)`, evaluated. -/
theorem evalExp_callAddrLhs10 :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn))
      (.caseE "%;%" (.tupE [.varE "z", .catE valsKE (.listE [.caseE "CALL_ADDR" (.varE "a")])]))
      (configV hn ⟨s, f, values args ++ [.invoke a]⟩) := by
  have fk : (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)).findVal? "k" =
      some (.num (.natN (args.map valV).length)) := by
    rw [List.length_map]
    rfl
  have hv : EvalExp (simEnv10 B)
      (VarEnv.empty.bindVals (callAddrScope (stateV hn s f) args a ft m fn)) valsKE
      (.list (args.map valV)) := by
    have h := evalExp_iterNMap (env := simEnv10 B) (x := "val") (y := "val*")
      (b := .subE (.varE "val") (.varT "val" []) (.varT "admininstr" [])) (g := id) fk rfl
      fun _ _ =>
      evalExp_subE_iff.2 (Sim.evalExp_var (findVal_bind1 (by decide)))
    simpa using h
  rw [configV_eq_cfgV10, adminsToV_invoke10]
  exact evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl)
    (evalExp_cat hv (Sim.evalExp_list1 (evalExp_case (Sim.evalExp_var rfl)))))

end Prems

/-! ## `call_addr`, forward -/

/-- **`call_addr` fires forward** at V1's `invokeWasm`, its quantifiers typed. -/
theorem fires10_callAddr {s : Store H} {f : Frame} {a : FuncAddr} {ft : V1.FuncType}
    {m : ModuleInst} {fn : V1.Func} {args : List Execution.Runtime.Value}
    (T : CallAddrTyped B (stateV hn s f) args m fn)
    (hfi : s.funcs[a.value]? = some (.wasm ft m fn)) (harity : args.length = ft.params.length) :
    Fires (simEnv10 B) "Step_read" 5 (.tuple [configV hn ⟨s, f, values args ++ [.invoke a]⟩,
      .list (adminsToV [.frame ft.results.length
        ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
        [.label ft.results.length [] (expression fn.body)]])]) := by
  rw [adminsToV_callFrame10]
  refine fires_of_ruleAt (hasRuleAt10_callAddr B) (callAddrScope (stateV hn s f) args a ft m fn)
    (callAddr_quantsOk T) (evalExp_tup2 evalExp_callAddrLhs10 (evalExp_callAddrRhs rfl rfl rfl))
    ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl | rfl
  · exact .ifPr (premCA1 hfi harity)
  · exact .ifPr premCA2
  · exact .ifPr premCA3

/-- **`call_addr` of a Wasm function, forward**: V1's `invokeWasm`. -/
theorem fwdAt10_invokeWasm (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType)
    (m : ModuleInst) (fn : V1.Func) (args : List Execution.Runtime.Value)
    (hfi : s.funcs[a.value]? = some (.wasm ft m fn)) (harity : args.length = ft.params.length) :
    FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩
      ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
        [.label ft.results.length [] (expression fn.body)]]⟩ := by
  refine fun hz _ hc hc' => (sstepB10_iff B).2 (sstep10_read hz hc hc' (sread10_of_fires (k := 5) ?_))
  obtain ⟨hF, hbody⟩ := typed_callFrame10 hc'
  exact fires10_callAddr ⟨hz, typedV_vals_of_code10 hc, hF, hbody,
    typedV_funcV_of_store10 (typedV_stV_iff10.1 hz).1 hfi⟩ hfi harity

end Silmaril.Wasm.SpecTec.Sim10.Whole
