module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdMem10T

/-!
# `call_addr` of a Wasm function forward in `simEnv10T`

Round 3's `invokeWasm` leaf at `FwdAt10T`. The callee's code `func` is typed from the store in
`simEnv10T`, so it may contain stores; the new frame and the body are typed from the successor
code in `simEnv10T`.
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
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

theorem findTyp_funcinstG10T : ∃ t₁ t₂, (simEnv10T B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" t₁ [] [], .mk "MODULE" t₂ [] [], .mk "CODE" (.varT "func" []) [] []])]) :=
  let ⟨t₁, t₂, h⟩ := findTyp_funcinstG10 (B := B)
  ⟨t₁, t₂, findTypT_ne h⟩

theorem findTyp_frame10T : (simEnv10T B).findTyp? "frame" = some ([], [.instD [] []
    (.structT [.mk "LOCALS" (.iterT (.varT "val" []) .list) [] [],
      .mk "MODULE" (.varT "moduleinst" []) [] []])]) := findTypT_ne findTyp_frame10

theorem typedV_addr10T (k : Nat) : TypedV (simEnv10T B) (.varT "addr" []) (.num (.natN k)) :=
  typedV10T (typedV_addr10 k)

theorem typedV_admin_of_mem10T {l : List Admin} (h : TypedV (simEnv10T B) adminsT
    (.list (adminsToV l))) {a : Admin} (ha : a ∈ l) : TypedV (simEnv10T B) adminT10 (adminToV a) := by
  rw [adminsToV_map10] at h
  exact typedV_list_iff.1 h _ (List.mem_map_of_mem ha)

/-- A store function of a typed store is a typed `funcinst`. -/
theorem hasTyp_funcinst_of_store10T {s : Store H} (hst : TypedV (simEnv10T B) storeT (storeV hn s))
    {i : Nat} {fi : FuncInst V1.Func H} (hfi : s.funcs[i]? = some fi) :
    HasTyp (simEnv10T B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn fi) := by
  obtain ⟨rest, htd⟩ := findTyp_store10T (B := B)
  have hfs : HasTypFields (simEnv10T B) VarEnv.empty _ _ :=
    Sim20.Whole.hasTypFields_of_closed htd hst
  obtain ⟨w, gs', he, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs
  have ew : w = .list (s.funcs.map (funcInstV hn)) := ((Prod.mk.inj (List.cons.inj he).1).2).symm
  subst ew
  obtain ⟨us, hus, hl⟩ := hasTyp_iterT_list_iff.1 hw
  have eus : us = s.funcs.map (funcInstV hn) := (Value.list.inj hus).symm
  subst eus
  exact hasTypList_iff.1 hl _ (List.mem_map_of_mem (List.mem_of_getElem? hfi))

/-- **The code of a typed Wasm `funcinst` is a typed `func`.** -/
theorem typedV_funcV_of_inst10T {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hi : HasTyp (simEnv10T B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.wasm ft m fn))) :
    TypedV (simEnv10T B) (.varT "func" []) (funcV fn) := by
  obtain ⟨t₁, t₂, htd'⟩ := findTyp_funcinstG10T (B := B)
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
theorem typedV_funcV_of_store10T {s : Store H} (hst : TypedV (simEnv10T B) storeT (storeV hn s))
    {i : Nat} {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hfi : s.funcs[i]? = some (.wasm ft m fn)) : TypedV (simEnv10T B) (.varT "func" []) (funcV fn) :=
  typedV_funcV_of_inst10T (hasTyp_funcinst_of_store10T hst hfi)

/-- The arguments of typed code `values args ++ rest` are typed values. -/
theorem typedV_vals_of_code10T {args : List Execution.Runtime.Value} {rest : List Admin}
    (hc : TypedV (simEnv10T B) adminsT (.list (adminsToV (values args ++ rest)))) :
    TypedV (simEnv10T B) (.iterT (.varT "val" []) .list) (.list (args.map valV)) := by
  refine typedV_list_iff.2 fun u hu => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
  have hmem : value v ∈ values args ++ rest :=
    List.mem_append_left _ (List.mem_map_of_mem hv)
  have ha := typedV_admin_of_mem10T hc hmem
  rw [adminToV_value] at ha
  exact typedV_val_of_admin10T (w := .tuple [valTypeV v.type, numV v]) ha

/-- Every list of V1 value types is a typed `valtype*`. -/
theorem typedV_valtypes10T (ts : List V1.ValType) :
    TypedV (simEnv10T B) (.iterT (.varT "valtype" []) .list) (.list (ts.map valTypeV)) :=
  typedV_list_iff.2 fun _ hu => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_valtype10T t

/-- The new frame and the body, typed from the successor code. -/
theorem typed_callFrame10T {len : Nat} {F : Frame} {body : V1.Expr}
    (hc' : TypedV (simEnv10T B) adminsT
      (.list (adminsToV [.frame len F [.label len [] (expression body)]]))) :
    TypedV (simEnv10T B) frameT (frameV F) ∧
      TypedV (simEnv10T B) instrsT (.list (instrsToV body)) := by
  rw [adminsToV_callFrame10] at hc'
  obtain ⟨-, hF, hb⟩ := frame_inv10T (typedV_list_iff.1 hc' _ (.head _))
  obtain ⟨-, -, hbody⟩ := label_inv10T (typedV_list_iff.1 hb _ (.head _))
  have hb' : TypedV (simEnv10T B) adminsT (.list (adminsToV (expression body))) := by
    rwa [adminsToV_expression]
  have hi := typedV_instrs_of_admins10T (is := body) hb'
  change TypedV _ _ (.list (adminsToV (expression body))) at hi
  rw [adminsToV_expression] at hi
  exact ⟨hF, hi⟩

/-- The typings `call_addr`'s quantifiers need. -/
structure CallAddrTypedT (B : Builtins) (z : Value) (args : List Execution.Runtime.Value)
    (m : ModuleInst) (fn : V1.Func) : Prop where
  hz : TypedV (simEnv10T B) stateT z
  hargs : TypedV (simEnv10T B) (.iterT (.varT "val" []) .list) (.list (args.map valV))
  hF : TypedV (simEnv10T B) frameT (frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩)
  hbody : TypedV (simEnv10T B) instrsT (.list (instrsToV fn.body))
  hfunc : TypedV (simEnv10T B) (.varT "func" []) (funcV fn)

/-- **The quantifiers of `call_addr` are typed in its scope.** -/
theorem callAddr_quantsOkT {z : Value} {args : List Execution.Runtime.Value} {a : FuncAddr}
    {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func} (T : CallAddrTypedT B z args m fn) :
    QuantsOk (simEnv10T B) (VarEnv.empty.bindVals (callAddrScope z args a ft m fn))
      callAddrRule10Qs := by
  have hρ := Sim20.Pure.valsOnly_bindVals (callAddrScope z args a ft m fn)
  have hmm : TypedV (simEnv10T B) (.varT "moduleinst" []) (moduleInstV m) :=
    Sim20.Whole.typedV_of_empty20 (Sim20.Whole.hasTyp_struct2_snd findTyp_frame10T T.hF)
  exact QuantsOk.cons rfl (T.hz _ hρ) (QuantsOk.cons rfl (Sim20.Whole.hasTyp_nat _ _ _)
    (QuantsOk.cons rfl (T.hargs _ hρ) (QuantsOk.cons rfl (typedV_addr10T _ _ hρ)
    (QuantsOk.cons rfl (typedV_n10T _ _ hρ) (QuantsOk.cons rfl (T.hF _ hρ)
    (QuantsOk.cons rfl (T.hbody _ hρ) (QuantsOk.cons rfl (typedV_valtypes10T _ _ hρ)
    (QuantsOk.cons rfl (typedV_valtypes10T _ _ hρ) (QuantsOk.cons rfl (hmm _ hρ)
    (QuantsOk.cons rfl (T.hfunc _ hρ) (QuantsOk.cons rfl (typedV_idxAll10T _ _ hρ)
    (QuantsOk.cons rfl (typedV_valtypes10T _ _ hρ) QuantsOk.nil))))))))))))

/-- **`call_addr` fires forward** at V1's `invokeWasm`, its quantifiers typed. -/
theorem fires10_callAddrT {s : Store H} {f : Frame} {a : FuncAddr} {ft : V1.FuncType}
    {m : ModuleInst} {fn : V1.Func} {args : List Execution.Runtime.Value}
    (T : CallAddrTypedT B (stateV hn s f) args m fn)
    (hfi : s.funcs[a.value]? = some (.wasm ft m fn)) (harity : args.length = ft.params.length) :
    Fires (simEnv10T B) "Step_read" 5 (.tuple [configV hn ⟨s, f, values args ++ [.invoke a]⟩,
      .list (adminsToV [.frame ft.results.length
        ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
        [.label ft.results.length [] (expression fn.body)]])]) := by
  rw [adminsToV_callFrame10]
  refine fires_of_ruleAtT (hasRuleAt10_callAddr B) (callAddrScope (stateV hn s f) args a ft m fn)
    (callAddr_quantsOkT T) (evalExp_tup2 evalExp_callAddrLhs10 (evalExp_callAddrRhs rfl rfl rfl))
    ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl | rfl
  · exact .ifPr (premCA1 hfi harity)
  · exact .ifPr premCA2
  · exact .ifPr premCA3

/-- **`call_addr` of a Wasm function, forward**: V1's `invokeWasm`. -/
theorem fwdAt10T_invokeWasm (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType)
    (m : ModuleInst) (fn : V1.Func) (args : List Execution.Runtime.Value)
    (hfi : s.funcs[a.value]? = some (.wasm ft m fn)) (harity : args.length = ft.params.length) :
    FwdAt10T B hn ⟨s, f, values args ++ [.invoke a]⟩
      ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
        [.label ft.results.length [] (expression fn.body)]]⟩ := by
  refine fun hz _ hc hc' => (StoreFix.sstepB10T_iff B).2 (sstep10_readT hz hc hc' (sread10T_of_fires (k := 5) ?_))
  obtain ⟨hF, hbody⟩ := typed_callFrame10T hc'
  exact fires10_callAddrT ⟨hz, typedV_vals_of_code10T hc, hF, hbody,
    typedV_funcV_of_store10T (typedV_stV_iff10T.1 hz).1 hfi⟩ hfi harity


end Silmaril.Wasm.SpecTec.Sim10.Whole
