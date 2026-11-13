module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WData

/-!
# Module typing of the wasm-3.0 script, the scope of `Module_ok` at memories and data

The scope `modσD mts ds` of `Module_ok` at `mdModuleV mts ds` (memories `mts`, passive data
segments `ds`, nothing else), and the parts of the rule that see the memories or the data:

* `quantsOk_modD`, `evalExp_modConclD`: the quantifiers are typed and the conclusion evaluates;
* `dprem4_D`: `Mem_ok` over the rows `(MEMORY mt, mt)`;
* `dprem7_D`: `Data_ok(C, data, ok)` over the rows `(dataV d, OK)`, in `C = {MEMS mt*, DATAS OK*}`;
* `dprem12_D`: `C = C' ⊕ {…, MEMS [] ++ mt*, …, DATAS ok*, …}` at `C' = {}`;
* `dprem14_D`: `[] = $funcidx_nonfuncs([], MEMORY mt*, [], [], [])` (data segments are not
  arguments of `$funcidx_nonfuncs`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff applies_iff_callDef)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ctxT_empty evalExp_nil pctNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modParams modConcl modPrem4 modPrem7 modPrem12
  modPrem14 mtNil findDef_closMod tryClausesUndef_closMod fd_fnf)
open Silmaril.Wasm.SpecTec.Institution.Instr30Z (memV typedV_memV typedV_memtype evalExp_star
  evalExp_pctStar evalExp_optStarNone iterRows_pair' evalExpFields_cons'' tc_funcidxNonfuncsL
  dd_memOk)

variable {B : Builtins}

/-! ## The scope -/

/-- The `OK`s of the data segments `ds`. -/
def oksV (ds : List Silmaril.Wasm.Data) : List Value := ds.map fun _ => okV

/-- **The scope of `Module_ok` at `mdModuleV mts ds`**: as at `memModuleV mts`, except
`data* = dataV d*`, `ok* = OK*` and `C = {MEMS mt*, DATAS OK*}`. -/
def modσD (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) :
    List (IL.Id × Value) :=
  [("type*", .list []), ("import*", .list []), ("tag*", .list []), ("global*", .list []),
   ("mem*", .list (mts.map memV)), ("table*", .list []), ("func*", .list []),
   ("data*", .list (ds.map dataV)), ("elem*", .list []), ("start?", .opt none), ("export*", .list []),
   ("C", ctxMD (mts.map Encode.toValue) (oksV ds)), ("xt_I*", .list []), ("xt_E*", .list []),
   ("dt'*", .list []), ("C'", Round6.RefOkV.ctxEmptyV), ("jt*", .list []), ("gt*", .list []),
   ("mt*", .list (mts.map Encode.toValue)),
   ("tt*", .list []), ("dt*", .list []), ("ok*", .list (oksV ds)), ("rt*", .list []),
   ("nm*", .list []), ("jt_I*", .list []), ("mt_I*", .list []), ("tt_I*", .list []),
   ("gt_I*", .list []), ("dt_I*", .list []), ("x*", .list [])]

/-- The scope, as a variable environment. -/
abbrev ρD (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) : VarEnv :=
  VarEnv.empty.bindVals (modσD mts ds)

/-- **`C = {MEMS mt*, DATAS OK*}` is typed.** -/
theorem ctxT_md (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) :
    CtxT B (ctxMD (mts.map Encode.toValue) (oksV ds)) :=
  ctxT_ctxMD
    (fun u hu => by
      obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_memtype mt)
    (fun u hu => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_okV)

/-- **`modσD mts ds` is a well-typed assignment of `Module_ok`'s quantifiers.** -/
theorem quantsOk_modD (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) :
    QuantsOk (simEnv B) (ρD mts ds) modParams :=
  have hρ := valsOnly_bind (modσD mts ds)
  have hl {t : Typ} : HasTyp (simEnv B) (ρD mts ds) (.iterT t .list) (.list []) :=
    Round5.RefOk.typedV_listNil _ hρ
  have hc : HasTyp (simEnv B) (ρD mts ds) (.varT "context" []) Round6.RefOkV.ctxEmptyV :=
    ctxT_empty _ hρ
  have hcm : HasTyp (simEnv B) (ρD mts ds) (.varT "context" [])
      (ctxMD (mts.map Encode.toValue) (oksV ds)) := ctxT_md mts ds _ hρ
  have hm : HasTyp (simEnv B) (ρD mts ds) (.iterT (.varT "mem" []) .list) (.list (mts.map memV)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_memV mt) _ hρ
  have hd : HasTyp (simEnv B) (ρD mts ds) (.iterT (.varT "data" []) .list) (.list (ds.map dataV)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_dataV d) _ hρ
  have hok : HasTyp (simEnv B) (ρD mts ds) (.iterT (.varT "datatype" []) .list) (.list (oksV ds)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_okV) _ hρ
  have hmt : HasTyp (simEnv B) (ρD mts ds) (.iterT (.varT "memtype" []) .list)
      (.list (mts.map Encode.toValue)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_memtype mt) _ hρ
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hm <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hd <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl (hasTyp_iterT_opt_iff.2 (.inl rfl)) <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hcm <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hc <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hmt <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hok <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl <|
  QuantsOk.cons rfl hl <| QuantsOk.cons rfl hl QuantsOk.nil

/-! ## The conclusion -/

/-- The module part of the conclusion evaluates to `mdModuleV mts ds`. -/
theorem evalExp_modModuleD (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) :
    EvalExp (simEnv B) (ρD mts ds) modModE (mdModuleV mts ds) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_,
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_optStarNone rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) evalExps_nil, rfl⟩)

/-- **The conclusion evaluates to `(mdModuleV mts ds, v)`** when the primitives answer
`$clos_moduletype({MEMS mt*, DATAS OK*}, [] -> [])` with `v`. -/
theorem evalExp_modConclD (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data)
    {v : Value} (hB : B.call "clos_moduletype"
      [.val (ctxMD (mts.map Encode.toValue) (oksV ds)), .val mtNil] = some v) :
    EvalExp (simEnv B) (ρD mts ds) modConcl (.tuple [mdModuleV mts ds, v]) := by
  obtain ⟨ps, t, hd⟩ := findDef_closMod (B := B)
  have hargs : EvalArgs (simEnv B) (ρD mts ds)
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))]
      [.val (ctxMD (mts.map Encode.toValue) (oksV ds)), .val mtNil] :=
    Equiv.evalArgs_cons (Sim.evalExp_var rfl) (Equiv.evalArgs_cons
      (evalExp_case (evalExp_tup2 (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)))
      Equiv.evalArgs_nil)
  have hcall : EvalExp (simEnv B) (ρD mts ds) closE v := by
    refine evalExp_callE_iff.2 (callDef_iff.2 ⟨_, ps, t, Instr30X.closModClauses, hargs, ?_,
      .inr ⟨tryClausesUndef_closMod _ _, ?_⟩⟩)
    · rw [Memory.findDef_bindVals_empty, Option.getD_none]
      exact hd
    · rw [Memory.findDef_bindVals_empty, Option.getD_none, simEnv, Env.builtins_withBuiltins]
      exact hB
  rw [modConcl_eq]
  exact evalExp_tup2 (evalExp_modModuleD mts ds) hcall

/-! ## The premises that see the memories or the data -/

/-- **Premise 4, `Mem_ok(C', mem, mt)` over `mem* = MEMORY mt*`**, when Core validates every
`mt ∈ mts`. -/
theorem dprem4_D {mts : List Silmaril.Wasm.MemoryType} (ds : List Silmaril.Wasm.Data)
    (hv : ∀ mt ∈ mts, mt.Valid) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρD mts ds) modPrem4 :=
  .iterList (k := mts.length) (.inl rfl)
    (xvs := [("mem", .list (mts.map memV)), ("mt", .list (mts.map Encode.toValue))])
    ⟨5, by simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρD, modσD,
      Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure]⟩
    (by simp) (dls := [("mem", mts.map memV), ("mt", mts.map Encode.toValue)])
    (by simp [domLists, Value.asList?]) (by simp) (by
      intro r hr
      rw [iterRows_pair'] at hr
      obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hr
      exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)) (dd_memOk O Instr30.ctxT_empty (hv mt hmt)))

/-- **Premise 7, `Data_ok(C, data, ok)` over `data* = dataV d*` and `ok* = OK*`**, at every list of
data segments. -/
theorem dprem7_D (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) (O : ElseI)
    (els : Prop) : DPremB (simEnv B) O els (ρD mts ds) modPrem7 :=
  .iterList (k := ds.length) (.inl rfl)
    (xvs := [("data", .list (ds.map dataV)), ("ok", .list (oksV ds))])
    ⟨5, by simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρD, modσD,
      Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure]⟩
    (by simp) (dls := [("data", ds.map dataV), ("ok", oksV ds)])
    (by simp [domLists, Value.asList?]) (by simp [oksV]) (by
      intro r hr
      rw [oksV, iterRows_pair'] at hr
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hr
      exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)) (dd_dataOk O (ctxT_md mts ds) d))

/-- The record premise 12 adds to `C'`, at `mdModuleV mts ds`. -/
theorem evalExp_prem12RecD (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) :
    EvalExp (simEnv B) (ρD mts ds) (match modPrem12 with
      | .ifPr (.cmpE _ _ _ (.compE _ e)) => e | _ => .listE [])
      (ctxMD (mts.map Encode.toValue) (oksV ds)) :=
  evalExp_strE_iff.2 ⟨_,
    evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' (evalExp_cat (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)) <|
    evalExpFields_cons'' (evalExp_star (by decide) rfl) <|
    evalExpFields_cons'' (evalExp_cat (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)) <|
    evalExpFields_cons'' (evalExp_cat (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)) <|
    evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' (evalExp_star (by decide) rfl) <|
    evalExpFields_cons'' (evalExp_star (by decide) rfl) <|
    evalExpFields_cons'' evalExp_nil <| evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' (evalExp_optE_none_iff.2 rfl) <| evalExpFields_cons'' evalExp_nil <|
    evalExpFields_cons'' evalExp_nil ⟨1, by simp [evalExpFields]; rfl⟩, rfl⟩

/-- **Premise 12, `C = C' ⊕ {…}`, holds at `mdModuleV mts ds`.** -/
theorem dprem12_D (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) (O : ElseI)
    (els : Prop) : DPremB (simEnv B) O els (ρD mts ds) modPrem12 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, evalExp_compE_iff.2 ⟨_, _,
    Sim.evalExp_var rfl, evalExp_prem12RecD mts ds, rfl⟩,
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

/-- **Premise 14, `x* = $funcidx_nonfuncs(…)`, holds at `mdModuleV mts ds`.** -/
theorem dprem14_D (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) (O : ElseI)
    (els : Prop) : DPremB (simEnv B) O els (ρD mts ds) modPrem14 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_star (by decide) rfl,
    evalExp_callE_iff.2 ((applies_iff_callDef (Memory.findDef_bindVals_empty _ _)
      (Equiv.evalArgs_cons (evalExp_case (evalExp_tupE_iff.2 ⟨_,
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) <|
        evalExps_cons (evalExp_star (by decide) rfl) evalExps_nil, rfl⟩)) Equiv.evalArgs_nil)).1
        ⟨_, _, _, fd_fnf, .inl (tc_funcidxNonfuncsL mts)⟩),
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

end Silmaril.Wasm.SpecTec.Institution.Instr30W
