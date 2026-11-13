module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30VConst

/-!
# Module typing of the wasm-3.0 script, ws5 the scope of `Module_ok` at data images

The scope `modσV mts dvs` of `Module_ok` at `mdvModuleV mts dvs` (memories `mts`, arbitrary data
images `dvs`, nothing else), and the parts of the rule that see the memories or the data. This is
`Instr30WModD` with `dataV d*` replaced by any list of values; the data images enter only through
their typing (`quantsOk_modV`) and through premise 7 (`dprem7_V`):

* `quantsOk_modV`, `evalExp_modConclV`: the quantifiers are typed when every image is a `data`, and
  the conclusion evaluates;
* `dprem4_V`: `Mem_ok` over the rows `(MEMORY mt, mt)`;
* `dprem7_V`: `Data_ok(C, data, OK)` over `data* = dvs`, in `C = {MEMS mt*, DATAS OK*}`, from a
  `Data_ok` fact at every image;
* `dprem12_V`, `dprem14_V`: as in `Instr30WModD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

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
open Silmaril.Wasm.SpecTec.Institution.Instr30W (ctxMD okV ctxT_ctxMD typedV_okV modModE closE
  modConcl_eq)

variable {B : Builtins}

/-! ## The scope -/

/-- One `OK` per data image. -/
def oksL (dvs : List Value) : List Value := dvs.map fun _ => okV

/-- `C = {MEMS mt*, DATAS OK*}` at the memories `mts` and the data images `dvs`. -/
abbrev ctxV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) : Value :=
  ctxMD (mts.map Encode.toValue) (oksL dvs)

/-- **The scope of `Module_ok` at `mdvModuleV mts dvs`**: as `Instr30W.modσD`, with
`data* = dvs`. -/
def modσV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) : List (IL.Id × Value) :=
  [("type*", .list []), ("import*", .list []), ("tag*", .list []), ("global*", .list []),
   ("mem*", .list (mts.map memV)), ("table*", .list []), ("func*", .list []),
   ("data*", .list dvs), ("elem*", .list []), ("start?", .opt none), ("export*", .list []),
   ("C", ctxV mts dvs), ("xt_I*", .list []), ("xt_E*", .list []),
   ("dt'*", .list []), ("C'", Round6.RefOkV.ctxEmptyV), ("jt*", .list []), ("gt*", .list []),
   ("mt*", .list (mts.map Encode.toValue)),
   ("tt*", .list []), ("dt*", .list []), ("ok*", .list (oksL dvs)), ("rt*", .list []),
   ("nm*", .list []), ("jt_I*", .list []), ("mt_I*", .list []), ("tt_I*", .list []),
   ("gt_I*", .list []), ("dt_I*", .list []), ("x*", .list [])]

/-- The scope, as a variable environment. -/
abbrev ρV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) : VarEnv :=
  VarEnv.empty.bindVals (modσV mts dvs)

/-- **`C = {MEMS mt*, DATAS OK*}` is typed.** -/
theorem ctxT_v (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) : CtxT B (ctxV mts dvs) :=
  ctxT_ctxMD
    (fun u hu => by
      obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_memtype mt)
    (fun u hu => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_okV)

/-- **`modσV mts dvs` is a well-typed assignment of `Module_ok`'s quantifiers** when every image
is a `data`. -/
theorem quantsOk_modV (mts : List Silmaril.Wasm.MemoryType) {dvs : List Value}
    (hdv : ∀ dv ∈ dvs, TypedV (simEnv B) (.varT "data" []) dv) :
    QuantsOk (simEnv B) (ρV mts dvs) modParams :=
  have hρ := valsOnly_bind (modσV mts dvs)
  have hl {t : Typ} : HasTyp (simEnv B) (ρV mts dvs) (.iterT t .list) (.list []) :=
    Round5.RefOk.typedV_listNil _ hρ
  have hc : HasTyp (simEnv B) (ρV mts dvs) (.varT "context" []) Round6.RefOkV.ctxEmptyV :=
    ctxT_empty _ hρ
  have hcm : HasTyp (simEnv B) (ρV mts dvs) (.varT "context" []) (ctxV mts dvs) :=
    ctxT_v mts dvs _ hρ
  have hm : HasTyp (simEnv B) (ρV mts dvs) (.iterT (.varT "mem" []) .list) (.list (mts.map memV)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_memV mt) _ hρ
  have hd : HasTyp (simEnv B) (ρV mts dvs) (.iterT (.varT "data" []) .list) (.list dvs) :=
    typedV_list_iff.2 hdv _ hρ
  have hok : HasTyp (simEnv B) (ρV mts dvs) (.iterT (.varT "datatype" []) .list) (.list (oksL dvs)) :=
    typedV_list_iff.2 (fun u hu => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
      exact typedV_okV) _ hρ
  have hmt : HasTyp (simEnv B) (ρV mts dvs) (.iterT (.varT "memtype" []) .list)
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

/-- The module part of the conclusion evaluates to `mdvModuleV mts dvs`. -/
theorem evalExp_modModuleV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) :
    EvalExp (simEnv B) (ρV mts dvs) modModE (mdvModuleV mts dvs) :=
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

/-- **The conclusion evaluates to `(mdvModuleV mts dvs, v)`** when the primitives answer
`$clos_moduletype({MEMS mt*, DATAS OK*}, [] -> [])` with `v`. -/
theorem evalExp_modConclV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value)
    {v : Value} (hB : B.call "clos_moduletype" [.val (ctxV mts dvs), .val mtNil] = some v) :
    EvalExp (simEnv B) (ρV mts dvs) modConcl (.tuple [mdvModuleV mts dvs, v]) := by
  obtain ⟨ps, t, hd⟩ := findDef_closMod (B := B)
  have hargs : EvalArgs (simEnv B) (ρV mts dvs)
      [.expA (.varE "C"), .expA (.caseE "%->%" (.tupE [
        .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
        .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])]))]
      [.val (ctxV mts dvs), .val mtNil] :=
    Equiv.evalArgs_cons (Sim.evalExp_var rfl) (Equiv.evalArgs_cons
      (evalExp_case (evalExp_tup2 (evalExp_star (by decide) rfl) (evalExp_star (by decide) rfl)))
      Equiv.evalArgs_nil)
  have hcall : EvalExp (simEnv B) (ρV mts dvs) closE v := by
    refine evalExp_callE_iff.2 (callDef_iff.2 ⟨_, ps, t, Instr30X.closModClauses, hargs, ?_,
      .inr ⟨tryClausesUndef_closMod _ _, ?_⟩⟩)
    · rw [Memory.findDef_bindVals_empty, Option.getD_none]
      exact hd
    · rw [Memory.findDef_bindVals_empty, Option.getD_none, simEnv, Env.builtins_withBuiltins]
      exact hB
  rw [modConcl_eq]
  exact evalExp_tup2 (evalExp_modModuleV mts dvs) hcall

/-! ## The premises that see the memories or the data -/

/-- **Premise 4, `Mem_ok(C', mem, mt)` over `mem* = MEMORY mt*`**, when Core validates every
`mt ∈ mts`. -/
theorem dprem4_V {mts : List Silmaril.Wasm.MemoryType} (dvs : List Value)
    (hv : ∀ mt ∈ mts, mt.Valid) (O : ElseI) (els : Prop) :
    DPremB (simEnv B) O els (ρV mts dvs) modPrem4 :=
  .iterList (k := mts.length) (.inl rfl)
    (xvs := [("mem", .list (mts.map memV)), ("mt", .list (mts.map Encode.toValue))])
    ⟨5, by simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure]⟩
    (by simp) (dls := [("mem", mts.map memV), ("mt", mts.map Encode.toValue)])
    (by simp [domLists, Value.asList?]) (by simp) (by
      intro r hr
      rw [iterRows_pair'] at hr
      obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hr
      exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)) (dd_memOk O Instr30.ctxT_empty (hv mt hmt)))

/-- **Premise 7, `Data_ok(C, data, ok)` over `data* = dvs` and `ok* = OK*`**, when every image has
a `Data_ok` fact in `C`. -/
theorem dprem7_V (mts : List Silmaril.Wasm.MemoryType) {dvs : List Value} (O : ElseI)
    (hdd : ∀ dv ∈ dvs, DDerivesB (simEnv B) O "Data_ok" "%|-%:%" [] (.tuple [ctxV mts dvs, dv, okV]))
    (els : Prop) : DPremB (simEnv B) O els (ρV mts dvs) modPrem7 :=
  .iterList (k := dvs.length) (.inl rfl)
    (xvs := [("data", .list dvs), ("ok", .list (oksL dvs))])
    ⟨5, by simp [evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals, ρV, modσV,
      Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure]⟩
    (by simp) (dls := [("data", dvs), ("ok", oksL dvs)])
    (by simp [domLists, Value.asList?]) (by simp [oksL]) (by
      intro r hr
      have e : iterRows [("data", dvs), ("ok", oksL dvs)] none dvs.length =
          dvs.map fun dv => [("data", dv), ("ok", okV)] := by
        have := iterRows_pair' (x₁ := "data") (x₂ := "ok") (g₁ := id) (g₂ := fun _ => okV) dvs
        rwa [List.map_id] at this
      rw [e] at hr
      obtain ⟨dv, hdv, rfl⟩ := List.mem_map.1 hr
      exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)) (hdd dv hdv))

/-- The record premise 12 adds to `C'`, at `mdvModuleV mts dvs`. -/
theorem evalExp_prem12RecV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) :
    EvalExp (simEnv B) (ρV mts dvs) (match modPrem12 with
      | .ifPr (.cmpE _ _ _ (.compE _ e)) => e | _ => .listE [])
      (ctxV mts dvs) :=
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

/-- **Premise 12, `C = C' ⊕ {…}`, holds at `mdvModuleV mts dvs`.** -/
theorem dprem12_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI)
    (els : Prop) : DPremB (simEnv B) O els (ρV mts dvs) modPrem12 :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, evalExp_compE_iff.2 ⟨_, _,
    Sim.evalExp_var rfl, evalExp_prem12RecV mts dvs, rfl⟩,
    Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩)

/-- **Premise 14, `x* = $funcidx_nonfuncs(…)`, holds at `mdvModuleV mts dvs`.** -/
theorem dprem14_V (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) (O : ElseI)
    (els : Prop) : DPremB (simEnv B) O els (ρV mts dvs) modPrem14 :=
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

end Silmaril.Wasm.SpecTec.Institution.Instr30V
