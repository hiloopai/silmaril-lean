module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30XModFns
public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Defs

/-!
# Instruction typing of the wasm-3.0 script, extended: `$funcidx_nonfuncs` at empty lists

`Task.funcidxEmpty`, proved clause by clause, in every evaluator `simEnv B`:

* `tc_freeModule`: `$free_module(MODULE …)` at the empty module is `free0` (every field empty).
  Its argument pattern (twelve components) is matched by composing one lemma per pattern shape
  (`matchExp_pctList`, `matchExp_optVar`), not by unfolding the matcher, which the kernel checks
  too slowly; the body, ten compositions of `$free_list([])` and `$free_opt(eps)`, is evaluated
  by `simp`.
* `tc_funcidxModule`: `$funcidx_module(MODULE …) = $free_module(MODULE …).FUNCS = []`;
* `tc_funcidxNonfuncs`, `funcidxEmpty`: `$funcidx_nonfuncs(%%%%%([], [], [], [], [])) = []`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (MatchExps matchExps_cons_iff)
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d75 Original.d74 Original.d310 Original.d311
  Original.d384)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (emptyModuleV pctNil)

variable {B : Builtins}

/-! ## Matching, one pattern shape at a time -/

/-- A tuple pattern matches a tuple, component by component. -/
theorem matchExp_tupE' {env : Env} {ρ ρ' : VarEnv} {es : List Exp} {vs : List Value}
    (h : MatchExps env ρ es vs ρ') : MatchExp env ρ (.tupE es) (.tuple vs) ρ' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [matchExp, Value.asTuple?, Bind.bind, Except.bind, Res.ofOption, h]⟩

/-- No patterns match no values. -/
theorem matchExps_nil' {env : Env} {ρ : VarEnv} : MatchExps env ρ [] [] ρ :=
  ⟨1, by simp [matchExps]⟩

/-- Patterns match values head first. -/
theorem matchExps_cons' {env : Env} {ρ σ ρ' : VarEnv} {e : Exp} {es : List Exp} {v : Value}
    {vs : List Value} (h₁ : MatchExp env ρ e v σ) (h₂ : MatchExps env σ es vs ρ') :
    MatchExps env ρ (e :: es) (v :: vs) ρ' :=
  matchExps_cons_iff.2 ⟨_, _, _, rfl, h₁, h₂⟩

/-- `x*` matches `[]`, binding `x*`. -/
theorem matchExp_listVar {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hfxs : ρ.findVal? xs = none) :
    MatchExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) (.list [])
      (ρ.bindVal xs (.list [])) :=
  ⟨6, by simp [matchExp, matchIterE, matchIterList, matchRounds, matchExps, iterCols, iterCol,
    domSrc, domVar, Value.asList?, Bind.bind, Except.bind, Res.ofOption, hfxs]⟩

/-- `%(x*)` matches `%([])`, binding `x*`. -/
theorem matchExp_pctList {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hfxs : ρ.findVal? xs = none) :
    MatchExp env ρ (.caseE "%" (.tupE [.iterE (.varE x) (.mk .list [.mk x (.varE xs)])]))
      pctNil (ρ.bindVal xs (.list [])) :=
  matchExp_caseE (matchExp_tupE' (matchExps_cons' (matchExp_listVar hfxs) matchExps_nil'))

/-- `x?` matches `eps`, binding `x?`. -/
theorem matchExp_optVar {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hfxs : ρ.findVal? xs = none) :
    MatchExp env ρ (.iterE (.varE x) (.mk .opt [.mk x (.varE xs)])) (.opt none)
      (ρ.bindVal xs (.opt none)) :=
  ⟨5, by simp [matchExp, matchIterE, matchExps, Value.asOpt?, domSrc, Bind.bind, Except.bind,
    Res.ofOption, hfxs]⟩

/-! ## `$free_module` -/

/-- The empty free-index record. -/
def free0 : Value := .struct [("TYPES", .list []), ("FUNCS", .list []), ("GLOBALS", .list []),
  ("TABLES", .list []), ("MEMS", .list []), ("ELEMS", .list []), ("DATAS", .list []),
  ("LOCALS", .list []), ("LABELS", .list []), ("TAGS", .list [])]

/-- `$free_module`'s quantifiers. -/
def fmQs : List Param :=
  [(Param.expP "type*" (Typ.iterT (Typ.varT "type" []) Iter.list)), (Param.expP "import*" (Typ.iterT
    (Typ.varT "import" []) Iter.list)), (Param.expP "tag*" (Typ.iterT (Typ.varT "tag" []) Iter.list)),
    (Param.expP "global*" (Typ.iterT (Typ.varT "global" []) Iter.list)), (Param.expP "mem*" (Typ.iterT
    (Typ.varT "mem" []) Iter.list)), (Param.expP "table*" (Typ.iterT (Typ.varT "table" []) Iter.list)),
    (Param.expP "func*" (Typ.iterT (Typ.varT "func" []) Iter.list)), (Param.expP "data*" (Typ.iterT
    (Typ.varT "data" []) Iter.list)), (Param.expP "elem*" (Typ.iterT (Typ.varT "elem" []) Iter.list)),
    (Param.expP "start?" (Typ.iterT (Typ.varT "start" []) Iter.opt)), (Param.expP "export*" (Typ.iterT
    (Typ.varT "export" []) Iter.list))]

/-- `$free_module`'s argument pattern. -/
def fmPats : List Arg :=
  [(Arg.expA (Exp.caseE "MODULE" (Exp.tupE [(Exp.caseE "%" (Exp.tupE
    [(Exp.iterE (Exp.varE "type") (IterExp.mk Iter.list [(Dom.mk "type" (Exp.varE "type*"))]))])),
    (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "import") (IterExp.mk Iter.list [(Dom.mk "import"
    (Exp.varE "import*"))]))])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "tag") (IterExp.mk Iter.list
    [(Dom.mk "tag" (Exp.varE "tag*"))]))])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "global")
    (IterExp.mk Iter.list [(Dom.mk "global" (Exp.varE "global*"))]))])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE
    (Exp.varE "mem") (IterExp.mk Iter.list [(Dom.mk "mem" (Exp.varE "mem*"))]))])), (Exp.caseE "%"
    (Exp.tupE [(Exp.iterE (Exp.varE "table") (IterExp.mk Iter.list [(Dom.mk "table" (Exp.varE "table*"))]))])),
    (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "func") (IterExp.mk Iter.list [(Dom.mk "func" (Exp.varE "func*"))]))])),
    (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "data") (IterExp.mk Iter.list [(Dom.mk "data" (Exp.varE "data*"))]))])),
    (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "elem") (IterExp.mk Iter.list [(Dom.mk "elem" (Exp.varE "elem*"))]))])),
    (Exp.iterE (Exp.varE "start") (IterExp.mk Iter.opt [(Dom.mk "start" (Exp.varE "start?"))])), (Exp.caseE "%"
    (Exp.tupE [(Exp.iterE (Exp.varE "export") (IterExp.mk Iter.list [(Dom.mk "export" (Exp.varE "export*"))]))]))])))]

/-- `$free_module`'s body. -/
def fmBody : Exp :=
  (Exp.compE (Exp.compE (Exp.compE (Exp.compE (Exp.compE (Exp.compE (Exp.compE (Exp.compE (Exp.compE
    (Exp.compE (Exp.callE "free_list" [(Arg.expA (Exp.iterE (Exp.callE "free_type" [(Arg.expA (Exp.varE "type"))])
    (IterExp.mk Iter.list [(Dom.mk "type" (Exp.varE "type*"))])))]) (Exp.callE "free_list" [(Arg.expA
    (Exp.iterE (Exp.callE "free_tag" [(Arg.expA (Exp.varE "tag"))]) (IterExp.mk Iter.list [(Dom.mk "tag"
    (Exp.varE "tag*"))])))])) (Exp.callE "free_list" [(Arg.expA (Exp.iterE (Exp.callE "free_global"
    [(Arg.expA (Exp.varE "global"))]) (IterExp.mk Iter.list [(Dom.mk "global" (Exp.varE "global*"))])))]))
    (Exp.callE "free_list" [(Arg.expA (Exp.iterE (Exp.callE "free_mem" [(Arg.expA (Exp.varE "mem"))])
    (IterExp.mk Iter.list [(Dom.mk "mem" (Exp.varE "mem*"))])))])) (Exp.callE "free_list" [(Arg.expA
    (Exp.iterE (Exp.callE "free_table" [(Arg.expA (Exp.varE "table"))]) (IterExp.mk Iter.list [(Dom.mk "table"
    (Exp.varE "table*"))])))])) (Exp.callE "free_list" [(Arg.expA (Exp.iterE (Exp.callE "free_func"
    [(Arg.expA (Exp.varE "func"))]) (IterExp.mk Iter.list [(Dom.mk "func" (Exp.varE "func*"))])))]))
    (Exp.callE "free_list" [(Arg.expA (Exp.iterE (Exp.callE "free_data" [(Arg.expA (Exp.varE "data"))])
    (IterExp.mk Iter.list [(Dom.mk "data" (Exp.varE "data*"))])))])) (Exp.callE "free_list" [(Arg.expA
    (Exp.iterE (Exp.callE "free_elem" [(Arg.expA (Exp.varE "elem"))]) (IterExp.mk Iter.list [(Dom.mk "elem"
    (Exp.varE "elem*"))])))])) (Exp.callE "free_opt" [(Arg.expA (Exp.iterE (Exp.callE "free_start"
    [(Arg.expA (Exp.varE "start"))]) (IterExp.mk Iter.opt [(Dom.mk "start" (Exp.varE "start?"))])))]))
    (Exp.callE "free_list" [(Arg.expA (Exp.iterE (Exp.callE "free_import" [(Arg.expA (Exp.varE "import"))])
    (IterExp.mk Iter.list [(Dom.mk "import" (Exp.varE "import*"))])))])) (Exp.callE "free_list" [(Arg.expA
    (Exp.iterE (Exp.callE "free_export" [(Arg.expA (Exp.varE "export"))]) (IterExp.mk Iter.list [(Dom.mk "export"
    (Exp.varE "export*"))])))]))

/-- `$free_module`'s one clause. -/
theorem fm_clauses : defClauses Original.d310 = [.defD fmQs fmPats fmBody []] := rfl

/-- The scope `$free_module`'s pattern binds at the empty module. -/
def fmρ : VarEnv :=
  (((((((((((VarEnv.empty.bindVal "type*" (.list [])).bindVal "import*" (.list [])).bindVal
    "tag*" (.list [])).bindVal "global*" (.list [])).bindVal "mem*" (.list [])).bindVal
    "table*" (.list [])).bindVal "func*" (.list [])).bindVal "data*" (.list [])).bindVal
    "elem*" (.list [])).bindVal "start?" (.opt none)).bindVal "export*" (.list []))

set_option maxRecDepth 100000 in
/-- **`$free_module`'s pattern matches the empty module.** -/
theorem fm_match : MatchArgs (simEnv B) VarEnv.empty fmPats [.val emptyModuleV] fmρ :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
    (matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_optVar (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) matchExps_nil')))) matchArgs_nil

/-- **`$free_module`'s body is `free0`** in that scope. -/
theorem fm_body : EvalExp (simEnv B) fmρ fmBody free0 := ⟨40, by
  simp [fmBody, fmρ, free0, evalExp, callDef, evalArgs, evalArg, evalExps, tryClauses, matchArg,
    matchExp, premsHold, VarEnv.findDef?, VarEnv.empty, Res.elimUndef, Bind.bind, Except.bind,
    Res.ofOption, Pure.pure, Except.pure, matchArgs.eq_def, argSubOk, matchExps, defClauses, defSig,
    Original.d75, Original.d74, fd_flist, fd_fopt, evalIterE, evalDoms, domSrc, domVar,
    VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, Map.find?, evalIterList, evalRounds,
    Value.asList?, iterRows, Functor.map, Except.map, evalExpFields, Value.comp?, Value.compFields?,
    Value.asOpt?, VarEnv.bindVal]⟩

/-- **`$free_module(MODULE …)` at the empty module is `free0`.** -/
theorem tc_freeModule : TryClauses (simEnv B) (defClauses Original.d310) [.val emptyModuleV] free0 :=
  fm_clauses ▸ tryClauses_hit fm_match (Equiv.Validation.premsHold_nil_iff.2 rfl) fm_body

/-! ## `$funcidx_module` and `$funcidx_nonfuncs` -/

/-- `$funcidx_module`'s one clause. -/
theorem fmod_clauses : defClauses Original.d311 = [.defD [.expP "module" (.varT "module" [])]
    [.expA (.varE "module")] (.dotE (.callE "free_module" [.expA (.varE "module")]) "FUNCS") []] :=
  rfl

/-- **`$funcidx_module(MODULE …)` at the empty module is `[]`.** -/
theorem tc_funcidxModule :
    TryClauses (simEnv B) (defClauses Original.d311) [.val emptyModuleV] (.list []) :=
  fmod_clauses ▸ tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_dotE_iff.2 ⟨free0, evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
      Equiv.evalArgs_cons (Sim.evalExp_var rfl) Equiv.evalArgs_nil, fd_fmod,
      .inl tc_freeModule⟩), rfl⟩)

/-- `$funcidx_nonfuncs`'s quantifiers. -/
def fnfQs : List Param :=
  [(Param.expP "global*" (Typ.iterT (Typ.varT "global" []) Iter.list)),
    (Param.expP "mem*" (Typ.iterT (Typ.varT "mem" []) Iter.list)), (Param.expP "table*" (Typ.iterT
    (Typ.varT "table" []) Iter.list)), (Param.expP "elem*" (Typ.iterT (Typ.varT "elem" []) Iter.list)),
    (Param.expP "export*" (Typ.iterT (Typ.varT "export" []) Iter.list))]

/-- `$funcidx_nonfuncs`'s argument pattern. -/
def fnfPats : List Arg :=
  [(Arg.expA (Exp.caseE "%%%%%"
    (Exp.tupE [(Exp.iterE (Exp.varE "global") (IterExp.mk Iter.list [(Dom.mk "global" (Exp.varE "global*"))])),
    (Exp.iterE (Exp.varE "mem") (IterExp.mk Iter.list [(Dom.mk "mem" (Exp.varE "mem*"))])), (Exp.iterE
    (Exp.varE "table") (IterExp.mk Iter.list [(Dom.mk "table" (Exp.varE "table*"))])), (Exp.iterE (Exp.varE "elem")
    (IterExp.mk Iter.list [(Dom.mk "elem" (Exp.varE "elem*"))])), (Exp.iterE (Exp.varE "export") (IterExp.mk Iter.list
    [(Dom.mk "export" (Exp.varE "export*"))]))])))]

/-- `$funcidx_nonfuncs`'s body. -/
def fnfBody : Exp :=
  (Exp.callE "funcidx_module" [(Arg.expA (Exp.caseE "MODULE"
    (Exp.tupE [(Exp.caseE "%" (Exp.tupE [(Exp.listE [])])), (Exp.caseE "%" (Exp.tupE [(Exp.listE [])])),
    (Exp.caseE "%" (Exp.tupE [(Exp.listE [])])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "global")
    (IterExp.mk Iter.list [(Dom.mk "global" (Exp.varE "global*"))]))])), (Exp.caseE "%" (Exp.tupE [(Exp.iterE
    (Exp.varE "mem") (IterExp.mk Iter.list [(Dom.mk "mem" (Exp.varE "mem*"))]))])), (Exp.caseE "%"
    (Exp.tupE [(Exp.iterE (Exp.varE "table") (IterExp.mk Iter.list [(Dom.mk "table" (Exp.varE "table*"))]))])),
    (Exp.caseE "%" (Exp.tupE [(Exp.listE [])])), (Exp.caseE "%" (Exp.tupE [(Exp.listE [])])), (Exp.caseE "%"
    (Exp.tupE [(Exp.iterE (Exp.varE "elem") (IterExp.mk Iter.list [(Dom.mk "elem" (Exp.varE "elem*"))]))])),
    (Exp.optE none), (Exp.caseE "%" (Exp.tupE [(Exp.iterE (Exp.varE "export") (IterExp.mk Iter.list
    [(Dom.mk "export" (Exp.varE "export*"))]))]))])))])

/-- `$funcidx_nonfuncs`'s one clause. -/
theorem fnf_clauses : defClauses Original.d384 = [.defD fnfQs fnfPats fnfBody []] := rfl

/-- The scope `$funcidx_nonfuncs`'s pattern binds at five empty lists. -/
def fnfρ : VarEnv :=
  ((((VarEnv.empty.bindVal "global*" (.list [])).bindVal "mem*" (.list [])).bindVal
    "table*" (.list [])).bindVal "elem*" (.list [])).bindVal "export*" (.list [])

/-- **`$funcidx_nonfuncs(%%%%%([], [], [], [], [])) = []`.** -/
theorem tc_funcidxNonfuncs : TryClauses (simEnv B) (defClauses Original.d384)
    [.val (.case "%%%%%" (.tuple [.list [], .list [], .list [], .list [], .list []]))] (.list []) :=
  fnf_clauses ▸ tryClauses_hit (ρ₀ := fnfρ)
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
      (matchExps_cons' (matchExp_listVar (by rfl)) <| matchExps_cons' (matchExp_listVar (by rfl)) <|
      matchExps_cons' (matchExp_listVar (by rfl)) <| matchExps_cons' (matchExp_listVar (by rfl)) <|
      matchExps_cons' (matchExp_listVar (by rfl)) matchExps_nil')))) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _, ⟨20, by
      simp [emptyModuleV, pctNil, fnfρ, evalArgs, evalArg, evalExp, evalExps, evalIterE, evalDoms,
        domSrc, domVar, VarEnv.findVal?, VarEnv.bindVal, Map.bind, Map.find?, evalIterList,
        evalRounds, Value.asList?, iterRows, Functor.map, Except.map, Bind.bind, Except.bind,
        Res.ofOption, Pure.pure, Except.pure]⟩, fd_fm, .inl tc_funcidxModule⟩))

/-- **`Task.funcidxEmpty` holds.** -/
theorem funcidxEmpty : Task.funcidxEmpty := fun _ => ⟨_, _, _, fd_fnf, .inl tc_funcidxNonfuncs⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30X
