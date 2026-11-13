module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Thms
public import Silmaril.Wasm.SpecTec.Institution.Instr30Y.Defs

/-!
# Instruction typing of the wasm-3.0 script, the variable instructions

`Instr30X` fired `Instr_ok/local.get` and `local.set` in the context `{LOCALS ls}`. This file
widens the context to `{LOCALS ls, GLOBALS gs}` (`ctxLG`, the image of Core's
`{locals := L, globals := G}`) and fires all five variable rules there:

* `Instr_ok/local.get`, `local.set`, `local.tee` (rules 52–54), with the premise
  `C.LOCALS[x] = %%(init, t)`;
* `Instr_ok/global.get` and `global.set` (rules 55, 56), with the premise
  `C.GLOBALS[x] = %%(mut?, t)` (`MUT` for `global.set`).

`variable_preserves`: in a bounded context `{locals := L, globals := G}`, every Core typing of a
variable instruction (`VariableInstrOk`, all five constructors) is an `Instr_ok` fact of every
`simEnv B`, under every reading of `otherwise`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Y

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV idxV mutV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil evalExp_resNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (localV LocalBnd typedV_localV itLXE
  evalExp_eqTrue initV typedV_initV getElem?_localV)

variable {B : Builtins}

/-! ## Contexts with locals and globals -/

/-- Without globals it is `Instr30X.ctxL`. -/
theorem ctxLG_nil (ls : List Value) : ctxLG ls [] = Instr30X.ctxL ls := rfl

set_option maxRecDepth 100000 in
/-- `globaltype`'s definition. -/
theorem findTyp_globaltype : (simEnv B).findTyp? "globaltype" = some ([], [.instD [] [] (.variantT
    [.mk "%%" (.tupT [.mk "mut?" (.iterT (.varT "mut" []) .opt), .mk "valtype" (.varT "valtype" [])])
      [] []])]) :=
  rfl

/-- A bounded global type is a `globaltype`. -/
theorem typedV_globalV {gt : CGlobalType} (hb : GlobalBnd gt) :
    TypedV (simEnv B) (.varT "globaltype" []) (globalV gt) :=
  Typing.typedV_closedCase findTyp_globaltype rfl
    (Round5.Pos.hasTyp_tup2 (ConfigOk.typedV_mut gt.mutability) (Instr30.typedV_val hb))

/-- **`{LOCALS ls, GLOBALS gs}` is a typed context** when its entries are. -/
theorem ctxT_ctxLG {ls gs : List Value}
    (hl : ∀ u ∈ ls, TypedV (simEnv B) (.varT "localtype" []) u)
    (hg : ∀ u ∈ gs, TypedV (simEnv B) (.varT "globaltype" []) u) : CtxT B (ctxLG ls gs) :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  Round5.Pos.typedV_struct Round6.Reading.findTyp_context <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hg) <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hl) <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_one h0

/-- Its image. -/
def ctxLGV (L : List LocalType) (G : List CGlobalType) : Value := ctxLG (L.map localV) (G.map globalV)

/-- **The image of a bounded `{locals := L, globals := G}` is a typed context.** -/
theorem ctxT_lg {L : List LocalType} {G : List CGlobalType} (hb : CtxBnd L G) :
    CtxT B (ctxLGV L G) :=
  ctxT_ctxLG
    (fun u hu => by
      obtain ⟨lt, hlt, rfl⟩ := List.mem_map.1 hu
      exact typedV_localV (hb.1 lt hlt))
    (fun u hu => by
      obtain ⟨gt, hgt, rfl⟩ := List.mem_map.1 hu
      exact typedV_globalV (hb.2 gt hgt))

/-! ## The rules -/

/-- `C.LOCALS[x.0]`. -/
def fieldAtE (fld : String) : Exp :=
  .idxE (.dotE (.varE "C") fld) (.projE (.uncaseE (.varE "x") "%") (0 : Int))

/-- `mut?` as the rule writes it, `mut?` iterated over its own domain. -/
def mutIterE : Exp := .iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")])

set_option maxRecDepth 100000 in
/-- `Instr_ok/local.get`. -/
theorem ruleAt_localGet : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 52
    (.ruleD "local.get" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "LOCAL.GET" (.varE "x"), itLXE [] [] [.varE "t"]])
      [.ifPr (.cmpE .eqOp .boolT (fieldAtE "LOCALS")
        (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/local.set`. -/
theorem ruleAt_localSet : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 53
    (.ruleD "local.set" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" []),
      .expP "init" (.varT "init" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "LOCAL.SET" (.varE "x"), itLXE [.varE "t"] [.varE "x"] []])
      [.ifPr (.cmpE .eqOp .boolT (fieldAtE "LOCALS")
        (.caseE "%%" (.tupE [.varE "init", .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/local.tee`. -/
theorem ruleAt_localTee : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 54
    (.ruleD "local.tee" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" []),
      .expP "init" (.varT "init" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "LOCAL.TEE" (.varE "x"), itLXE [.varE "t"] [.varE "x"] [.varE "t"]])
      [.ifPr (.cmpE .eqOp .boolT (fieldAtE "LOCALS")
        (.caseE "%%" (.tupE [.varE "init", .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/global.get`. -/
theorem ruleAt_globalGet : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 55
    (.ruleD "global.get" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" []),
      .expP "mut?" (.iterT (.varT "mut" []) .opt)] "%|-%:%"
      (.tupE [.varE "C", .caseE "GLOBAL.GET" (.varE "x"), itLXE [] [] [.varE "t"]])
      [.ifPr (.cmpE .eqOp .boolT (fieldAtE "GLOBALS") (.caseE "%%" (.tupE [mutIterE, .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/global.set`. -/
theorem ruleAt_globalSet : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 56
    (.ruleD "global.set" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "GLOBAL.SET" (.varE "x"), itLXE [.varE "t"] [] []])
      [.ifPr (.cmpE .eqOp .boolT (fieldAtE "GLOBALS")
        (.caseE "%%" (.tupE [.optE (some (.caseE "MUT" (.tupE []))), .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Firing them -/

/-- `C.fld[x.0]` reads the entry at `x` of a field of `{LOCALS ls, GLOBALS gs}`. -/
theorem evalExp_fieldAt {env : Env} {ρ : VarEnv} {ls gs : List Value} {fld : String}
    {es : List Value} (hf : fld = "LOCALS" ∧ es = ls ∨ fld = "GLOBALS" ∧ es = gs) {n : Nat}
    {u : Value} (hC : ρ.findVal? "C" = some (ctxLG ls gs)) (hx : ρ.findVal? "x" = some (idxV n))
    (hu : es[n]? = some u) : EvalExp env ρ (fieldAtE fld) u := by
  refine evalExp_idxE_iff.2 ⟨.list es, n, evalExp_dotE_iff.2 ⟨_, Sim.evalExp_var hC, ?_⟩,
    evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (Sim.evalExp_var hx), le_refl _, rfl⟩,
    by simpa [Value.idx?] using hu⟩
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- A singleton list expression of a variable. -/
theorem evalExp_one {env : Env} {ρ : VarEnv} {y : IL.Id} {v : Value} (h : ρ.findVal? y = some v) :
    EvalExp env ρ (.caseE "%" (.tupE [.listE [.varE y]])) (.case "%" (.tuple [.list [v]])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_list1 (Sim.evalExp_var h))
    evalExps_nil, rfl⟩)

/-- `mut?` evaluates to itself. -/
theorem evalExp_mutIter {env : Env} {ρ : VarEnv} (m : Mutability)
    (h : ρ.findVal? "mut?" = some (mutV m)) : EvalExp env ρ mutIterE (mutV m) := by
  cases m
  · exact IntNumeric.evalExp_iterOpt h (fun _ e => nomatch e) fun _ => rfl
  · exact IntNumeric.evalExp_iterOpt h
      (fun w e => by
        obtain rfl := Option.some.inj e
        exact ⟨_, rfl, Sim.evalExp_var (Instr30.findVal_bind1 (by decide) _)⟩) fun e => nomatch e

/-- **`Instr_ok/local.get`** in `{LOCALS ls, GLOBALS gs}`, at a set local. -/
theorem dd_localGet (O : ElseI) {ls gs : List Value} (hc : CtxT B (ctxLG ls gs)) (x : LocalIdx)
    {t : CValType} (hb : Round4.tyBnd t = true) (hl : ls[x.toNat]? = some (localV ⟨.set, t⟩)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxLG ls gs, instrToV (.localGet x), itV [] [] [tyV t]]) :=
  dderivesB_of_ruleAt ruleAt_localGet (self_mem_conclAlts _)
    [("C", ctxLG ls gs), ("x", idxV x.toNat), ("t", tyV t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3 evalExp_resNil evalExp_nil (evalExp_one rfl))))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_fieldAt (.inl ⟨rfl, rfl⟩) rfl rfl hl)
      (evalExp_case (evalExp_tup2 (Round6.AgreeSub.evalExp_atomE "SET") (Sim.evalExp_var rfl))))))

/-- **`Instr_ok/local.set`** in `{LOCALS ls, GLOBALS gs}`, at any local. -/
theorem dd_localSet (O : ElseI) {ls gs : List Value} (hc : CtxT B (ctxLG ls gs)) (x : LocalIdx)
    {i : Init} {t : CValType} (hb : Round4.tyBnd t = true)
    (hl : ls[x.toNat]? = some (localV ⟨i, t⟩)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxLG ls gs, instrToV (.localSet x), itV [tyV t] [idxV x.toNat] []]) :=
  dderivesB_of_ruleAt ruleAt_localSet (self_mem_conclAlts _)
    [("C", ctxLG ls gs), ("x", idxV x.toNat), ("t", tyV t), ("init", initV i)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_initV i _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3 (evalExp_one rfl) (evalExp_list1 (Sim.evalExp_var rfl))
        evalExp_resNil)))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_fieldAt (.inl ⟨rfl, rfl⟩) rfl rfl hl)
      (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl))))))

/-- **`Instr_ok/local.tee`** in `{LOCALS ls, GLOBALS gs}`, at any local. -/
theorem dd_localTee (O : ElseI) {ls gs : List Value} (hc : CtxT B (ctxLG ls gs)) (x : LocalIdx)
    {i : Init} {t : CValType} (hb : Round4.tyBnd t = true)
    (hl : ls[x.toNat]? = some (localV ⟨i, t⟩)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxLG ls gs, instrToV (.localTee x), itV [tyV t] [idxV x.toNat] [tyV t]]) :=
  dderivesB_of_ruleAt ruleAt_localTee (self_mem_conclAlts _)
    [("C", ctxLG ls gs), ("x", idxV x.toNat), ("t", tyV t), ("init", initV i)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_initV i _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3 (evalExp_one rfl) (evalExp_list1 (Sim.evalExp_var rfl))
        (evalExp_one rfl))))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_fieldAt (.inl ⟨rfl, rfl⟩) rfl rfl hl)
      (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl))))))

/-- **`Instr_ok/global.get`** in `{LOCALS ls, GLOBALS gs}`, at any global. -/
theorem dd_globalGet (O : ElseI) {ls gs : List Value} (hc : CtxT B (ctxLG ls gs)) (x : GlobalIdx)
    {gt : CGlobalType} (hb : GlobalBnd gt) (hg : gs[x.toNat]? = some (globalV gt)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxLG ls gs, instrToV (.globalGet x), itV [] [] [tyV gt.type]]) :=
  dderivesB_of_ruleAt ruleAt_globalGet (self_mem_conclAlts _)
    [("C", ctxLG ls gs), ("x", idxV x.toNat), ("t", tyV gt.type), ("mut?", mutV gt.mutability)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (ConfigOk.typedV_mut gt.mutability _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3 evalExp_resNil evalExp_nil (evalExp_one rfl))))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_fieldAt (.inr ⟨rfl, rfl⟩) rfl rfl hg)
      (evalExp_case (evalExp_tup2 (evalExp_mutIter gt.mutability rfl) (Sim.evalExp_var rfl))))))

/-- **`Instr_ok/global.set`** in `{LOCALS ls, GLOBALS gs}`, at a mutable global. -/
theorem dd_globalSet (O : ElseI) {ls gs : List Value} (hc : CtxT B (ctxLG ls gs)) (x : GlobalIdx)
    {t : CValType} (hb : Round4.tyBnd t = true) (hg : gs[x.toNat]? = some (globalV ⟨.var, t⟩)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxLG ls gs, instrToV (.globalSet x), itV [tyV t] [] []]) :=
  dderivesB_of_ruleAt ruleAt_globalSet (self_mem_conclAlts _)
    [("C", ctxLG ls gs), ("x", idxV x.toNat), ("t", tyV t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3 (evalExp_one rfl) evalExp_nil evalExp_resNil)))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_fieldAt (.inr ⟨rfl, rfl⟩) rfl rfl hg)
      (evalExp_case (evalExp_tup2
        (evalExp_optE_some_iff.2 ⟨_, Round6.AgreeSub.evalExp_atomE "MUT", rfl⟩)
        (Sim.evalExp_var rfl))))))

/-! ## Core's variable typings, preserved -/

/-- The global at `x` of `G`, read through the image. -/
theorem getElem?_globalV {G : List CGlobalType} {n : Nat} {gt : CGlobalType}
    (h : G[n]? = some gt) : (G.map globalV)[n]? = some (globalV gt) := by
  rw [List.getElem?_map, h]
  rfl

/-- **The five variable instructions are preserved**: in a bounded context
`{locals := L, globals := G}`, a Core typing of `local.get`, `local.set`, `local.tee`,
`global.get` or `global.set` is an `Instr_ok` fact of `simEnv B` in its image. -/
theorem variable_preserves (O : ElseI) {L : List LocalType} {G : List CGlobalType}
    (hb : CtxBnd L G) {i : Instr} {it : InstrType} (h : VariableInstrOk (ctxLoc L G) i it) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, instrToV i, Silmaril.SpecTec.Equiv.Validation.instrtypeV it]) := by
  have hc : CtxT B (ctxLGV L G) := ctxT_lg hb
  cases h with
  | @localGet x t hl =>
    exact dd_localGet O hc x (hb.1 _ (List.mem_of_getElem? hl)) (getElem?_localV hl)
  | @localSet x i t hl =>
    exact dd_localSet O hc x (hb.1 _ (List.mem_of_getElem? hl)) (getElem?_localV hl)
  | @localTee x i t hl =>
    exact dd_localTee O hc x (hb.1 _ (List.mem_of_getElem? hl)) (getElem?_localV hl)
  | @globalGet x m t hg =>
    exact dd_globalGet O hc x (gt := ⟨m, t⟩) (hb.2 _ (List.mem_of_getElem? hg))
      (getElem?_globalV hg)
  | @globalSet x t hg =>
    exact dd_globalSet O hc x (hb.2 _ (List.mem_of_getElem? hg)) (getElem?_globalV hg)

end Silmaril.Wasm.SpecTec.Institution.Instr30Y
