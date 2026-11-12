module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdBlock

/-!
# `call_addr` forward (`Step_read` 5)

2.0's

  `z; val^k (CALL_ADDR a) ~> (FRAME_ n {f} (LABEL_ n {eps} instr*))`

under `$funcinst(z)[a] = {TYPE (t_1^k -> t_2^n), MODULE mm, CODE func}`,
`func = FUNC x (LOCAL t)* instr*` and `f = {LOCALS val^k ($default_(t))*, MODULE mm}`: V2's
`ReadStep.callAddr` of a Wasm function. Forward, every quantifier is bound to the image of the
corresponding part of V2's step: `mm`, `func` and `instr*` are typed because the store is
(`typedV_funcInst_parts20`, through the record `funcinst` and the variant `func`), `f` because
its locals are values and its module is `mm`.

* `evalExp_default20`: `$default_(t)` is the image of V2's `defaultVal t`, at every 2.0 value
  type;
* `fires_callAddr20`: the rule fires at the image of V2's step, from a typed image;
* `CallAddrFwd20`, `fwdBase20_callAddr` (subject reduction and the forward step), and
  **`Task.wholeStepFwd20C`** (proved): at `storeB`, the nested fragment `FwdStep20BL` plus
  `call_addr` of a Wasm function is matched forward.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 evalExp_call1)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.State (sfPat matchArgs_sf)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `$funcinst` -/

theorem hasClause_funcinst20 : HasClause1 (simEnv20 B) "funcinst" sfPat
    (.dotE (.varE "s") "FUNCS") := ⟨_, _, _, rfl⟩

/-- **`$funcinst(z)[a]`**, at a store function. -/
theorem evalExp_funcinstAt20 {ρ : VarEnv} {s : Store H} {f : Frame} {a : FuncAddr}
    {fi : FuncInst H} (hρ : ρ.findDef? "funcinst" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hf : s.funcInst? a = some fi) :
    EvalExp (simEnv20 B) ρ (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
      (funcInstV hn fi) :=
  evalExp_idxE_iff.2 ⟨_, a, evalExp_call1 hasClause_funcinst20 hρ
    (evalArgs_cons (evalExp_var fz) evalArgs_nil) matchArgs_sf
    (evalExp_dotE_iff.2 ⟨storeV hn s, evalExp_var rfl, rfl⟩), evalExp_var fa,
    by simpa [Value.idx?, List.getElem?_map] using ⟨fi, by simpa [Store.funcInst?] using hf, rfl⟩⟩

/-! ## `$default_` -/

theorem findDef_fzero20 : ∃ ps t, (simEnv20 B).findDef? "fzero" = some (ps, t,
    [.defD [.expP "N" (.varT "N" [])] [.expA (.varE "N")]
      (.caseE "POS" (.caseE "SUBNORM" (.tupE [.numE (.natN 0)]))) []]) := ⟨_, _, rfl⟩

/-- `$fzero(N) = POS (SUBNORM 0)`. -/
theorem evalExp_fzero20 {ρ : VarEnv} (N : Nat) (hρ : ρ.findDef? "fzero" = none) :
    EvalExp (simEnv20 B) ρ (.callE "fzero" [.expA (.numE (.natN N))])
      (.case "POS" (.case "SUBNORM" (.tuple [.num (.natN 0)]))) := by
  obtain ⟨ps, t, hd⟩ := findDef_fzero20 (B := B)
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd
    (evalArgs_cons (evalExp_numE_iff.2 rfl) evalArgs_nil) ?_)
  exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    premsHold_nil (evalExp_case (evalExp_case (evalExp_tupE_iff.2
      ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)))

/-- The seven clauses of `$default_` (`Original`, `5-runtime-aux:7`). -/
abbrev defaultClauses20 : List Clause :=
  [.defD [] [.expA (.caseE "I32" (.tupE []))]
      (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.numE (.natN 0)])])) [],
    .defD [] [.expA (.caseE "I64" (.tupE []))]
      (.caseE "CONST" (.tupE [.caseE "I64" (.tupE []), .caseE "%" (.tupE [.numE (.natN 0)])])) [],
    .defD [] [.expA (.caseE "F32" (.tupE []))]
      (.caseE "CONST" (.tupE [.caseE "F32" (.tupE []), .callE "fzero" [.expA (.numE (.natN 32))]])) [],
    .defD [] [.expA (.caseE "F64" (.tupE []))]
      (.caseE "CONST" (.tupE [.caseE "F64" (.tupE []), .callE "fzero" [.expA (.numE (.natN 64))]])) [],
    .defD [] [.expA (.caseE "V128" (.tupE []))]
      (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .caseE "%" (.tupE [.numE (.natN 0)])])) [],
    .defD [] [.expA (.caseE "FUNCREF" (.tupE []))] (.caseE "REF.NULL" (.caseE "FUNCREF" (.tupE []))) [],
    .defD [] [.expA (.caseE "EXTERNREF" (.tupE []))]
      (.caseE "REF.NULL" (.caseE "EXTERNREF" (.tupE []))) []]

theorem findDef_default20 :
    ∃ ps t, (simEnv20 B).findDef? "default_" = some (ps, t, defaultClauses20) := ⟨_, _, rfl⟩

/-- The nullary case `op`, evaluated. -/
theorem evalExp_nil0_20 {env : Env} {ρ : VarEnv} (op : MixopS) :
    EvalExp env ρ (.caseE op (.tupE [])) (.case op (.tuple [])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- `%0`, evaluated. -/
theorem evalExp_pct0_20 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (pctV 0) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)

/-- The image of a zero float's default is `CONST` of `$fzero`'s value. -/
theorem valV_default_float20 (t : FloatType) :
    valV (defaultVal (.num (.float t))) = .case "CONST" (.tuple [numTypeV (.float t),
      .case "POS" (.case "SUBNORM" (.tuple [.num (.natN 0)]))]) := by
  cases t <;> rfl

/-- **`$default_(t)`** is the image of V2's `defaultVal t`, at every 2.0 value type. -/
theorem evalExp_default20 (t : V2.ValType) {ρ : VarEnv} {e : Exp}
    (hρ : ρ.findDef? "default_" = none) (he : EvalExp (simEnv20 B) ρ e (valTypeV t)) :
    EvalExp (simEnv20 B) ρ (.callE "default_" [.expA e]) (valV (defaultVal t)) := by
  obtain ⟨ps, ty, hd⟩ := findDef_default20 (B := B)
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd (evalArgs_cons he evalArgs_nil) ?_)
  rcases t with ((_ | _) | (_ | _)) | ⟨⟩ | (_ | _) <;>
  · repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) ?_)
    refine tryClauses_hit (ρ₀ := VarEnv.empty)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
      premsHold_nil ?_
    first
      | exact evalExp_case (evalExp_tup2 (evalExp_nil0_20 _) evalExp_pct0_20)
      | (rw [valV_default_float20]
         exact evalExp_case (evalExp_tup2 (evalExp_nil0_20 _) (evalExp_fzero20 _ rfl)))
      | exact evalExp_case (evalExp_nil0_20 _)


/-- A value type, read back from its image. -/
def vtOf20 : Value → V2.ValType
  | .case "I64" _ => .num (.int .i64)
  | .case "F32" _ => .num (.float .f32)
  | .case "F64" _ => .num (.float .f64)
  | .case "V128" _ => .vec .v128
  | .case "FUNCREF" _ => .ref .funcref
  | .case "EXTERNREF" _ => .ref .externref
  | _ => .num (.int .i32)

theorem vtOf20_valTypeV (t : V2.ValType) : vtOf20 (valTypeV t) = t := by
  rcases t with ((_ | _) | (_ | _)) | ⟨⟩ | (_ | _) <;> rfl

/-! ## The parts of a typed function instance are typed -/

theorem findTyp_funcinst20 : (simEnv20 B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])]) := rfl

theorem findTyp_func20 : (simEnv20 B).findTyp? "func" = some ([], [.instD [] [] (.variantT
    [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]) := rfl

theorem findTyp_expr20 : (simEnv20 B).findTyp? "expr" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]) := rfl

/-- The image of a Wasm function's code. -/
def codeV20 (fn : V2.Func) : Value :=
  .case "FUNC" (.tuple [idxV fn.type, .list ((fn.locals.map valTypeV).map (.case "LOCAL")),
    .list (instrsToV fn.body)])

theorem funcInstV_wasm {fi : FuncInst H} {fn : V2.Func} (hcode : fi.code = .wasm fn) :
    funcInstV hn fi = .struct [("TYPE", funcTypeV fi.type), ("MODULE", moduleInstV fi.module),
      ("CODE", codeV20 fn)] := by
  simp [funcInstV, hcode, codeV20, List.map_map, Function.comp_def]

/-- **A typed function instance has a typed module and a typed code.** -/
theorem typedV_funcInst_parts20 {fi : FuncInst H} {fn : V2.Func} (hcode : fi.code = .wasm fn)
    (h : TypedV (simEnv20 B) (.varT "funcinst" []) (funcInstV hn fi)) :
    TypedV (simEnv20 B) (.varT "moduleinst" []) (moduleInstV fi.module) ∧
      TypedV (simEnv20 B) (.varT "func" []) (codeV20 fn) := by
  rw [funcInstV_wasm hcode] at h
  have h₀ := hasTypFields_of_closed findTyp_funcinst20 h
  have h₁ := (hasTypFields_cons_nil_iff.1 h₀).2
  have h₂ := hasTypFields_cons_nil_iff.1 h₁
  exact ⟨typedV_of_empty20 h₂.1, typedV_of_empty20 (hasTypFields_cons_nil_iff.1 h₂.2).1⟩

/-- **A typed Wasm function has a typed body.** -/
theorem typedV_body_of_func20 {fn : V2.Func} (h : TypedV (simEnv20 B) (.varT "func" []) (codeV20 fn)) :
    TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV fn.body)) := by
  obtain ⟨op, w, he, hc⟩ :=
    hasTypDef_variantT_iff.1 (hasTypDef_of_closed findTyp_func20 (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : op = "FUNC" ∧ w = .tuple [idxV fn.type,
      .list ((fn.locals.map valTypeV).map (.case "LOCAL")), .list (instrsToV fn.body)] := by
    simpa [codeV20] using he.symm
  have ht := Sim.IntNumeric.hasTyp_of_hasTypCase hc rfl
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 ht
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y₁, ys₁, h₁, -, ht₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
  obtain ⟨y₂, ys₂, h₂, -, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₂
  obtain ⟨y₃, ys₃, h₃, hy₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj h₃
  have hE : TypedV (simEnv20 B) (.varT "expr" []) (.list (instrsToV fn.body)) :=
    typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ hy₃
  exact typedV_list_of_empty20 (hasTypDef_aliasT_iff.1
    (hasTypDef_of_closed findTyp_expr20 (hE _ valsOnly_empty)))

/-- A frame from values and a typed module is typed. -/
theorem typedV_frame_of20 {m : ModuleInst} (hm : TypedV (simEnv20 B) (.varT "moduleinst" [])
    (moduleInstV m)) (ls : List Val) : TypedV (simEnv20 B) Pure.frameT (frameV ⟨ls, m⟩) :=
  typedV_struct2 findTyp_frame20 (typedV_vals20 ls _ valsOnly_empty) (hm _ valsOnly_empty)

/-- The function instance at an address of a typed state is typed. -/
theorem typedV_funcInst_of_state20 {s : Store H} {f : Frame} {a : FuncAddr} {fi : FuncInst H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) (hf : s.funcInst? a = some fi) :
    TypedV (simEnv20 B) (.varT "funcinst" []) (funcInstV hn fi) :=
  typedV_of_getElem? (typedV_storeV_iff.1 (typedV_stateV_iff.1 hz).1).funcs
    (by simpa [Store.funcInst?] using hf)


/-! ## The rule -/

/-- `%(t_1^k) -> %(t_2^n)`. -/
abbrev ftKNE20 : Exp := .caseE "%->%" (.tupE [
  .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none) [.mk "t_1" (.varE "t_1*")])]),
  .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])])

/-- `FUNC x (LOCAL t)* instr*`. -/
abbrev funcE20 : Exp := .caseE "FUNC" (.tupE [.varE "x",
  .iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]), instrsE20])

/-- `{LOCALS val^k ($default_(t))*, MODULE mm}`. -/
abbrev frameE20 : Exp := .strE [.mk "LOCALS" (.catE
    (.iterE (.varE "val") (.mk (.listN (.varE "k") none) [.mk "val" (.varE "val*")]))
    (.iterE (.callE "default_" [.expA (.varE "t")]) (.mk .list [.mk "t" (.varE "t*")]))),
  .mk "MODULE" (.varE "mm")]

/-- `Step_read/call_addr`, rule 5 (transcribed). -/
def callAddrRule20 : Rule :=
  .ruleD "call_addr" [.expP "z" (.varT "state" []), .expP "k" (.numT .natT),
      .expP "val*" (.iterT (.varT "val" []) .list), .expP "a" (.varT "addr" []),
      .expP "n" (.varT "n" []), .expP "f" (.varT "frame" []),
      .expP "instr*" (.iterT (.varT "instr" []) .list),
      .expP "t_1*" (.iterT (.varT "valtype" []) .list), .expP "t_2*" (.iterT (.varT "valtype" []) .list),
      .expP "mm" (.varT "moduleinst" []), .expP "func" (.varT "func" []), .expP "x" (.varT "idx" []),
      .expP "t*" (.iterT (.varT "valtype" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .catE valsKE20 (.listE [.caseE "CALL_ADDR" (.varE "a")])]),
      .listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n", .varE "f", .listE [.caseE "LABEL_%{%}%"
        (.tupE [.varE "n", .listE [], instrsAdmE20])]])]])
    [.ifPr (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
        (.strE [.mk "TYPE" ftKNE20, .mk "MODULE" (.varE "mm"), .mk "CODE" (.varE "func")])),
      .ifPr (.cmpE .eqOp .boolT (.varE "func") funcE20),
      .ifPr (.cmpE .eqOp .boolT (.varE "f") frameE20)]

theorem hasRuleAt_callAddr20 : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 5 callAddrRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- A three-field record, evaluated. -/
theorem evalExp_str3_20 {env : Env} {ρ : VarEnv} {a₁ a₂ a₃ : AtomS} {e₁ e₂ e₃ : Exp}
    {v₁ v₂ v₃ : Value} (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂)
    (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.strE [.mk a₁ e₁, .mk a₂ e₂, .mk a₃ e₃]) (.struct [(a₁, v₁), (a₂, v₂), (a₃, v₃)]) := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨n₃, h₃⟩ := h₃
  have g₁ : evalExp (max n₁ (max n₂ n₃)) env ρ e₁ = .ok v₁ := evalExp_ok_of_le (by omega) h₁
  have g₂ : evalExp (max n₁ (max n₂ n₃)) env ρ e₂ = .ok v₂ := evalExp_ok_of_le (by omega) h₂
  have g₃ : evalExp (max n₁ (max n₂ n₃)) env ρ e₃ = .ok v₃ := evalExp_ok_of_le (by omega) h₃
  refine evalExp_strE_iff.2 ⟨_, ⟨max n₁ (max n₂ n₃) + 1, ?_⟩, rfl⟩
  simp [evalExpFields, g₁, g₂, g₃]

/-- The callee's new frame. -/
abbrev calleeFrame20 (fi : FuncInst H) (vs : List Val) (fn : V2.Func) : Frame :=
  Frame.forCall fi.module vs fn.locals

/-- The assignment of `call_addr` at V2's left-hand side. -/
abbrev callAddrSigma20 (hn : H → String) (s : Store H) (f : Frame) (vs : List Val) (a : FuncAddr)
    (fi : FuncInst H) (fn : V2.Func) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("k", .num (.natN (vs.map valV).length)), ("val*", .list (vs.map valV)),
    ("a", .num (.natN a)), ("n", .num (.natN fi.type.results.length)),
    ("f", frameV (calleeFrame20 fi vs fn)), ("instr*", .list (instrsToV fn.body)),
    ("t_1*", .list (fi.type.params.map valTypeV)), ("t_2*", .list (fi.type.results.map valTypeV)),
    ("mm", moduleInstV fi.module), ("func", codeV20 fn), ("x", idxV fn.type),
    ("t*", .list (fn.locals.map valTypeV))]

/-- The third premise: `f` is the callee's frame. -/
theorem evalExp_frameE20 {s : Store H} {f : Frame} {vs : List Val} {a : FuncAddr}
    {fi : FuncInst H} {fn : V2.Func} :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn)) frameE20
      (frameV (calleeFrame20 fi vs fn)) := by
  have e₁ := evalExp_iterN20 (B := B) (x := "val") (xs := "val*") (c := "k")
    (ρ := VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn)) (by decide) rfl rfl
  have e₂ := Sim.evalExp_iterMap (env := simEnv20 B)
    (ρ := VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
    (b := .callE "default_" [.expA (.varE "t")]) (x := "t") (y := "t*")
    (g := fun w => valV (defaultVal (vtOf20 w)))
    rfl fun w hw => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hw
      rw [vtOf20_valTypeV]
      exact evalExp_default20 t rfl (evalExp_var (Sim.findVal_bind1 (by decide)))
  have e := Sim.evalExp_str2 (a₁ := "LOCALS") (a₂ := "MODULE") (Sim.evalExp_cat e₁ e₂)
    (evalExp_var (env := simEnv20 B) (x := "mm")
      (ρ := VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn)) rfl)
  have hv : frameV (calleeFrame20 fi vs fn) = .struct [("LOCALS", .list (vs.map valV ++
      (fn.locals.map valTypeV).map fun w => valV (defaultVal (vtOf20 w)))),
      ("MODULE", moduleInstV fi.module)] := by
    simp [frameV, Frame.forCall, List.map_map, Function.comp_def, vtOf20_valTypeV]
  rw [hv]
  exact e


/-- The second premise: `func` is `FUNC x (LOCAL t)* instr*`. -/
theorem evalExp_funcE20 {s : Store H} {f : Frame} {vs : List Val} {a : FuncAddr}
    {fi : FuncInst H} {fn : V2.Func} :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn)) funcE20
      (codeV20 fn) :=
  evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) (Sim.evalExp_iterMap (g := .case "LOCAL") rfl
    fun _ _ => evalExp_case (evalExp_var (Sim.findVal_bind1 (by decide))))
    (Pure.evalExp_iter (by decide) rfl))

/-- The first premise: `$funcinst(z)[a]` is the record of the callee. -/
theorem evalExp_callAddrPrem1 {s : Store H} {f : Frame} {vs : List Val} {a : FuncAddr}
    {fi : FuncInst H} {fn : V2.Func} (hf : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
    (hk : vs.length = fi.type.params.length) :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
        (.strE [.mk "TYPE" ftKNE20, .mk "MODULE" (.varE "mm"), .mk "CODE" (.varE "func")]))
      (.bool true) := by
  have fk : (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn)).findVal? "k" =
      some (.num (.natN fi.type.params.length)) :=
    show some (Value.num (.natN (vs.map valV).length)) = _ by simp [hk]
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (.strE [.mk "TYPE" ftKNE20, .mk "MODULE" (.varE "mm"), .mk "CODE" (.varE "func")])
      (funcInstV hn fi) := by
    rw [funcInstV_wasm hcode]
    exact evalExp_str3_20 (evalExp_ftPrem20 fk rfl rfl rfl) (evalExp_var rfl) (evalExp_var rfl)
  exact evalExp_eqTrue (evalExp_funcinstAt20 rfl rfl rfl hf) hr

/-- The image of `val^k (CALL_ADDR a)`. -/
theorem configV_callAddr20 (s : Store H) (f : Frame) (vs : List Val) (a : FuncAddr) :
    configV hn ⟨s, f, vals vs ++ [.callAddr a]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list (vs.map valV ++ [.case "CALL_ADDR" (.num (.natN a))])]) := by
  simp only [configV, Pure.adminsToV_append, Pure.adminsToV_vals]
  rfl

/-- The image of the callee's frame. -/
theorem adminsToV_callFrame20 (n : Nat) (F : Frame) (body : List V2.Instr) :
    adminsToV [.frame n F [.label n [] (expression body)]] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV F, .list [.case "LABEL_%{%}%"
        (.tuple [.num (.natN n), .list [], .list (instrsToV body)])]])] := by
  show [Value.case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV F,
    .list [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV []),
      .list (adminsToV (expression body))])]])] = _
  rw [Pure.adminsToV_expression]
  rfl

/-- **`Step_read/call_addr` fires forward** at the image of V2's `ReadStep.callAddr`, from a
typed state. -/
theorem fires_callAddr20 {s : Store H} {f : Frame} {vs : List Val} {a : FuncAddr}
    {fi : FuncInst H} {fn : V2.Func} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
    (hk : vs.length = fi.type.params.length) :
    Fires (simEnv20 B) "Step_read" 5 (.tuple [configV hn ⟨s, f, vals vs ++ [.callAddr a]⟩,
      .list (adminsToV [.frame fi.type.results.length (calleeFrame20 fi vs fn)
        [.label fi.type.results.length [] (expression fn.body)]])]) := by
  have hfi := typedV_funcInst_of_state20 hz hf
  obtain ⟨hm, hfunc⟩ := typedV_funcInst_parts20 hcode hfi
  have hi := typedV_body_of_func20 hfunc
  have hρ : ValsOnly (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn)) :=
    Pure.valsOnly_bindVals _
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (match callAddrRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedV_nat20 _ _ hρ)
      (QuantsOk.cons rfl (typedV_vals20 vs _ hρ) (QuantsOk.cons rfl (typedV_addr20 a _ hρ)
        (QuantsOk.cons rfl (typedV_n20 _ _ hρ) (QuantsOk.cons rfl (typedV_frame_of20 hm _ _ hρ)
          (QuantsOk.cons rfl (hi _ hρ) (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ)
            (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ) (QuantsOk.cons rfl (hm _ hρ)
              (QuantsOk.cons rfl (hfunc _ hρ) (QuantsOk.cons rfl (typedV_idx20 _ _ hρ)
                (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ) QuantsOk.nil))))))))))))
  have hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (.caseE "%;%" (.tupE [.varE "z", .catE valsKE20 (.listE [.caseE "CALL_ADDR" (.varE "a")])]))
      (configV hn ⟨s, f, vals vs ++ [.callAddr a]⟩) := by
    rw [configV_callAddr20]
    exact evalExp_case (evalExp_tup2 (evalExp_var rfl) (Sim.evalExp_cat
      (Pure.evalExp_valsN (by decide) rfl rfl) (evalExp_list1 (evalExp_case (evalExp_var rfl)))))
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n", .varE "f", .listE [.caseE "LABEL_%{%}%"
        (.tupE [.varE "n", .listE [], instrsAdmE20])]])])
      (.list (adminsToV [.frame fi.type.results.length (calleeFrame20 fi vs fn)
        [.label fi.type.results.length [] (expression fn.body)]])) := by
    rw [adminsToV_callFrame20]
    exact evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) Pure.evalExp_list0
        (Pure.evalExp_subIter (by decide) rfl))))))
  have p₂ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (.cmpE .eqOp .boolT (.varE "func") funcE20) (.bool true) :=
    evalExp_eqTrue (evalExp_var rfl) evalExp_funcE20
  have p₃ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals (callAddrSigma20 hn s f vs a fi fn))
      (.cmpE .eqOp .boolT (.varE "f") frameE20) (.bool true) :=
    evalExp_eqTrue (evalExp_var rfl) evalExp_frameE20
  refine Pure.fires_of_ruleAt hasRuleAt_callAddr20 _ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl | rfl
  · exact .ifPr (evalExp_callAddrPrem1 hf hcode hk)
  · exact .ifPr p₂
  · exact .ifPr p₃


/-! ## The fragment -/

/-- **V2's `call_addr` of a Wasm function**, with V2's premises. -/
inductive CallAddrFwd20 : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {a : FuncAddr} {vs : List Val} {fi : FuncInst H} {fn : V2.Func}
      (hf : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
      (hk : vs.length = fi.type.params.length) :
      CallAddrFwd20 ⟨s, f, vals vs ++ [.callAddr a]⟩
        ⟨s, f, [.frame fi.type.results.length (Frame.forCall fi.module vs fn.locals)
          [.label fi.type.results.length [] (expression fn.body)]]⟩

theorem CallAddrFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : CallAddrFwd20 c c') : Step P host c c' := by
  cases h with
  | mk hf hcode hk => exact .read (.callAddr hf hcode hk)

/-- **Subject reduction for `call_addr`**: the callee's frame and body are typed. -/
theorem typed20_succ_callAddr20 {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c)
    (h : CallAddrFwd20 c c') : Typed20 (simEnv20 B) hn c' := by
  obtain ⟨hz, -⟩ := typed20_iff.1 hc
  cases h with
  | @mk s f a vs fi fn hf hcode hk =>
    obtain ⟨hm, hfunc⟩ := typedV_funcInst_parts20 hcode (typedV_funcInst_of_state20 hz hf)
    have hlab : TypedV (simEnv20 B) adminsTy (.list (adminsToV
        [.label fi.type.results.length [] (expression fn.body)])) :=
      typedV_admins_single20_iff.2 (typedV_adminLabel20_iff.2 ⟨typedV_n20 _, typedV_instrs_nil20,
        (typedV_admins_expression20_iff _).2 (typedV_body_of_func20 hfunc)⟩)
    exact typed20_iff.2 ⟨hz, typedV_admins_single20_iff.2 (typedV_adminFrame20_iff.2
      ⟨typedV_n20 _, typedV_frame_of20 hm _, hlab⟩)⟩

/-- **`call_addr` is a base**, at every builtins and any store condition. -/
theorem fwdBase20_callAddr {W : Store H → Prop} : FwdBase20 B hn W (CallAddrFwd20 (H := H)) where
  sr c c' hc h := typed20_succ_callAddr20 hc h
  fwd c c' hc _ h := by
    have hc' := typed20_succ_callAddr20 hc h
    have hz := typedV_state_of_typed20 hc
    cases h with
    | mk hf hcode hk =>
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_callAddr20 hz hf hcode hk)))

/-! ## The widened forward statement -/

/-- **The base at `storeB`, with `block`, `loop` and `call_addr`.** -/
inductive FwdStep20C (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20BL P c c') : FwdStep20C P c c'
  | callAddr {c c' : Config H} (h : CallAddrFwd20 c c') : FwdStep20C P c c'

theorem FwdStep20C.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20C P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | callAddr h => exact h.step

/-- The widened base is a base at `storeB`. -/
theorem fwdBase20_fwdC (P : Profile) :
    FwdBase20 (storeB P) hn WholePages (FwdStep20C (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdBL P).sr c c' hc h
    | callAddr h => exact (fwdBase20_callAddr (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdBL P).fwd c c' hc hw h
    | callAddr h => exact fwdBase20_callAddr.fwd c c' hc hw h

/-- **The forward 2.0 half with `block`, `loop` and `call_addr`** (stated and proved): at
`storeB`, every step of `Nest20 (FwdStep20C P)` from a configuration with typed image and whole
pages is a step of the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20C : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20C P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20C` is proved**, at every profile. -/
theorem wholeStepFwd20C : Task.wholeStepFwd20C :=
  fun _ _ P _ _ hc hw h => fwd_nest20 (fwdBase20_fwdC P) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
