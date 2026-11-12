module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdStoreFrag

/-!
# `block` and `loop` forward (`Step_read` 0 and 1)

2.0's

  `z; val^k (BLOCK bt instr*) ~> (LABEL_ n {eps} val^k instr*)`
  `z; val^k (LOOP bt instr*) ~> (LABEL_ k {LOOP bt instr*} val^k instr*)`

both under `$blocktype(z, bt) = t_1^k -> t_2^n`. The quantifiers `t_1*`, `t_2*` and `n` are bound
only by the premise; under the declarative reading they are quantified and typed like every
other variable, so the rules fire once they are given the function type's parameter and result
types (every 2.0 value type is a typed `valtype`, `typedV_valType20`).

* `callDef_blocktype20`: `$blocktype(z, bt)` is the image of V2's `blockType? bt` at the
  frame's module, through its three clauses (`_RESULT eps`, `_RESULT t`, `_IDX x`, the last
  through `$type(z, x) = f.MODULE.TYPES[x]`, `evalExp_type20`);
* `fires_block20`, `fires_loop20`: from a typed image, the rules fire at the image of V2's
  `ReadStep.block` and `ReadStep.loop`, with V2's premises;
* `BlockFwd20`: the two steps as a fragment, `fwdBase20_block` (subject reduction and the
  forward step), and **`Task.wholeStepFwd20BL`** (proved): at `storeB`, the nested fragment
  `FwdStep20L` plus `block` and `loop` is matched forward.
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
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 evalExp_call1 evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.State (sfxPat matchArgs_sfx frameV_module)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Value types are typed -/

theorem findTyp_valtype20 : (simEnv20 B).findTyp? "valtype" = some ([], [.instD [] [] (.variantT
    [.mk "I32" (.tupT []) [] [], .mk "I64" (.tupT []) [] [], .mk "F32" (.tupT []) [] [],
      .mk "F64" (.tupT []) [] [], .mk "V128" (.tupT []) [] [], .mk "FUNCREF" (.tupT []) [] [],
      .mk "EXTERNREF" (.tupT []) [] [], .mk "BOT" (.tupT []) [] []])]) := rfl

/-- **Every 2.0 value type is a typed `valtype`.** -/
theorem typedV_valType20 (t : V2.ValType) : TypedV (simEnv20 B) (.varT "valtype" []) (valTypeV t) := by
  rcases t with ((_ | _) | (_ | _)) | ⟨⟩ | (_ | _) <;>
    exact Pure.typedV_closedCase20 findTyp_valtype20 rfl hasTyp_tupT_nil

/-- Every list of 2.0 value types is a typed `valtype*`. -/
theorem typedV_valTypes20 (ts : List V2.ValType) :
    TypedV (simEnv20 B) (.iterT (.varT "valtype" []) .list) (.list (ts.map valTypeV)) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_valType20 t

/-- A natural number is a typed `nat`. -/
theorem typedV_nat20 (k : Nat) : TypedV (simEnv20 B) (.numT .natT) (.num (.natN k)) :=
  fun _ _ => hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩

/-! ## `$type` and `$blocktype` -/

theorem hasClause_type20 : HasClause1 (simEnv20 B) "type" sfxPat
    (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TYPES") Sim.State.idxPayload) := ⟨_, _, _, rfl⟩

/-- **`$type(z, x)`**, at a type index in range. -/
theorem evalExp_type20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : TypeIdx}
    {ft : V2.FuncType} (hρ : ρ.findDef? "type" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ht : f.module.types[x.toNat]? = some ft) :
    EvalExp (simEnv20 B) ρ (.callE "type" [.expA ez, .expA ex]) (funcTypeV ft) :=
  evalExp_call1 hasClause_type20 hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, List.getElem?_map, ht]⟩)

/-- The three clauses of `$blocktype` (`Original.d366`). -/
abbrev blocktypeClauses20 : List Clause :=
  [.defD [.expP "z" (.varT "state" [])] [.expA (.varE "z"), .expA (.caseE "_RESULT" (.optE none))]
      (.caseE "%->%" (.tupE [.caseE "%" (.tupE [.listE []]), .caseE "%" (.tupE [.listE []])])) [],
    .defD [.expP "z" (.varT "state" []), .expP "t" (.varT "valtype" [])]
      [.expA (.varE "z"), .expA (.caseE "_RESULT" (.optE (some (.varE "t"))))]
      (.caseE "%->%" (.tupE [.caseE "%" (.tupE [.listE []]), .caseE "%" (.tupE [.listE [.varE "t"]])]))
      [],
    .defD [.expP "z" (.varT "state" []), .expP "x" (.varT "idx" [])]
      [.expA (.varE "z"), .expA (.caseE "_IDX" (.varE "x"))]
      (.callE "type" [.expA (.varE "z"), .expA (.varE "x")]) []]

theorem findDef_blocktype20 :
    ∃ ps t, (simEnv20 B).findDef? "blocktype" = some (ps, t, blocktypeClauses20) := ⟨_, _, rfl⟩

/-- `%(eps) -> %(t?)`, evaluated. -/
theorem evalExp_resultFT {ρ : VarEnv} {es : List Exp} {ws : List Value}
    (h : EvalExps (simEnv20 B) ρ es ws) :
    EvalExp (simEnv20 B) ρ (.caseE "%->%" (.tupE [.caseE "%" (.tupE [.listE []]),
      .caseE "%" (.tupE [.listE es])]))
      (.case "%->%" (.tuple [.case "%" (.tuple [.list []]), .case "%" (.tuple [.list ws])])) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
    Pure.evalExp_list0 evalExps_nil, rfl⟩)) (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
      (evalExp_listE_iff.2 ⟨_, h, rfl⟩) evalExps_nil, rfl⟩)))

/-- `z` matches any value as the first argument. -/
theorem matchArgs_z {env : Env} {Z : Value} {pat : Arg} {w : ArgV} {ρ' : VarEnv}
    (h : MatchArgs env (VarEnv.empty.bindVal "z" Z) [pat] [w] ρ') :
    MatchArgs env VarEnv.empty [.expA (.varE "z"), pat] [.val Z, w] ρ' :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl)) h

/-- `z` matches, and the second argument does not. -/
theorem matchArgsUndef_z {env : Env} {Z : Value} {e : Exp} {v : Value}
    (h : MatchExpUndef env (VarEnv.empty.bindVal "z" Z) e v) :
    MatchArgsUndef env VarEnv.empty [.expA (.varE "z"), .expA e] [.val Z, .val v] :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (matchArg_expA_undef h))

/-- `z, _RESULT ?(t)` matches a state and a result block type. -/
theorem matchArgs_resultSome20 {Z : Value} (t : V2.ValType) :
    MatchArgs (simEnv20 B) VarEnv.empty
      [.expA (.varE "z"), .expA (.caseE "_RESULT" (.optE (some (.varE "t"))))]
      [.val Z, .val (blockTypeV (.result (some t)))]
      ((VarEnv.empty.bindVal "z" Z).bindVal "t" (valTypeV t)) :=
  matchArgs_z (matchArgs_cons (matchArg_expA (matchExp_caseE
    (Silmaril.SpecTec.Equiv.Validation.matchExp_optSome_iff.2 ⟨_, rfl, matchExp_varE rfl⟩)))
    matchArgs_nil)

/-- **`$blocktype(z, bt)` is V2's `blockType?`** at the frame's module. -/
theorem callDef_blocktype20 {ρ : VarEnv} {args : List Arg} {s : Store H} {f : Frame}
    {bt : V2.BlockType} {ft : V2.FuncType} (hρ : ρ.findDef? "blocktype" = none)
    (ha : EvalArgs (simEnv20 B) ρ args [.val (stateV hn s f), .val (blockTypeV bt)])
    (hbt : f.module.blockType? bt = some ft) :
    CallDef (simEnv20 B) ρ "blocktype" args (funcTypeV ft) := by
  obtain ⟨ps, t, hd⟩ := findDef_blocktype20 (B := B)
  refine callDef_of_tryClauses hρ hd ha ?_
  rcases bt with (_ | t) | x
  · obtain rfl : ft = ⟨[], []⟩ := (Option.some.inj hbt).symm
    exact tryClauses_hit (matchArgs_z (matchArgs_cons (matchArg_expA (matchExp_caseE
      (Silmaril.SpecTec.Equiv.Validation.matchExp_optNone_iff.2 ⟨rfl, rfl⟩))) matchArgs_nil)) premsHold_nil
      (evalExp_resultFT evalExps_nil)
  · obtain rfl : ft = ⟨[], [t]⟩ := (Option.some.inj hbt).symm
    refine tryClauses_skip_match (matchArgsUndef_z (matchExp_caseE_undef'
      Pure.matchExp_optNone_undef)) ?_
    exact tryClauses_hit (matchArgs_resultSome20 t) premsHold_nil
      (evalExp_resultFT (evalExps_cons (evalExp_var rfl) evalExps_nil))
  · refine tryClauses_skip_match (matchArgsUndef_z (matchExp_caseE_undef (by decide)))
      (tryClauses_skip_match (matchArgsUndef_z (matchExp_caseE_undef (by decide))) ?_)
    exact tryClauses_hit (matchArgs_z (matchArgs_cons (matchArg_expA (matchExp_caseE
      (matchExp_varE rfl))) matchArgs_nil)) premsHold_nil
      (evalExp_type20 rfl (evalExp_var rfl) (evalExp_var rfl) hbt)


/-! ## The rules -/

/-- `val^k`, coerced to `admininstr`. -/
abbrev valsKE20 : Exp := .iterE (.subE (.varE "val") (.varT "val" []) (.varT "admininstr" []))
  (.mk (.listN (.varE "k") none) [.mk "val" (.varE "val*")])

/-- `instr*`. -/
abbrev instrsE20 : Exp := .iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")])

/-- `instr*`, coerced to `admininstr`. -/
abbrev instrsAdmE20 : Exp :=
  .iterE (.subE (.varE "instr") (.varT "instr" []) (.varT "admininstr" []))
    (.mk .list [.mk "instr" (.varE "instr*")])

/-- `$blocktype(z, bt) = t_1^k -> t_2^n`. -/
abbrev blocktypePrem20 : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.callE "blocktype" [.expA (.varE "z"), .expA (.varE "bt")])
    (.caseE "%->%" (.tupE [
      .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])])))

/-- `Step_read/block`, rule 0 (transcribed). -/
def blockRule20 : Rule :=
  .ruleD "block" [.expP "z" (.varT "state" []), .expP "k" (.numT .natT),
      .expP "val*" (.iterT (.varT "val" []) .list), .expP "bt" (.varT "blocktype" []),
      .expP "instr*" (.iterT (.varT "instr" []) .list), .expP "n" (.varT "n" []),
      .expP "t_1*" (.iterT (.varT "valtype" []) .list), .expP "t_2*" (.iterT (.varT "valtype" []) .list)]
    "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .catE valsKE20
        (.listE [.caseE "BLOCK" (.tupE [.varE "bt", instrsE20])])]),
      .listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], .catE valsKE20 instrsAdmE20])]])
    [blocktypePrem20]

/-- `Step_read/loop`, rule 1 (transcribed). -/
def loopRule20 : Rule :=
  .ruleD "loop" [.expP "z" (.varT "state" []), .expP "k" (.numT .natT),
      .expP "val*" (.iterT (.varT "val" []) .list), .expP "bt" (.varT "blocktype" []),
      .expP "instr*" (.iterT (.varT "instr" []) .list),
      .expP "t_1*" (.iterT (.varT "valtype" []) .list), .expP "n" (.varT "n" []),
      .expP "t_2*" (.iterT (.varT "valtype" []) .list)]
    "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .catE valsKE20
        (.listE [.caseE "LOOP" (.tupE [.varE "bt", instrsE20])])]),
      .listE [.caseE "LABEL_%{%}%" (.tupE [.varE "k",
        .listE [.caseE "LOOP" (.tupE [.varE "bt", instrsE20])], .catE valsKE20 instrsAdmE20])]])
    [blocktypePrem20]

theorem hasRuleAt_block20 : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 0 blockRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_loop20 : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 1 loopRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Evaluating the pieces -/

/-- `x^c` over a list bound to `xs`, with `c` its length. -/
theorem evalExp_iterN20 {ρ : VarEnv} {x xs c : IL.Id} (hx : x ≠ "_") {ws : List Value}
    (hc : ρ.findVal? c = some (.num (.natN ws.length))) (hy : ρ.findVal? xs = some (.list ws)) :
    EvalExp (simEnv20 B) ρ (.iterE (.varE x) (.mk (.listN (.varE c) none) [.mk x (.varE xs)]))
      (.list ws) := by
  simpa using Sim.evalExp_iterNMap (g := id) hc hy fun _ _ => evalExp_var (Sim.findVal_bind1 hx)

/-- The right-hand side of the premise, at a function type. -/
theorem evalExp_ftPrem20 {ρ : VarEnv} {ft : V2.FuncType}
    (fk : ρ.findVal? "k" = some (.num (.natN ft.params.length)))
    (fn : ρ.findVal? "n" = some (.num (.natN ft.results.length)))
    (f₁ : ρ.findVal? "t_1*" = some (.list (ft.params.map valTypeV)))
    (f₂ : ρ.findVal? "t_2*" = some (.list (ft.results.map valTypeV))) :
    EvalExp (simEnv20 B) ρ (.caseE "%->%" (.tupE [
      .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])]))
      (funcTypeV ft) := by
  have e₁ := evalExp_iterN20 (B := B) (x := "t_1") (c := "k") (by decide) (by simpa using fk) f₁
  have e₂ := evalExp_iterN20 (B := B) (x := "t_2") (c := "n") (by decide) (by simpa using fn) f₂
  exact evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons e₁
    evalExps_nil, rfl⟩)) (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons e₂ evalExps_nil, rfl⟩)))

/-- **The premise holds** at V2's `blockType?`. -/
theorem evalExp_blocktypePrem20 {ρ : VarEnv} {s : Store H} {f : Frame} {bt : V2.BlockType}
    {ft : V2.FuncType} (hρ : ρ.findDef? "blocktype" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fb : ρ.findVal? "bt" = some (blockTypeV bt))
    (fk : ρ.findVal? "k" = some (.num (.natN ft.params.length)))
    (fn : ρ.findVal? "n" = some (.num (.natN ft.results.length)))
    (f₁ : ρ.findVal? "t_1*" = some (.list (ft.params.map valTypeV)))
    (f₂ : ρ.findVal? "t_2*" = some (.list (ft.results.map valTypeV)))
    (hbt : f.module.blockType? bt = some ft) :
    EvalExp (simEnv20 B) ρ (.cmpE .eqOp .boolT
      (.callE "blocktype" [.expA (.varE "z"), .expA (.varE "bt")])
      (.caseE "%->%" (.tupE [
        .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none) [.mk "t_1" (.varE "t_1*")])]),
        .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])])))
      (.bool true) :=
  evalExp_eqTrue (evalExp_callE_iff.2 (callDef_blocktype20 hρ (evalArgs_cons (evalExp_var fz)
    (evalArgs_cons (evalExp_var fb) evalArgs_nil)) hbt)) (evalExp_ftPrem20 fk fn f₁ f₂)

/-- The image of `val^k (BLOCK bt instr*)`. -/
theorem adminsToV_valsBlock (vs : List Val) (bt : V2.BlockType) (body : List V2.Instr) :
    adminsToV (vals vs ++ [.plain (.block bt body)]) =
      vs.map valV ++ [.case "BLOCK" (.tuple [blockTypeV bt, .list (instrsToV body)])] := by
  rw [Pure.adminsToV_append, Pure.adminsToV_vals]
  rfl

/-- The image of `val^k (LOOP bt instr*)`. -/
theorem adminsToV_valsLoop (vs : List Val) (bt : V2.BlockType) (body : List V2.Instr) :
    adminsToV (vals vs ++ [.plain (.loop bt body)]) =
      vs.map valV ++ [.case "LOOP" (.tuple [blockTypeV bt, .list (instrsToV body)])] := by
  rw [Pure.adminsToV_append, Pure.adminsToV_vals]
  rfl

/-- The image of a label around `val^k instr*`. -/
theorem adminsToV_labelBody (n : Nat) (cont : List V2.Instr) (vs : List Val)
    (body : List V2.Instr) :
    adminsToV [.label n cont (vals vs ++ expression body)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont),
        .list (vs.map valV ++ instrsToV body)])] := by
  show [Value.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont),
    .list (adminsToV (vals vs ++ expression body))])] = _
  rw [Pure.adminsToV_append, Pure.adminsToV_vals, Pure.adminsToV_expression]

/-- The left-hand side `z; val^k (op bt instr*)`, evaluated. -/
theorem evalExp_blockLhs20 {ρ : VarEnv} {op : MixopS} {Z bt : Value} {ws is : List Value}
    (fz : ρ.findVal? "z" = some Z) (fk : ρ.findVal? "k" = some (.num (.natN ws.length)))
    (fv : ρ.findVal? "val*" = some (.list ws)) (fb : ρ.findVal? "bt" = some bt)
    (fi : ρ.findVal? "instr*" = some (.list is)) :
    EvalExp (simEnv20 B) ρ (.caseE "%;%" (.tupE [.varE "z", .catE valsKE20
        (.listE [.caseE op (.tupE [.varE "bt", instrsE20])])]))
      (.case "%;%" (.tuple [Z, .list (ws ++ [.case op (.tuple [bt, .list is])])])) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) (Sim.evalExp_cat (Pure.evalExp_valsN (by decide) fk fv)
    (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) (Pure.evalExp_iter (by decide) fi))))))

/-- `val^k instr*`, coerced, evaluated. -/
theorem evalExp_labelBody20 {ρ : VarEnv} {ws is : List Value}
    (fk : ρ.findVal? "k" = some (.num (.natN ws.length)))
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list is)) :
    EvalExp (simEnv20 B) ρ (.catE valsKE20 instrsAdmE20) (.list (ws ++ is)) :=
  Sim.evalExp_cat (Pure.evalExp_valsN (by decide) fk fv) (Pure.evalExp_subIter (by decide) fi)


/-! ## The rules fire -/

/-- The assignment of `block` and `loop` at V2's left-hand side. -/
abbrev blockSigma20 (hn : H → String) (s : Store H) (f : Frame) (vs : List Val)
    (bt : V2.BlockType) (body : List V2.Instr) (ft : V2.FuncType) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("k", .num (.natN (vs.map valV).length)), ("val*", .list (vs.map valV)),
    ("bt", blockTypeV bt), ("instr*", .list (instrsToV body)),
    ("n", .num (.natN ft.results.length)), ("t_1*", .list (ft.params.map valTypeV)),
    ("t_2*", .list (ft.results.map valTypeV))]

/-- The premise of `block` and `loop` holds at the assignment. -/
theorem blocktypePrem_sigma20 {s : Store H} {f : Frame} {vs : List Val} {bt : V2.BlockType}
    {body : List V2.Instr} {ft : V2.FuncType} (hbt : f.module.blockType? bt = some ft)
    (hk : vs.length = ft.params.length) :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft))
      (.cmpE .eqOp .boolT (.callE "blocktype" [.expA (.varE "z"), .expA (.varE "bt")])
        (.caseE "%->%" (.tupE [
          .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none)
            [.mk "t_1" (.varE "t_1*")])]),
          .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none)
            [.mk "t_2" (.varE "t_2*")])])]))) (.bool true) :=
  evalExp_blocktypePrem20 rfl rfl rfl
    (show some (Value.num (.natN (vs.map valV).length)) = _ by simp [hk]) rfl rfl rfl hbt

/-- **`Step_read/block` fires forward** at the image of V2's `ReadStep.block`, from a typed
state, a typed block type and a typed body. -/
theorem fires_block20 {s : Store H} {f : Frame} {vs : List Val} {bt : V2.BlockType}
    {body : List V2.Instr} {ft : V2.FuncType} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hb : TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt))
    (hi : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV body)))
    (hbt : f.module.blockType? bt = some ft) (hk : vs.length = ft.params.length) :
    Fires (simEnv20 B) "Step_read" 0 (.tuple [
      configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩,
      .list (adminsToV [.label ft.results.length [] (vals vs ++ expression body)])]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft)) :=
    Pure.valsOnly_bindVals _
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft))
      (match blockRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedV_nat20 _ _ hρ)
      (QuantsOk.cons rfl (typedV_vals20 vs _ hρ) (QuantsOk.cons rfl (hb _ hρ)
        (QuantsOk.cons rfl (hi _ hρ) (QuantsOk.cons rfl (typedV_n20 _ _ hρ)
          (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ)
            (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ) QuantsOk.nil)))))))
  have hl := evalExp_blockLhs20 (B := B) (op := "BLOCK") (Z := stateV hn s f) (bt := blockTypeV bt)
    (ws := vs.map valV) (is := instrsToV body)
    (ρ := VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft)) rfl rfl rfl rfl rfl
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft))
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], .catE valsKE20 instrsAdmE20])])
      (.list (adminsToV [.label ft.results.length [] (vals vs ++ expression body)])) := by
    rw [adminsToV_labelBody]
    exact evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) Pure.evalExp_list0
      (evalExp_labelBody20 rfl rfl rfl)))
  have hc : configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list (vs.map valV ++
        [.case "BLOCK" (.tuple [blockTypeV bt, .list (instrsToV body)])])]) := by
    simp only [configV, adminsToV_valsBlock]
  rw [hc]
  refine Pure.fires_of_ruleAt hasRuleAt_block20 _ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (blocktypePrem_sigma20 hbt hk)

/-- **`Step_read/loop` fires forward** at the image of V2's `ReadStep.loop`. -/
theorem fires_loop20 {s : Store H} {f : Frame} {vs : List Val} {bt : V2.BlockType}
    {body : List V2.Instr} {ft : V2.FuncType} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hb : TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt))
    (hi : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV body)))
    (hbt : f.module.blockType? bt = some ft) (hk : vs.length = ft.params.length) :
    Fires (simEnv20 B) "Step_read" 1 (.tuple [
      configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩,
      .list (adminsToV [.label ft.params.length [.loop bt body] (vals vs ++ expression body)])]) := by
  let σ : List (IL.Id × Value) :=
    [("z", stateV hn s f), ("k", .num (.natN (vs.map valV).length)), ("val*", .list (vs.map valV)),
      ("bt", blockTypeV bt), ("instr*", .list (instrsToV body)),
      ("t_1*", .list (ft.params.map valTypeV)), ("n", .num (.natN ft.results.length)),
      ("t_2*", .list (ft.results.map valTypeV))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals _
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match loopRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedV_nat20 _ _ hρ)
      (QuantsOk.cons rfl (typedV_vals20 vs _ hρ) (QuantsOk.cons rfl (hb _ hρ)
        (QuantsOk.cons rfl (hi _ hρ) (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ)
          (QuantsOk.cons rfl (typedV_n20 _ _ hρ)
            (QuantsOk.cons rfl (typedV_valTypes20 _ _ hρ) QuantsOk.nil)))))))
  have hl := evalExp_blockLhs20 (B := B) (op := "LOOP") (Z := stateV hn s f) (bt := blockTypeV bt)
    (ws := vs.map valV) (is := instrsToV body) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl rfl
  have fk : (VarEnv.empty.bindVals σ).findVal? "k" = some (.num (.natN ft.params.length)) :=
    show some (Value.num (.natN (vs.map valV).length)) = _ by simp [hk]
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "k",
        .listE [.caseE "LOOP" (.tupE [.varE "bt", instrsE20])], .catE valsKE20 instrsAdmE20])])
      (.list (adminsToV [.label ft.params.length [.loop bt body] (vals vs ++ expression body)])) := by
    rw [adminsToV_labelBody]
    exact evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var fk)
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
        (Pure.evalExp_iter (by decide) rfl)))) (evalExp_labelBody20 rfl rfl rfl)))
  have hc : configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list (vs.map valV ++
        [.case "LOOP" (.tuple [blockTypeV bt, .list (instrsToV body)])])]) := by
    simp only [configV, adminsToV_valsLoop]
  have hp : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "blocktype" [.expA (.varE "z"), .expA (.varE "bt")])
        (.caseE "%->%" (.tupE [
          .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none)
            [.mk "t_1" (.varE "t_1*")])]),
          .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none)
            [.mk "t_2" (.varE "t_2*")])])]))) (.bool true) :=
    evalExp_blocktypePrem20 rfl rfl rfl fk rfl rfl rfl hbt
  rw [hc]
  refine Pure.fires_of_ruleAt hasRuleAt_loop20 _ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr hp


/-! ## Typing -/

/-- A typed `BLOCK` has a typed block type and body. -/
theorem typed_block_inv20 {bt : V2.BlockType} {b : List V2.Instr} (h : TypedI B (.block bt b)) :
    TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b)) := by
  obtain ⟨h₁, h₂⟩ := hasTyp_tup2_inv20 (hasTyp_adminCase20 rfl h)
  exact ⟨typedV_of_empty20 h₁, typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂⟩

/-- A typed `LOOP` has a typed block type and body. -/
theorem typed_loop_inv20 {bt : V2.BlockType} {b : List V2.Instr} (h : TypedI B (.loop bt b)) :
    TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b)) := by
  obtain ⟨h₁, h₂⟩ := hasTyp_tup2_inv20 (hasTyp_adminCase20 rfl h)
  exact ⟨typedV_of_empty20 h₁, typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂⟩

/-- A label around `val^k instr*` with a typed continuation is a typed `admininstr*`. -/
theorem typedV_labelBody20 (n : Nat) {cont : List V2.Instr} (vs : List Val) {body : List V2.Instr}
    (hcont : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV cont)))
    (hi : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV body))) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV [.label n cont (vals vs ++ expression body)])) :=
  typedV_admins_single20_iff.2 (typedV_adminLabel20_iff.2 ⟨typedV_n20 n, hcont,
    typedV_admins_append20_iff.2 ⟨typedV_admins_vals20 vs, (typedV_admins_expression20_iff body).2 hi⟩⟩)

/-- The empty continuation is typed. -/
theorem typedV_instrs_nil20 : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV [])) :=
  Sim.typedV_list_iff.2 fun _ h => nomatch h

/-- A one-instruction continuation is typed when the instruction is. -/
theorem typedV_instrs_one20 {i : V2.Instr} (h : TypedI B i) :
    TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV [i])) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain rfl := List.mem_singleton.1 hu
    exact (typedV_plain20_iff i).1 h

/-! ## The fragment -/

/-- **V2's `block` and `loop`**, with V2's premises. -/
inductive BlockFwd20 : Config H → Config H → Prop where
  | block {s : Store H} {f : Frame} {bt : V2.BlockType} {body : List V2.Instr} {vs : List Val}
      {ft : V2.FuncType} (hbt : f.module.blockType? bt = some ft)
      (hk : vs.length = ft.params.length) :
      BlockFwd20 ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
        ⟨s, f, [.label ft.results.length [] (vals vs ++ expression body)]⟩
  | loop {s : Store H} {f : Frame} {bt : V2.BlockType} {body : List V2.Instr} {vs : List Val}
      {ft : V2.FuncType} (hbt : f.module.blockType? bt = some ft)
      (hk : vs.length = ft.params.length) :
      BlockFwd20 ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
        ⟨s, f, [.label ft.params.length [.loop bt body] (vals vs ++ expression body)]⟩

theorem BlockFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : BlockFwd20 c c') : Step P host c c' := by
  cases h with
  | block hbt hk => exact .read (.block hbt hk)
  | loop hbt hk => exact .read (.loop hbt hk)

/-- **Subject reduction for `block` and `loop`.** -/
theorem typed20_succ_block20 {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c)
    (h : BlockFwd20 c c') : Typed20 (simEnv20 B) hn c' := by
  obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
  cases h with
  | @block s f bt body vs ft _ _ =>
    have hb := typed_block_inv20 (typedI_of_mem hcode (i := .block bt body) (by simp))
    exact typed20_iff.2 ⟨hz, typedV_labelBody20 _ vs typedV_instrs_nil20 hb.2⟩
  | @loop s f bt body vs ft _ _ =>
    have hl : TypedI B (.loop bt body) := typedI_of_mem hcode (by simp)
    exact typed20_iff.2 ⟨hz, typedV_labelBody20 _ vs (typedV_instrs_one20 hl)
      (typed_loop_inv20 hl).2⟩

/-- **`block` and `loop` are a base**, at every builtins and any store condition. -/
theorem fwdBase20_block {W : Store H → Prop} : FwdBase20 B hn W (BlockFwd20 (H := H)) where
  sr c c' hc h := typed20_succ_block20 hc h
  fwd c c' hc _ h := by
    have hc' := typed20_succ_block20 hc h
    obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
    cases h with
    | @block s f bt body vs ft hbt hk =>
      obtain ⟨hb, hi⟩ := typed_block_inv20 (typedI_of_mem hcode (i := .block bt body) (by simp))
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_block20 hz hb hi hbt hk)))
    | @loop s f bt body vs ft hbt hk =>
      obtain ⟨hb, hi⟩ := typed_loop_inv20 (typedI_of_mem hcode (i := .loop bt body) (by simp))
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_loop20 hz hb hi hbt hk)))

/-! ## The widened forward statement -/

/-- **The base at `storeB`, with `block` and `loop`.** -/
inductive FwdStep20BL (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20L P c c') : FwdStep20BL P c c'
  | block {c c' : Config H} (h : BlockFwd20 c c') : FwdStep20BL P c c'

theorem FwdStep20BL.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20BL P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | block h => exact h.step

/-- Pass 2's base at `storeB`. -/
theorem fwdBase20_storeL (P : Profile) : FwdBase20 (storeB P) hn WholePages (FwdStep20L (H := H) P) :=
  fwdBase20_fwdL (growCalls20_storeB _) (Pure.numAgree_simEnv20 (intB_storeB _) (floatB_storeB P))
    (Pure.cvtAgree_simEnv20 (floatB_storeB P)) (vbytes20_storeB _) (laneCalls20_storeB _)

/-- The widened base is a base at `storeB`. -/
theorem fwdBase20_fwdBL (P : Profile) :
    FwdBase20 (storeB P) hn WholePages (FwdStep20BL (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_storeL P).sr c c' hc h
    | block h => exact (fwdBase20_block (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_storeL P).fwd c c' hc hw h
    | block h => exact fwdBase20_block.fwd c c' hc hw h

/-- **The forward 2.0 half with `block` and `loop`** (stated and proved): at `storeB`, every
step of `Nest20 (FwdStep20BL P)` from a configuration with typed image and whole pages is a step
of the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20BL : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20BL P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20BL` is proved**, at every profile. -/
theorem wholeStepFwd20BL : Task.wholeStepFwd20BL :=
  fun _ _ P _ _ hc hw h => fwd_nest20 (fwdBase20_fwdBL P) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
