module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepTyp

/-!
# The rules that copy an `instr*`, in `simEnv20T`

Once stores may stand inside instruction trees, every rule that quantifies over an `instr*` may
meet one, and a store is an `instr` of `simEnv20T` only. Round 3 fired these rules in `simEnv20`;
here they fire in `simEnv20T`, with every quantifier typed there:

* `Step_pure` 5 and 6 (`if-true`, `if-false`): `spureT_ifTrue`, `spureT_ifFalse`;
* `Step_pure` 7 (`label-vals`) and 18 (`trap-label`): `spureT_labelVals`, `spureT_trapLabel`;
* `Step_read` 0 and 1 (`block`, `loop`): `sreadT_block`, `sreadT_loop`, and as steps of
  `simEnv20T` from a typed state, `sstepT_block`, `sstepT_loop`.

The `Step_pure` rules are evaluated 's environment-generic lemmas (`Pure.eval_if`,
`Pure.eval_labelVals`). The `Step_read` rules are evaluated by environment-generic copies of round
3's (`evalExp_blockLhsG`, `evalExp_labelBodyG`), and their premise `$blocktype(z, bt) = …`
is round 3's evaluation in `simEnv20` (`Whole.blocktypePrem_sigma20`), moved: relation-free
syntax evaluates alike in `simEnv20` and `simEnv20S` (`RelFree.evalExp_withRels`), and
`simEnv20S` and `simEnv20T` share every definition (`StoreAgree.evalExp_of`). This is
`evalT_of_20`. Every rule is found in `simEnv20T` by `rfl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreDeep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure SRead QuantsOk ValsOnly Fires stateT dderives_of_ruleAt cfgV
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (blockRule20 loopRule20 valsKE20 instrsE20 instrsAdmE20
  blockSigma20)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} (B : Builtins)

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Provenance in `simEnv20T` -/

theorem hasRuleAt_ifTrueT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 5 Pure.ifTrueRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_ifFalseT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 6 Pure.ifFalseRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_labelValsT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 7 Pure.labelValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_trapLabelT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 18 Pure.trapLabelRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_blockT : HasRuleAt (simEnv20T B) "Step_read" "%~>%" 0 blockRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_loopT : HasRuleAt (simEnv20T B) "Step_read" "%~>%" 1 loopRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem findRel_readT : ∃ t rules,
    (simEnv20T B).findRel? "Step_read" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩

variable {B}

/-! ## Moving an evaluation from `simEnv20` to `simEnv20T` -/

/-- **Relation-free syntax evaluates in `simEnv20T` as in `simEnv20`**, in a scope of values. -/
theorem evalT_of_20 {ρ : VarEnv} {e : Exp} {v : Value} (hρ : ValsOnly ρ)
    (hG : RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evExp e)) (h : EvalExp (E20 B) ρ e v) :
    EvalExp (simEnv20T B) ρ e v := by
  have hD : RelFree.DefsOk RelFree.bad20 ρ := fun p hp => by
    rw [hρ.2.1] at hp
    cases hp
  have hS : EvalExp (StepFix.simEnv20S B) ρ e v := by
    rw [RelFree.simEnv20S_eq B]
    exact RelFree.evalExp_withRels (RelFree.defsGood_simEnv20 B) hD hG h
  exact StoreAgree.evalExp_of (StoreAgree.envSame20T B) hS

/-! ## `if` -/

/-- A typing of `simEnv20` of a relation-free type is one of `simEnv20T`. -/
theorem typedV_toT {t : Typ} {v : Value}
    (ht : (Sim.Round7.Script.evTyp t).all (RelFree.rfEvB RelFree.bad20) = true)
    (h : TypedV (E20 B) t v) : TypedV (simEnv20T B) t v :=
  StoreAgree.typedV_of (StoreAgree.envSame20T B) (StoreAgree.typRepair20T B)
    (Whole.typedV_withRels20 ht h)

theorem typedV_i32T (c : BitVec 32) : TypedV (simEnv20T B) Pure.i32T (pctV c.toNat) :=
  typedV_toT (by decide) ((Pure.numTyped_simEnv20 B).i32 c)

/-- The quantifiers of the `if` rules, typed in `simEnv20T`. -/
theorem ifQuantsT {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (hb : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt))
    (h₁ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₁)))
    (h₂ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₂))) :
    QuantsOk (simEnv20T B) (Pure.ifScope c bt b₁ b₂)
      (match Pure.ifTrueRule with | .ruleD _ qs _ _ _ => qs) :=
  QuantsOk.cons rfl (typedV_i32T c _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hb _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (h₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (h₂ _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil)))

/-- **`if-true` in `simEnv20T`.** -/
theorem spureT_ifTrue {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr} (hc : c ≠ 0)
    (hb : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt))
    (h₁ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₁)))
    (h₂ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₂))) :
    SPure (simEnv20T B) (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)])
      (adminsToV [.plain (.block bt b₁)]) := by
  rw [Pure.adminsToV_if]
  exact dderives_of_ruleAt (hasRuleAt_ifTrueT B) _ (ifQuantsT hb h₁ h₂)
    (Pure.eval_if (ρ := Pure.ifScope c bt b₁ b₂) rfl rfl rfl rfl).1
    (Sim.prems_one (.ifPr (Pure.evalExp_immCmp rfl (Pure.cmp_ne_zero hc))))

/-- **`if-false` in `simEnv20T`.** -/
theorem spureT_ifFalse {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (hb : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt))
    (h₁ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₁)))
    (h₂ : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV b₂))) :
    SPure (simEnv20T B) (adminsToV [constI32 0, .plain (.if_ bt b₁ b₂)])
      (adminsToV [.plain (.block bt b₂)]) := by
  rw [Pure.adminsToV_if]
  exact dderives_of_ruleAt (hasRuleAt_ifFalseT B) _ (ifQuantsT hb h₁ h₂)
    (Pure.eval_if (ρ := Pure.ifScope 0 bt b₁ b₂) rfl rfl rfl rfl).2
    (Sim.prems_one (.ifPr (Pure.evalExp_immCmp rfl Pure.cmp_eq_zero)))

/-! ## `label-vals`, `trap-label` -/

/-- **`label-vals` in `simEnv20T`.** -/
theorem spureT_labelVals {n : Nat} {cont : List V2.Instr} {vs : List Val}
    (hn : TypedV (simEnv20T B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont))) :
    SPure (simEnv20T B) (adminsToV [.label n cont (vals vs)]) (adminsToV (vals vs)) :=
  dderives_of_ruleAt (hasRuleAt_labelValsT B)
    [("n", .num (.natN n)), ("instr*", .list (instrsToV cont)), ("val*", .list (adminsToV (vals vs)))]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (StoreGood.typedV_valsT20T vs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (Pure.eval_labelVals rfl rfl rfl) Sim.Exn.prems_nil

/-- **`trap-label` in `simEnv20T`.** -/
theorem spureT_trapLabel {n : Nat} {cont : List V2.Instr}
    (hn : TypedV (simEnv20T B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont))) :
    SPure (simEnv20T B) (adminsToV [.label n cont [.trap]]) (adminsToV [.trap]) :=
  dderives_of_ruleAt (hasRuleAt_trapLabelT B)
    [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont))]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl)
      (Pure.evalExp_iter (by decide) rfl) (evalExp_list1 Pure.evalExp_caseNil))))
      (evalExp_list1 Pure.evalExp_caseNil)) Sim.Exn.prems_nil

/-! ## `block` and `loop` -/

/-- The left-hand side `z; val^k (op bt instr*)`, evaluated in any environment. -/
theorem evalExp_blockLhsG {env : Env} {ρ : VarEnv} {op : MixopS} {Z bt : Value}
    {ws is : List Value} (fz : ρ.findVal? "z" = some Z)
    (fk : ρ.findVal? "k" = some (.num (.natN ws.length))) (fv : ρ.findVal? "val*" = some (.list ws))
    (fb : ρ.findVal? "bt" = some bt) (fi : ρ.findVal? "instr*" = some (.list is)) :
    EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .catE valsKE20
        (.listE [.caseE op (.tupE [.varE "bt", instrsE20])])]))
      (.case "%;%" (.tuple [Z, .list (ws ++ [.case op (.tuple [bt, .list is])])])) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) (Sim.evalExp_cat (Pure.evalExp_valsN (by decide) fk fv)
    (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) (Pure.evalExp_iter (by decide) fi))))))

/-- `val^k instr*`, coerced, evaluated in any environment. -/
theorem evalExp_labelBodyG {env : Env} {ρ : VarEnv} {ws is : List Value}
    (fk : ρ.findVal? "k" = some (.num (.natN ws.length)))
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list is)) :
    EvalExp env ρ (.catE valsKE20 instrsAdmE20) (.list (ws ++ is)) :=
  Sim.evalExp_cat (Pure.evalExp_valsN (by decide) fk fv) (Pure.evalExp_subIter (by decide) fi)

/-- The premise `$blocktype(z, bt) = t_1^k -> t_2^n`. -/
abbrev blocktypePremE : Exp :=
  .cmpE .eqOp .boolT (.callE "blocktype" [.expA (.varE "z"), .expA (.varE "bt")])
    (.caseE "%->%" (.tupE [
      .caseE "%" (.tupE [.iterE (.varE "t_1") (.mk (.listN (.varE "k") none)
        [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2") (.mk (.listN (.varE "n") none)
        [.mk "t_2" (.varE "t_2*")])])]))

theorem goodEvs_blocktypePrem :
    RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evExp blocktypePremE) :=
  RelFree.goodEvs_of_all (by decide)

/-- The quantifier typings `block` and `loop` need beyond the state, in `simEnv20T`. -/
structure BlockTypedT (B : Builtins) (bt : V2.BlockType) (body : List V2.Instr) : Prop where
  bt : TypedV (simEnv20T B) Pure.blocktypeT (blockTypeV bt)
  body : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV body))

theorem typedV_natT (k : Nat) : TypedV (simEnv20T B) (.numT .natT) (.num (.natN k)) :=
  typedV_toT (by decide) (Whole.typedV_nat20 k)

theorem typedV_valsT20 (vs : List Val) :
    TypedV (simEnv20T B) (.iterT (.varT "val" []) .list) (.list (vs.map valV)) := by
  exact StoreAgree.typedV_list_to20T (x := "val") (by decide) (Whole.typedV_vals20 vs)

theorem typedV_valTypesT (ts : List V2.ValType) :
    TypedV (simEnv20T B) (.iterT (.varT "valtype" []) .list) (.list (ts.map valTypeV)) :=
  StoreAgree.typedV_list_to20T (x := "valtype") (by decide) (Whole.typedV_valTypes20 ts)

theorem typedV_nT (k : Nat) : TypedV (simEnv20T B) (.varT "n" []) (.num (.natN k)) :=
  StoreAgree.typedV_to20T (x := "n") (by decide) (Whole.typedV_n20 k)

/-- **`Step_read/block` fires in `simEnv20T`** at the image of V2's `ReadStep.block`. -/
theorem firesT_block {s : Store H} {f : Frame} {vs : List Val} {bt : V2.BlockType}
    {body : List V2.Instr} {ft : V2.FuncType} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (T : BlockTypedT B bt body) (hbt : f.module.blockType? bt = some ft)
    (hk : vs.length = ft.params.length) :
    Fires (simEnv20T B) "Step_read" 0 (.tuple [
      configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩,
      .list (adminsToV [.label ft.results.length [] (vals vs ++ expression body)])]) := by
  have hρ : ValsOnly (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft)) :=
    Pure.valsOnly_bindVals _
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft))
      (match blockRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedV_natT _ _ hρ)
      (QuantsOk.cons rfl (typedV_valsT20 vs _ hρ) (QuantsOk.cons rfl (T.bt _ hρ)
        (QuantsOk.cons rfl (T.body _ hρ) (QuantsOk.cons rfl (typedV_nT _ _ hρ)
          (QuantsOk.cons rfl (typedV_valTypesT _ _ hρ)
            (QuantsOk.cons rfl (typedV_valTypesT _ _ hρ) QuantsOk.nil)))))))
  have hl := evalExp_blockLhsG (env := simEnv20T B) (op := "BLOCK") (Z := stateV hn s f)
    (bt := blockTypeV bt) (ws := vs.map valV) (is := instrsToV body)
    (ρ := VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft)) rfl rfl rfl rfl rfl
  have hr : EvalExp (simEnv20T B) (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft))
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], .catE valsKE20 instrsAdmE20])])
      (.list (adminsToV [.label ft.results.length [] (vals vs ++ expression body)])) := by
    rw [Whole.adminsToV_labelBody]
    exact evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) Pure.evalExp_list0
      (evalExp_labelBodyG rfl rfl rfl)))
  have hp : EvalExp (simEnv20T B) (VarEnv.empty.bindVals (blockSigma20 hn s f vs bt body ft))
      blocktypePremE (.bool true) :=
    evalT_of_20 hρ goodEvs_blocktypePrem (Whole.blocktypePrem_sigma20 hbt hk)
  have hc : configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list (vs.map valV ++
        [.case "BLOCK" (.tuple [blockTypeV bt, .list (instrsToV body)])])]) := by
    simp only [configV, Whole.adminsToV_valsBlock]
  rw [hc]
  refine Pure.fires_of_ruleAt (hasRuleAt_blockT B) _ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr hp

/-- The assignment of `loop` at V2's left-hand side. -/
abbrev loopSigma (hn : H → String) (s : Store H) (f : Frame) (vs : List Val) (bt : V2.BlockType)
    (body : List V2.Instr) (ft : V2.FuncType) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("k", .num (.natN (vs.map valV).length)), ("val*", .list (vs.map valV)),
    ("bt", blockTypeV bt), ("instr*", .list (instrsToV body)),
    ("t_1*", .list (ft.params.map valTypeV)), ("n", .num (.natN ft.results.length)),
    ("t_2*", .list (ft.results.map valTypeV))]

/-- The premise of `loop`, in `simEnv20`. -/
theorem loopPrem20 {s : Store H} {f : Frame} {vs : List Val} {bt : V2.BlockType}
    {body : List V2.Instr} {ft : V2.FuncType} (hbt : f.module.blockType? bt = some ft)
    (hk : vs.length = ft.params.length) :
    EvalExp (E20 B) (VarEnv.empty.bindVals (loopSigma hn s f vs bt body ft)) blocktypePremE
      (.bool true) :=
  Whole.evalExp_blocktypePrem20 rfl rfl rfl
    (show some (Value.num (.natN (vs.map valV).length)) = _ by simp [hk]) rfl rfl rfl hbt

/-- **`Step_read/loop` fires in `simEnv20T`** at the image of V2's `ReadStep.loop`. -/
theorem firesT_loop {s : Store H} {f : Frame} {vs : List Val} {bt : V2.BlockType}
    {body : List V2.Instr} {ft : V2.FuncType} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (T : BlockTypedT B bt body) (hbt : f.module.blockType? bt = some ft)
    (hk : vs.length = ft.params.length) :
    Fires (simEnv20T B) "Step_read" 1 (.tuple [
      configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩,
      .list (adminsToV [.label ft.params.length [.loop bt body] (vals vs ++ expression body)])]) := by
  let σ := loopSigma hn s f vs bt body ft
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals _
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match loopRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedV_natT _ _ hρ)
      (QuantsOk.cons rfl (typedV_valsT20 vs _ hρ) (QuantsOk.cons rfl (T.bt _ hρ)
        (QuantsOk.cons rfl (T.body _ hρ) (QuantsOk.cons rfl (typedV_valTypesT _ _ hρ)
          (QuantsOk.cons rfl (typedV_nT _ _ hρ)
            (QuantsOk.cons rfl (typedV_valTypesT _ _ hρ) QuantsOk.nil)))))))
  have hl := evalExp_blockLhsG (env := simEnv20T B) (op := "LOOP") (Z := stateV hn s f)
    (bt := blockTypeV bt) (ws := vs.map valV) (is := instrsToV body)
    (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl rfl
  have fk : (VarEnv.empty.bindVals σ).findVal? "k" = some (.num (.natN ft.params.length)) :=
    show some (Value.num (.natN (vs.map valV).length)) = _ by simp [hk]
  have hr : EvalExp (simEnv20T B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "k",
        .listE [.caseE "LOOP" (.tupE [.varE "bt", instrsE20])], .catE valsKE20 instrsAdmE20])])
      (.list (adminsToV [.label ft.params.length [.loop bt body] (vals vs ++ expression body)])) := by
    rw [Whole.adminsToV_labelBody]
    exact evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var fk)
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
        (Pure.evalExp_iter (by decide) rfl)))) (evalExp_labelBodyG rfl rfl rfl)))
  have hc : configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list (vs.map valV ++
        [.case "LOOP" (.tuple [blockTypeV bt, .list (instrsToV body)])])]) := by
    simp only [configV, Whole.adminsToV_valsLoop]
  have hp : EvalExp (simEnv20T B) (VarEnv.empty.bindVals σ) blocktypePremE (.bool true) :=
    evalT_of_20 hρ goodEvs_blocktypePrem (loopPrem20 hbt hk)
  rw [hc]
  refine Pure.fires_of_ruleAt (hasRuleAt_loopT B) _ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr hp

/-- A `Step_read` firing of `simEnv20T` is a step of `simEnv20T`, from a state and codes typed
there. -/
theorem sstepT_of_firesRead {k : Nat} {z : Value} {is js : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (his : TypedV (simEnv20T B) adminsTy (.list is))
    (hjs : TypedV (simEnv20T B) adminsTy (.list js))
    (h : Fires (simEnv20T B) "Step_read" k (.tuple [cfgV z is, .list js])) :
    SStepB (simEnv20T B) (cfgV z is) (cfgV z js) := by
  obtain ⟨t, rules, hrel⟩ := findRel_readT B
  have hr : SRead (simEnv20T B) (cfgV z is) js := (Sim.dderives_iff_fires hrel).2 ⟨k, h⟩
  exact (StoreFix.sstepB20T_iff B).2 (StoreRun.sstepT_read hz his hjs hr)

end Silmaril.Wasm.SpecTec.Sim20.StoreDeep
