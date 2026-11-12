module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnTyp

/-!
# `call_addr` and `call_indirect` in `simEnv20T`, from a state typed there

* `firesT_callAddr` (`Step_read` 5): the callee's module, code and body are quantifiers, typed
  in `simEnv20T` from the state (`typedT_funcInst_of_state`, `typedT_funcInst_parts`,
  `typedT_body_of_func`); the body may hold stores.
* `firesT_callIndirectCall` (`Step_read` 3).
* `firesT_callIndirectTrap` (`Step_read` 4, `-- otherwise`). Its `otherwise` is proved in
  `simEnv20T` directly (`otherwise4T`): rules 0–2 name other instructions (round 3's tag table,
  which `simEnv20T` shares), and rule 3's body is refuted (`not_callIndBodyT`) by moving its
  evaluations back to `simEnv20` (`evalBack20`) and reading them as round 3 does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk RuleBody otherwiseAt
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (otherwiseAt_of_table tags_of_take relRules ruleTags)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (callAddrRule20 callAddrSigma20 calleeFrame20 codeV20
  configV_callAddr20 adminsToV_callFrame20 evalExp_callAddrPrem1 evalExp_funcE20 evalExp_frameE20
  evalExp_eqTrue valsKE20 instrsAdmE20 funcE20 frameE20 callIndirectCallRule20
  callIndirectTrapRule20 constIE tableE iPay evalExp_constIE evalExp_trapRhs table?_some
  evalExp_table20 evalExp_iPay evalExp_type20 evalExp_funcinstAt20)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems evParams)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## `call_addr` -/

/-- **`Step_read/call_addr` in `simEnv20T`**, from a state typed there: the callee's body may
hold stores. -/
theorem firesT_callAddr {s : Store H} {f : Frame} {vs : List Val} {a : FuncAddr}
    {fi : FuncInst H} {fn : V2.Func} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
    (hk : vs.length = fi.type.params.length) :
    Fires (simEnv20T B) "Step_read" 5 (.tuple [configV hn ⟨s, f, vals vs ++ [.callAddr a]⟩,
      .list (adminsToV [.frame fi.type.results.length (calleeFrame20 fi vs fn)
        [.label fi.type.results.length [] (expression fn.body)]])]) := by
  obtain ⟨hm, hfunc⟩ := typedT_funcInst_parts hcode (typedT_funcInst_of_state hz hf)
  have hi := typedT_body_of_func hfunc
  let σ := callAddrSigma20 hn s f vs a fi fn
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals _
  have hvt : ∀ ts : List V2.ValType, TypedV (simEnv20T B) (.iterT (.varT "valtype" []) .list)
      (.list (ts.map valTypeV)) := fun ts => StoreDeep.typedV_valTypesT ts
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match callAddrRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (StoreDeep.typedV_natT _ _ hρ)
      (QuantsOk.cons rfl (StoreDeep.typedV_valsT20 vs _ hρ)
        (QuantsOk.cons rfl (typedT (by decide) (Whole.typedV_addr20 a) _ hρ)
        (QuantsOk.cons rfl (typedT_n _ _ hρ) (QuantsOk.cons rfl (typedT_frame_of hm _ _ hρ)
          (QuantsOk.cons rfl (hi _ hρ) (QuantsOk.cons rfl (hvt _ _ hρ)
            (QuantsOk.cons rfl (hvt _ _ hρ) (QuantsOk.cons rfl (hm _ hρ)
              (QuantsOk.cons rfl (hfunc _ hρ) (QuantsOk.cons rfl (typedT_idx _ _ hρ)
                (QuantsOk.cons rfl (hvt _ _ hρ) QuantsOk.nil))))))))))))
  have hl : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .catE valsKE20 (.listE [.caseE "CALL_ADDR" (.varE "a")])]))
      (configV hn ⟨s, f, vals vs ++ [.callAddr a]⟩) := by
    rw [configV_callAddr20]
    exact evalExp_case (evalExp_tup2 (evalExp_var rfl) (Sim.evalExp_cat
      (Pure.evalExp_valsN (by decide) rfl rfl) (evalExp_list1 (evalExp_case (evalExp_var rfl)))))
  have hr : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n", .varE "f", .listE [.caseE "LABEL_%{%}%"
        (.tupE [.varE "n", .listE [], instrsAdmE20])]])])
      (.list (adminsToV [.frame fi.type.results.length (calleeFrame20 fi vs fn)
        [.label fi.type.results.length [] (expression fn.body)]])) := by
    rw [adminsToV_callFrame20]
    exact evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl) Pure.evalExp_list0
        (Pure.evalExp_subIter (by decide) rfl))))))
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) Whole.hasRuleAt_callAddr20 rfl
    σ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl | rfl
  · exact .ifPr (evalExp_callAddrPrem1 hf hcode hk)
  · exact .ifPr (evalExp_eqTrue (evalExp_var rfl) evalExp_funcE20)
  · exact .ifPr (evalExp_eqTrue (evalExp_var rfl) evalExp_frameE20)

/-! ## `call_indirect-call` -/

/-- **`Step_read/call_indirect-call` in `simEnv20T`.** -/
theorem firesT_callIndirectCall {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {i : BitVec 32} {ti : TableInst} {a : FuncAddr} {fi : FuncInst H}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some (.funcAddr a))
    (hf : s.funcInst? a = some fi) (hy : (⟨s, f⟩ : State H).type? y = some fi.type) :
    Fires (simEnv20T B) "Step_read" 3 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩,
      .list (adminsToV [.callAddr a])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("x", idxV x),
    ("y", idxV y), ("a", .num (.natN a))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match callIndirectCallRule20 with | .ruleD _ qs _ _ _ => qs) :=
    quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ) (QuantsOk.cons rfl (Whole.typedV_idx20 y _ hρ)
        (QuantsOk.cons rfl (Whole.typedV_addr20 a _ hρ) QuantsOk.nil))))
  have hl : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]]))
      (configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE rfl) (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl)
        (evalExp_var rfl))) evalExps_nil), rfl⟩))
  have hr' : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CALL_ADDR" (.varE "a")]) (.list (adminsToV [.callAddr a])) :=
    evalExp_list1 (evalExp_case (evalExp_var rfl))
  obtain ⟨ta, hta, htt⟩ := table?_some ht
  have p₁ : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.idxE (.dotE tableE "REFS") iPay) (.caseE "REF.FUNC_ADDR" (.varE "a")))
      (.bool true) := by
    refine evalExp_eqTrue (v := refV (.funcAddr a)) (evalExp_idxE_iff.2 ⟨_, i.toNat,
      evalExp_dotE_iff.2 ⟨tableInstV ti, evalExp_table20 rfl (evalExp_var rfl) (evalExp_var rfl)
        hta htt, rfl⟩, evalExp_iPay rfl, ?_⟩) (evalExp_case (evalExp_var rfl))
    simp [Value.idx?, List.getElem?_map, hr]
  have p₂ : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "type" [.expA (.varE "z"), .expA (.varE "y")])
        (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")) (.bool true) :=
    evalExp_eqTrue (evalExp_type20 rfl (evalExp_var rfl) (evalExp_var rfl)
      (by simpa [State.type?, ModuleInst.type?] using hy))
      (evalExp_dotE_iff.2 ⟨funcInstV hn fi, evalExp_funcinstAt20 rfl rfl rfl hf, rfl⟩)
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True)
    Whole.hasRuleAt_callIndirectCall20 rfl σ hq (evalExp_tup2 hl hr') ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .ifPr p₁
  · exact .ifPr p₂

/-! ## `call_indirect-trap` -/

/-- **Relation-free syntax evaluates in `simEnv20` as in `simEnv20T`**, in a scope of values. -/
theorem evalBack20 {ρ : VarEnv} {e : Exp} {v : Value} (hρ : ValsOnly ρ)
    (hG : RelFree.GoodEvs RelFree.bad20 (evExp e)) (h : EvalExp (simEnv20T B) ρ e v) :
    EvalExp (E20 B) ρ e v := by
  have hS : EvalExp (StepFix.simEnv20S B) ρ e v :=
    StoreAgree.evalExp_of (StoreAgree.envSame20T B).symm h
  rw [RelFree.simEnv20S_eq B] at hS
  exact (RelFree.evalExp_withRels_iff (RelFree.defsGood_simEnv20 B) (defsOk_of_valsOnly hρ) hG).1 hS

/-- The pieces of rule 3, relation-free. -/
theorem good_callInd (B : Builtins) : RelFree.GoodEvs RelFree.bad20 (evExp (match callIndirectCallRule20 with
      | .ruleD _ _ _ e _ => e)) ∧
    RelFree.GoodEvs RelFree.bad20 (evPrems (match callIndirectCallRule20 with
      | .ruleD _ _ _ _ prems => prems)) := by
  have hG := RelFree.goodEvs_of_all (readGood (B := B) Whole.hasRuleAt_callIndirectCall20)
  simp only [callIndirectCallRule20, evRule, RelFree.goodEvs_append] at hG ⊢
  exact ⟨hG.1.2, hG.2⟩

/-- The parts of rule 3's body in `simEnv20T` at a `call_indirect` left-hand side, moved back
to `simEnv20`: the bound operands and both premises. -/
theorem callIndBodyT_parts {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame} {x : TableIdx}
    {y : TypeIdx} {i : BitVec 32} {c' : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%" callIndirectCallRule20
      (.tuple [configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩, c'])) :
    ∃ ρ : VarEnv, ρ.findVal? "z" = some (stateV hn s f) ∧
      ρ.findVal? "i" = some (pctV i.toNat) ∧ ρ.findVal? "x" = some (idxV x) ∧
      ρ.findVal? "y" = some (idxV y) ∧ ρ.findDef? "table" = none ∧ ρ.findDef? "type" = none ∧
      ρ.findDef? "funcinst" = none ∧
      EvalExp (E20 B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE tableE "REFS") iPay)
        (.caseE "REF.FUNC_ADDR" (.varE "a"))) (.bool true) ∧
      EvalExp (E20 B) ρ (.cmpE .eqOp .boolT
        (.callE "type" [.expA (.varE "z"), .expA (.varE "y")])
        (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")) (.bool true) := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  obtain ⟨gE, gP⟩ := good_callInd B
  have gPs := RelFree.goodEvs_prems gP
  have hl := Sim.RefsGC.lhs_of_concl (evalBack20 hρ gE he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f,
      .list (adminsToV [constI32 i, .plain (.callIndirect x y)])] := (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  obtain ⟨fi, fx, fy⟩ := Whole.callIndScope_of (Sim.RefsGC.elems_of_list hL)
  exact ⟨_, evalExp_varE_iff.1 hZ, fi, fx, fy, rfl, rfl, rfl,
    evalBack20 hρ (gPs _ (List.mem_cons_self ..)) (Pure.ifPrem (hp _ (List.mem_cons_self ..))),
    evalBack20 hρ (gPs _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))⟩

/-- **Rule 3's body is refuted in `simEnv20T`** where V2 traps and the type index is defined. -/
theorem not_callIndBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame} {x : TableIdx}
    {y : TypeIdx} {i : BitVec 32} {ti : TableInst} {ft : V2.FuncType}
    (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hft : (⟨s, f⟩ : State H).type? y = some ft)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) (c' : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" callIndirectCallRule20
      (.tuple [configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩, c']) := by
  intro hbody
  obtain ⟨ρ, fz, fi, fx, fy, d₁, d₂, d₃, p₁, p₂⟩ := callIndBodyT_parts hbody
  obtain ⟨ta, hta, htt⟩ := table?_some ht
  have hft' : f.module.types[y.toNat]? = some ft := by
    simpa [State.type?, ModuleInst.type?] using hft
  obtain ⟨a, hr, fa⟩ := Whole.entry_of_callIndPrem fz fi fx d₁ hta htt p₁
  obtain ⟨fn, hfn, hty⟩ := Whole.type_of_callIndPrem fz fy fa d₂ d₃ hft' p₂
  exact h ⟨a, fn, hr, hfn, hty ▸ hft⟩

/-- `simEnv20T`'s `Step_read` rules are `simEnv20`'s. -/
theorem relRules_readT : relRules (simEnv20T B) "Step_read" = relRules (E20 B) "Step_read" := by
  obtain ⟨t', rules', h₁, h₂, -⟩ := RelFree.readRules20_spec B
  simp only [relRules, ((StoreAgree.envSame20T B).rels "Step_read").trans h₂, h₁]

/-- **`otherwise` holds for rule 4 in `simEnv20T`** where V2 traps and the type index is
defined. -/
theorem otherwise4T {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32}
    {ti : TableInst} {ft : V2.FuncType} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hft : (⟨s, f⟩ : State H).type? y = some ft)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩, w]) := by
  have h3 := hasRuleAtT_read (Whole.hasRuleAt_callIndirectCall20 (B := B))
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := h3
  have hT : ((relRules (simEnv20T B) "Step_read").map ruleTags).take 47 = Whole.readTags20 := by
    rw [relRules_readT, Whole.relRules_simEnv20, Whole.readTags20_eq]
    rfl
  refine otherwiseAt_of_table hrel (tags_of_take hrel hT) (by decide)
    (Whole.lhsIn_callInd s f i x y) (exc := [3]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read Whole.hasRuleAt_callIndirectCall20) hr]
  exact not_callIndBodyT ht hft h c'

/-- **`Step_read/call_indirect-trap` in `simEnv20T`**, where the type index is defined. -/
theorem firesT_callIndirectTrap {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {i : BitVec 32} {ti : TableInst} {ft : V2.FuncType}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hft : (⟨s, f⟩ : State H).type? y = some ft)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) :
    Fires (simEnv20T B) "Step_read" 4 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩,
      .list (adminsToV [.trap])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("x", idxV x),
    ("y", idxV y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      (match callIndirectTrapRule20 with | .ruleD _ qs _ _ _ => qs) :=
    quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ) (QuantsOk.cons rfl (Whole.typedV_idx20 y _ hρ)
        QuantsOk.nil)))
  have hl : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]]))
      (configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE rfl) (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl)
        (evalExp_var rfl))) evalExps_nil), rfl⟩))
  have hG := RelFree.goodEvs_of_all (readGood (B := B) Whole.hasRuleAt_callIndirectTrap20)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (match callIndirectTrapRule20 with
      | .ruleD _ _ _ e _ => e)) := by
    simp only [callIndirectTrapRule20, evRule, RelFree.goodEvs_append] at hG ⊢
    exact hG.1.2
  refine Pure.fires_of_ruleAt (hasRuleAtT_read Whole.hasRuleAt_callIndirectTrap20) σ hq
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 hl evalExp_trapRhs)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise4T ht hft h _)

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
