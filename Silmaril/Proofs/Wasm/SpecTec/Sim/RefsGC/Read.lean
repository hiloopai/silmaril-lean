module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Pure

/-!
# Family R: the reference rules of `Step_read`, forward

`ref.null`, `ref.func`, `ref.test-*`, `ref.cast-*` (rules 63–68) and `br_on_cast*` (rules 2–5),
as `Step_read` steps of the images of Core's steps. The cast rules read `Ref_ok` through
`RefOkBridge`, and `$moduleinst`/`$inst_reftype` through `RStoreFuns`. The `-fail` rules use
`otherwise`; the one earlier rule with the same opcode is the matching `-succeed`/`-true` rule,
refuted through the bridge.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {env : Env} {H : Type} {hn : H → String}

/-- The frame's module, by field selection. -/
theorem evalExp_frameModule {ρ : VarEnv} {e : Exp} {f : Frame} (h : EvalExp env ρ e (frameV f)) :
    EvalExp env ρ (.dotE e "MODULE") (moduleInstToValue' f.module) :=
  evalExp_dotE_iff.2 ⟨_, h, rfl⟩

/-- The `Ref_ok` premise of the cast rules, evaluated. -/
theorem evalExp_refOkArg (G : RStoreFuns env) {ρ : VarEnv} {s : Store H} {f : Frame} {r : Ref}
    {rt : RefType} (hvo : ValsOnly ρ) (hs : EvalExp env ρ (.varE "s") (storeV hn s))
    (hf : EvalExp env ρ (.varE "f") (frameV f)) (hr : EvalExp env ρ (.varE "ref") (refToValue r))
    {x : IL.Id} (ht : EvalExp env ρ (.varE x) (Encode.toValue rt)) :
    EvalExp env ρ (.tupE [.varE "s", .varE "ref",
        .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]])
      (.tuple [storeV hn s, refToValue r, CT.elemType (f.module.instRef rt)]) :=
  evalExp_tupE_of (evalExps_cons' hs (evalExps_cons' hr (evalExps_cons'
    (G.instReftype ρ _ _ f.module rt hvo (evalExp_frameModule hf) ht) evalExps_nil')))

/-! ## `ref.null`, `ref.func` -/

/-- `ref.null` (rule 63). -/
theorem sread_refNull (h : HasRuleAt env "Step_read" "%~>%" 63 refNullRule) (R : RTyping env)
    {s : Store H} {f : Frame} {ht : HeapType} (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.plain (.refNull ht)]))) :
    SRead env (configV hn ⟨s, f, [.plain (.refNull ht)]⟩) (adminsToV [.ref .null]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("ht", Encode.toValue ht)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hht : TypedV env heaptypeT (Encode.toValue ht) :=
    R.arg "REF.NULL" _ heaptypeT (by simp [argTypes]) hc
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (hht _ hρ) QuantsOk.nil))
    (by eval_tac) (fun _ hp => nomatch hp)

/-! ## `ref.test` -/

/-- `ref.test-true` (rule 65). -/
theorem sread_refTestTrue (h : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (hok : RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refTest rt)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) (adminsToV [constI32 1]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.TEST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K.refOk hn _ s r _).2 hok)))

/-- `ref.func` (rule 64). -/
theorem sread_refFunc (h : HasRuleAt env "Step_read" "%~>%" 64 refFuncRule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.plain (.refFunc x)]))) :
    SRead env (configV hn ⟨s, f, [.plain (.refFunc x)]⟩) (adminsToV [.ref (.func a)]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hx : TypedV env idxT (Encode.toValue x) := R.arg "REF.FUNC" _ idxT (by simp [argTypes]) hc
  have hm := G.moduleinst hn (VarEnv.empty.bindVals σ) (.varE "z") s f hρ (by eval_tac)
  have hfs : EvalExp env (VarEnv.empty.bindVals σ)
      (.dotE (.callE "moduleinst" [.expA (.varE "z")]) "FUNCS")
      (.list (f.module.funcs.map fun a => .num (.natN a))) := evalExp_dotE_iff.2 ⟨_, hm, rfl⟩
  have hi : EvalExp env (VarEnv.empty.bindVals σ) (.projE (.uncaseE (.varE "x") "%") 0)
      (.num (.natN x.toNat)) :=
    evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (by eval_tac), le_refl _, rfl⟩
  have hidx : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.dotE (.callE "moduleinst" [.expA (.varE "z")]) "FUNCS")
        (.projE (.uncaseE (.varE "x") "%") 0)) (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨_, _, hfs, hi, by simp [Value.idx?, ha]⟩
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (hx _ hρ) QuantsOk.nil))
    (evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_case hidx))) (fun _ hp => nomatch hp)

/-- A `Ref_ok` premise of a cast rule that holds gives `RefOk`. -/
theorem refOk_of_prem (G : RStoreFuns env) (K : RefOkBridge env) {O : ElseI} {els : Prop}
    {ρ : VarEnv} {s : Store H} {f : Frame} {r : Ref} {rt : RefType} {x : IL.Id} (hvo : ValsOnly ρ)
    (hs : EvalExp env ρ (.varE "s") (storeV hn s)) (hf : EvalExp env ρ (.varE "f") (frameV f))
    (hr : EvalExp env ρ (.varE "ref") (refToValue r))
    (ht : EvalExp env ρ (.varE x) (Encode.toValue rt))
    (hp : PremW env (DDerives env O) els ρ (.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s",
      .varE "ref", .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]]))) :
    RefOk s r (f.module.instRef rt) := by
  obtain ⟨w, he, hd⟩ := premW_rule hp
  have hw := EvalExp.unique he (evalExp_refOkArg G hvo hs hf hr ht)
  rw [hw] at hd
  exact (K.refOk hn O s r _).1 hd

/-- The bindings of a left-hand side `(s; f); [ref, OP e₂]`. -/
theorem binds_ref1 {ρ : VarEnv} {op : MixopS} {e₂ : Exp} {t₁ t₂ : Typ} {a b x w : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]),
      .listE [.subE (.varE "ref") t₁ t₂, .caseE op e₂]])) (cfgV (stV a b) [x, .case op w])) :
    EvalExp env ρ (.varE "s") a ∧ EvalExp env ρ (.varE "f") b ∧ EvalExp env ρ (.varE "ref") x ∧
      EvalExp env ρ e₂ w := by
  obtain ⟨hs, hf, hl⟩ := cfg_inv h
  have h₁ := evalExps_cons_inv (elems_of_list hl)
  have h₂ := evalExps_cons_inv h₁.2
  exact ⟨hs, hf, evalExp_subE_iff.1 h₁.1, case_inv h₂.1⟩

/-- The third of three bound components. -/
theorem third_of_tup3 {ρ : VarEnv} {x₁ x₂ x₃ : IL.Id} {w₁ w₂ w₃ : Value}
    (h : EvalExp env ρ (.tupE [.varE x₁, .varE x₂, .varE x₃]) (.tuple [w₁, w₂, w₃])) :
    EvalExp env ρ (.varE x₃) w₃ :=
  (evalExps_cons_inv (evalExps_cons_inv (evalExps_cons_inv (elems_of_tup h)).2).2).1

/-! ## `ref.test-false`, `ref.cast-*` -/

/-- `ref.test-true` does not fire when the cast fails. -/
theorem not_refTestTrue (G : RStoreFuns env) (K : RefOkBridge env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (hok : ¬ RefOk s r (f.module.instRef rt))
    {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" refTestTrueRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  exact hok (refOk_of_prem G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `ref.test-false` (rule 66). -/
theorem sread_refTestFalse (h : HasRuleAt env "Step_read" "%~>%" 66 refTestFalseRule)
    (h₆₅ : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (hok : ¬ RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refTest rt)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) (adminsToV [constI32 0]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.TEST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  have ha : LhsIn (["REF.TEST"] ++ valTags) (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 66) (b := .list (adminsToV [constI32 0])) (by decide)
    (exc := [65]) ha (by decide) (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 65 := by simpa using hj
      rw [relRules_of_ruleAt h₆₅ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_refTestTrue G K hok)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.elsePr hel))

/-- `ref.cast-succeed` (rule 67). -/
theorem sread_refCastSucceed (h : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (hok : RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refCast rt)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩) (adminsToV [.ref r]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.CAST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K.refOk hn _ s r _).2 hok)))

/-- `ref.cast-succeed` does not fire when the cast fails. -/
theorem not_refCastSucceed (G : RStoreFuns env) (K : RefOkBridge env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (hok : ¬ RefOk s r (f.module.instRef rt))
    {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" refCastSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  exact hok (refOk_of_prem G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `ref.cast-fail` (rule 68). -/
theorem sread_refCastFail (h : HasRuleAt env "Step_read" "%~>%" 68 refCastFailRule)
    (h₆₇ : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (hok : ¬ RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refCast rt)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.CAST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  have ha : LhsIn (["REF.CAST"] ++ valTags) (configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 68) (b := .list (adminsToV [.trap])) (by decide)
    (exc := [67]) ha (by decide) (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 67 := by simpa using hj
      rw [relRules_of_ruleAt h₆₇ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_refCastSucceed G K hok)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.elsePr hel))

/-! ## `br_on_cast`, `br_on_cast_fail` -/

/-- The immediates of a typed `BR_ON_CAST`/`BR_ON_CAST_FAIL`. -/
theorem typed_brOnCast (R : RTyping env) {op : MixopS} (hop : op = "BR_ON_CAST" ∨ op = "BR_ON_CAST_FAIL")
    {l : LabelIdx} {rt₁ rt₂ : RefType}
    (h : TypedV env instrsT (.list [.case op
      (.tuple [Encode.toValue l, Encode.toValue rt₁, Encode.toValue rt₂])])) :
    TypedV env labelidxT (Encode.toValue l) ∧ TypedV env reftypeT (Encode.toValue rt₁) ∧
      TypedV env reftypeT (Encode.toValue rt₂) :=
  R.arg3 op _ _ _ _ _ _ (by rcases hop with rfl | rfl <;> simp [argTypes3]) h

/-- The bindings of `(s; f); [ref, BR_ON_CAST… (l, rt_1, rt_2)]`, through `rt_2`. -/
theorem binds_brOnCast {ρ : VarEnv} {op : MixopS} {t₁ t₂ : Typ} {a b x w₁ w₂ w₃ : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]),
      .listE [.subE (.varE "ref") t₁ t₂, .caseE op (.tupE [.varE "l", .varE "rt_1", .varE "rt_2"])]]))
      (cfgV (stV a b) [x, .case op (.tuple [w₁, w₂, w₃])])) :
    EvalExp env ρ (.varE "s") a ∧ EvalExp env ρ (.varE "f") b ∧ EvalExp env ρ (.varE "ref") x ∧
      EvalExp env ρ (.varE "rt_2") w₃ := by
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 h
  exact ⟨hs, hf, hr, third_of_tup3 ht⟩

/-- `brOnCastSucceed` (rule 2). -/
theorem sread_brOnCastSucceed (h : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
    (hok : RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCast l rt₁ rt₂)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩) (adminsToV [.ref r, .plain (.br l)]) := by
  let σ : List (IL.Id × Value) := [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r),
    ("l", Encode.toValue l), ("rt_1", Encode.toValue rt₁), ("rt_2", Encode.toValue rt₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  obtain ⟨hl, hrt₁, hrt₂⟩ := typed_brOnCast R (by decide) (typed_tail T hc)
  have hq : QuantsOk env (VarEnv.empty.bindVals σ) [.expP "s" storeT, .expP "f" frameT,
      .expP "ref" refT, .expP "l" labelidxT, .expP "rt_1" reftypeT, .expP "rt_2" reftypeT] :=
    QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ) (QuantsOk.cons rfl (hr _ hρ)
      (QuantsOk.cons rfl (hl _ hρ) (QuantsOk.cons rfl (hrt₁ _ hρ)
        (QuantsOk.cons rfl (hrt₂ _ hρ) QuantsOk.nil)))))
  exact dderives_of_ruleAt h σ hq (by eval_tac)
    (prems_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K.refOk hn _ s r _).2 hok)))

/-- `brOnCastSucceed` does not fire when the cast fails. -/
theorem not_brOnCastSucceed (G : RStoreFuns env) (K : RefOkBridge env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" brOnCastSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_brOnCast (lhs_of_concl he)
  exact hok (refOk_of_prem G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `brOnCastFail` (rule 3). -/
theorem sread_brOnCastFail (h : HasRuleAt env "Step_read" "%~>%" 3 brOnCastFailRule)
    (h₀ : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCast l rt₁ rt₂)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩) (adminsToV [.ref r]) := by
  let σ : List (IL.Id × Value) := [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r),
    ("l", Encode.toValue l), ("rt_1", Encode.toValue rt₁), ("rt_2", Encode.toValue rt₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  obtain ⟨hl, hrt₁, hrt₂⟩ := typed_brOnCast R (by decide) (typed_tail T hc)
  have hq : QuantsOk env (VarEnv.empty.bindVals σ) [.expP "s" storeT, .expP "f" frameT,
      .expP "ref" refT, .expP "l" labelidxT, .expP "rt_1" reftypeT, .expP "rt_2" reftypeT] :=
    QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ) (QuantsOk.cons rfl (hr _ hρ)
      (QuantsOk.cons rfl (hl _ hρ) (QuantsOk.cons rfl (hrt₁ _ hρ)
        (QuantsOk.cons rfl (hrt₂ _ hρ) QuantsOk.nil)))))
  have ha : LhsIn (["BR_ON_CAST"] ++ valTags)
      (configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 3) (b := .list (adminsToV [.ref r])) (by decide)
    (exc := [2]) ha (by decide) (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 2 := by simpa using hj
      rw [relRules_of_ruleAt h₀ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_brOnCastSucceed G K hok)
  exact dderives_of_ruleAt h σ hq (by eval_tac) (prems_one (.elsePr hel))

/-- `brOnCastFailSucceed` (rule 4). -/
theorem sread_brOnCastFailSucceed (h : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
    (hok : RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩) (adminsToV [.ref r]) := by
  let σ : List (IL.Id × Value) := [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r),
    ("l", Encode.toValue l), ("rt_1", Encode.toValue rt₁), ("rt_2", Encode.toValue rt₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  obtain ⟨hl, hrt₁, hrt₂⟩ := typed_brOnCast R (by decide) (typed_tail T hc)
  have hq : QuantsOk env (VarEnv.empty.bindVals σ) [.expP "s" storeT, .expP "f" frameT,
      .expP "ref" refT, .expP "l" labelidxT, .expP "rt_1" reftypeT, .expP "rt_2" reftypeT] :=
    QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ) (QuantsOk.cons rfl (hr _ hρ)
      (QuantsOk.cons rfl (hl _ hρ) (QuantsOk.cons rfl (hrt₁ _ hρ)
        (QuantsOk.cons rfl (hrt₂ _ hρ) QuantsOk.nil)))))
  exact dderives_of_ruleAt h σ hq (by eval_tac)
    (prems_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K.refOk hn _ s r _).2 hok)))

/-- `brOnCastFailSucceed` does not fire when the cast fails. -/
theorem not_brOnCastFailSucceed (G : RStoreFuns env) (K : RefOkBridge env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" brOnCastFailSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_brOnCast (lhs_of_concl he)
  exact hok (refOk_of_prem G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `brOnCastFailFail` (rule 5). -/
theorem sread_brOnCastFailFail (h : HasRuleAt env "Step_read" "%~>%" 5 brOnCastFailFailRule)
    (h₀ : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) (K : RefOkBridge env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩) (adminsToV [.ref r, .plain (.br l)]) := by
  let σ : List (IL.Id × Value) := [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r),
    ("l", Encode.toValue l), ("rt_1", Encode.toValue rt₁), ("rt_2", Encode.toValue rt₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  obtain ⟨hl, hrt₁, hrt₂⟩ := typed_brOnCast R (by decide) (typed_tail T hc)
  have hq : QuantsOk env (VarEnv.empty.bindVals σ) [.expP "s" storeT, .expP "f" frameT,
      .expP "ref" refT, .expP "l" labelidxT, .expP "rt_1" reftypeT, .expP "rt_2" reftypeT] :=
    QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ) (QuantsOk.cons rfl (hr _ hρ)
      (QuantsOk.cons rfl (hl _ hρ) (QuantsOk.cons rfl (hrt₁ _ hρ)
        (QuantsOk.cons rfl (hrt₂ _ hρ) QuantsOk.nil)))))
  have ha : LhsIn (["BR_ON_CAST_FAIL"] ++ valTags)
      (configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 5) (b := .list (adminsToV [.ref r, .plain (.br l)])) (by decide)
    (exc := [4]) ha (by decide) (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 4 := by simpa using hj
      rw [relRules_of_ruleAt h₀ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_brOnCastFailSucceed G K hok)
  exact dderives_of_ruleAt h σ hq (by eval_tac) (prems_one (.elsePr hel))

end Silmaril.Wasm.SpecTec.Sim.RefsGC
