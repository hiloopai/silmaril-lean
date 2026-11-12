module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Assemble

/-!
# Round 5: family R's cast rules from `Ref_ok` at one store and type

Family R's forward lemmas for `ref.test`, `ref.cast`, `br_on_cast` and `br_on_cast_fail`
(`RefsGC/Read.lean`) took `RefsGC.RefOkBridge`, which quantifies over every store and is argued
false (round 3, track refok). This file copies the lemmas that use it, each renamed with a
suffix `C`, with the bridge replaced by `RefOkAt env hn s (f.module.instRef rt)`: the bridge at
the one store and reference type of the step. The proofs are otherwise unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open RefsGC

variable {env : Env} {H : Type} {hn : H → String}

/-- `ref.test-true` (rule 65). -/
theorem sread_refTestTrueC (h : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) (hok : RefOk s r (f.module.instRef rt))
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
      ((K _ r).2 hok)))

/-- A `Ref_ok` premise of a cast rule that holds gives `RefOk`. -/
theorem refOk_of_premC (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {ρ : VarEnv} {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) {x : IL.Id} (hvo : ValsOnly ρ)
    (hs : EvalExp env ρ (.varE "s") (storeV hn s)) (hf : EvalExp env ρ (.varE "f") (frameV f))
    (hr : EvalExp env ρ (.varE "ref") (refToValue r))
    (ht : EvalExp env ρ (.varE x) (Encode.toValue rt))
    (hp : PremW env (DDerives env O) els ρ (.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s",
      .varE "ref", .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]]))) :
    RefOk s r (f.module.instRef rt) := by
  obtain ⟨w, he, hd⟩ := premW_rule hp
  have hw := EvalExp.unique he (evalExp_refOkArg G hvo hs hf hr ht)
  rw [hw] at hd
  exact (K O r).1 hd

/-- `ref.test-true` does not fire when the cast fails. -/
theorem not_refTestTrueC (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
    {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" refTestTrueRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  exact hok (refOk_of_premC G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `ref.test-false` (rule 66). -/
theorem sread_refTestFalseC (h : HasRuleAt env "Step_read" "%~>%" 66 refTestFalseRule)
    (h₆₅ : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
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
      exact not_refTestTrueC G K hok)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.elsePr hel))

/-- `ref.cast-succeed` (rule 67). -/
theorem sread_refCastSucceedC (h : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) (hok : RefOk s r (f.module.instRef rt))
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
      ((K _ r).2 hok)))

/-- `ref.cast-succeed` does not fire when the cast fails. -/
theorem not_refCastSucceedC (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
    {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" refCastSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  exact hok (refOk_of_premC G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `ref.cast-fail` (rule 68). -/
theorem sread_refCastFailC (h : HasRuleAt env "Step_read" "%~>%" 68 refCastFailRule)
    (h₆₇ : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAt env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
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
      exact not_refCastSucceedC G K hok)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.elsePr hel))

/-- `brOnCastSucceed` (rule 2). -/
theorem sread_brOnCastSucceedC (h : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAt env hn s (f.module.instRef rt₂))
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
      ((K _ r).2 hok)))

/-- `brOnCastSucceed` does not fire when the cast fails. -/
theorem not_brOnCastSucceedC (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAt env hn s (f.module.instRef rt₂))
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" brOnCastSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_brOnCast (lhs_of_concl he)
  exact hok (refOk_of_premC G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `brOnCastFail` (rule 3). -/
theorem sread_brOnCastFailC (h : HasRuleAt env "Step_read" "%~>%" 3 brOnCastFailRule)
    (h₀ : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAt env hn s (f.module.instRef rt₂))
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
      exact not_brOnCastSucceedC G K hok)
  exact dderives_of_ruleAt h σ hq (by eval_tac) (prems_one (.elsePr hel))

/-- `brOnCastFailSucceed` (rule 4). -/
theorem sread_brOnCastFailSucceedC (h : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAt env hn s (f.module.instRef rt₂))
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
      ((K _ r).2 hok)))

/-- `brOnCastFailSucceed` does not fire when the cast fails. -/
theorem not_brOnCastFailSucceedC (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAt env hn s (f.module.instRef rt₂))
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" brOnCastFailSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_brOnCast (lhs_of_concl he)
  exact hok (refOk_of_premC G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `brOnCastFailFail` (rule 5). -/
theorem sread_brOnCastFailFailC (h : HasRuleAt env "Step_read" "%~>%" 5 brOnCastFailFailRule)
    (h₀ : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAt env hn s (f.module.instRef rt₂))
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
      exact not_brOnCastFailSucceedC G K hok)
  exact dderives_of_ruleAt h σ hq (by eval_tac) (prems_one (.elsePr hel))

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
