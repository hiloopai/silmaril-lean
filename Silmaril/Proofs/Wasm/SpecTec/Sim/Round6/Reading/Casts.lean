module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Ref
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms

/-!
# Round 6: the cast rules of `Step_read`, forward, under `DDerivesB`

Round 5's `Round5Fwd/RefsCopy.lean` proved `ref.test`, `ref.cast`, `br_on_cast` and
`br_on_cast_fail` (rules 2–5 and 65–68 of `Step_read`), forward, from `RefOkAt` at the store and
type of the step. This file copies those proofs, each renamed with a suffix `B`, for the new
reading: `RefOkAtB` instead of `RefOkAt`, `SReadB` instead of `SRead`. Only the plumbing changes
(`dderivesB_of_ruleAt`, `otherwiseB_of_ruleAt`, `ruleBody_of_ruleBodyB`): the cast rules'
conclusions have no empty-domain option iteration, so each is its own only alternative.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

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

/-! ## Plumbing -/

/-- A rule whose conclusion has no empty-domain option iteration: its body under the new reading
is its body. -/
theorem ruleBody_of_ruleBodyB {D : Interp} {els : Prop} {ps : List Param} {args : List ArgV}
    {op : MixopS} {r : Rule} {v : Value} (hn : hasOptNil (ruleConcl r) = false)
    (h : RuleBodyB env D els ps args op r v) : RuleBody env D els ps args op r v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  exact (ruleBodyB_iff_of_not hn).1 h

/-- A rule that is plain, or names a cast constructor without empty-domain options, has none. -/
theorem noOpt_of_plainOrTags {S : List IL.Id} {K : List MixopS} {r : Rule}
    (h : (plainRuleB S r || (!hasOptNil (ruleConcl r) &&
      (RefsGC.ruleTags r).any fun op => decide (op ∈ K))) = true) :
    hasOptNil (ruleConcl r) = false := by
  obtain ⟨nm, qs, op, e, prems⟩ := r
  simp only [plainRuleB, ruleConcl, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact h.1
  · exact h.1

/-- No rule of `Step_read` has an empty-domain option iteration in its conclusion. -/
theorem noOpt_read {r : Rule} (hr : r ∈ RefsGC.relRules (envOfScript Specs.wasm30) "Step_read") :
    hasOptNil (ruleConcl r) = false :=
  noOpt_of_plainOrTags (List.all_eq_true.1 plainOrTagsB_read r hr)

/-- **`otherwise` by opcode, under the new reading** (`RefsGC.otherwise_of_ruleAt` for
`otherwiseB`): every earlier rule outside `exc` names a constructor the left-hand side avoids, and
the rules in `exc` are refuted separately. -/
theorem otherwiseB_of_ruleAt {x : IL.Id} {k : Nat} {r : Rule}
    (h : HasRuleAt env x "%~>%" k r) {n : Nat} {T : List (List MixopS)}
    (hT : ((relRules env x).map ruleTags).take n = T) {i : Nat} (hi : i ≤ T.length)
    {S : List MixopS} {exc : List Nat} {a b : Value} (ha : LhsIn S a)
    (hc : checkAvoid T i exc S = true)
    (hno : ∀ (j : Nat) (r' : Rule), (relRules env x)[j]? = some r' → hasOptNil (ruleConcl r') = false)
    (hexc : ∀ j ∈ exc, j < i → ∀ r', (relRules env x)[j]? = some r' → ∀ w,
      SameLhs (.tuple [a, b]) w →
      ¬ RuleBodyB env (DDerivesB env noElse) (otherwiseAtB env x [] j w) [] [] "%~>%" r' w) :
    otherwiseB env x [] i (.tuple [a, b]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := h
  have hrr : relRules env x = rules := by simp [relRules, hrel]
  have htg := tags_of_take hrel hT
  show otherwiseAtB env x [] i (.tuple [a, b])
  rw [otherwiseAtB]
  intro j hj ps' op t' rules' r' hrel' hr' w hw
  have he : (([] : List Param), ("%~>%" : MixopS), t, rules) = (ps', op, t', rules') :=
    Option.some.inj (hrel.symm.trans hrel')
  obtain ⟨rfl, rfl, rfl, rfl⟩ : [] = ps' ∧ "%~>%" = op ∧ t = t' ∧ rules = rules' := by
    simpa only [Prod.mk.injEq] using he
  by_cases hx : j ∈ exc
  · exact hexc j hx hj r' (hrr ▸ hr') w hw
  · obtain ⟨op', hop', hS⟩ := checkAvoid_sound hc hj hx
    obtain ⟨c, rfl⟩ := sameLhs_tuple hw
    have hjT : j < T.length := Nat.lt_of_lt_of_le hj hi
    rw [← htg j r' hr' hjT] at hop'
    exact fun hB => not_ruleBody_of_tags ha hop' hS
      (ruleBody_of_ruleBodyB (hno j r' (hrr ▸ hr')) hB)

/-- `Step_read`'s rules, by index, have no empty-domain option iteration in their conclusions. -/
theorem noOpt_read_at (B : Builtins) :
    ∀ (j : Nat) (r' : Rule), (relRules (simEnv B) "Step_read")[j]? = some r' → hasOptNil (ruleConcl r') = false := by
  intro j r' hr
  have hrr : relRules (simEnv B) "Step_read" = relRules (envOfScript Specs.wasm30) "Step_read" := by
    simp only [relRules, simEnv_findRel B]
  rw [hrr] at hr
  exact noOpt_read (List.mem_of_getElem? hr)

/-- A rule that fires under the new reading, at a conclusion without empty-domain options: its
body over `DDerivesB` (`Sim.fires_body` for `FiresB`). -/
theorem firesB_body {x : IL.Id} {i : Nat} {r : Rule} {v : Value}
    (hr : HasRuleAt env x "%~>%" i r) (hn : hasOptNil (ruleConcl r) = false)
    (hf : FiresB env x i v) :
    RuleBody env (DDerivesB env (otherwiseB env)) (otherwiseB env x [] i v) [] [] "%~>%" r v := by
  obtain ⟨t, rules, r', hrel, hi, hb⟩ := hf
  obtain ⟨ps, t', rules', hrel', -, hi'⟩ := hr
  have he : (([] : List Param), ("%~>%" : MixopS), t, rules) = (ps, "%~>%", t', rules') :=
    Option.some.inj (hrel.symm.trans hrel')
  obtain ⟨-, -, -, rfl⟩ : [] = ps ∧ "%~>%" = "%~>%" ∧ t = t' ∧ rules = rules' := by
    simpa only [Prod.mk.injEq] using he
  obtain rfl : r' = r := Option.some.inj (hi.symm.trans hi')
  exact ruleBody_of_ruleBodyB hn hb

/-- An earlier rule cannot fire on the left-hand side of a rule that uses `otherwise`, under the
new reading (`BwdPureStep.otherwise_false` for `otherwiseB`). -/
theorem otherwiseB_false {x : IL.Id} {k j : Nat} {r : Rule} {v w : Value}
    (ho : otherwiseB env x [] k v) (hj : j < k) (hr : HasRuleAt env x "%~>%" j r)
    (hs : SameLhs v w)
    (hb : RuleBodyB env (DDerivesB env noElse) (otherwiseAtB env x [] j w) [] [] "%~>%" r w) :
    False := by
  obtain ⟨ps, t, rules, hrel, rfl, hjr⟩ := hr
  have h : otherwiseAtB env x [] k v := ho
  rw [otherwiseAtB] at h
  exact h j hj [] "%~>%" t rules r hrel hjr w hs hb

/-! ## The cast rules -/

/-- `ref.test-true` (rule 65). -/
theorem sread_refTestTrueB (h : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) (hok : RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refTest rt)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) (adminsToV [constI32 1]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.TEST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K _ r).2 hok)))

/-- A `Ref_ok` premise of a cast rule that holds gives `RefOk`. -/
theorem refOk_of_premB (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {ρ : VarEnv} {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) {x : IL.Id} (hvo : ValsOnly ρ)
    (hs : EvalExp env ρ (.varE "s") (storeV hn s)) (hf : EvalExp env ρ (.varE "f") (frameV f))
    (hr : EvalExp env ρ (.varE "ref") (refToValue r))
    (ht : EvalExp env ρ (.varE x) (Encode.toValue rt))
    (hp : PremW env (DDerivesB env O) els ρ (.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s",
      .varE "ref", .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]]))) :
    RefOk s r (f.module.instRef rt) := by
  obtain ⟨w, he, hd⟩ := premW_rule hp
  have hw := EvalExp.unique he (evalExp_refOkArg G hvo hs hf hr ht)
  rw [hw] at hd
  exact (K O r).1 hd

/-- `ref.test-true` does not fire when the cast fails. -/
theorem not_refTestTrueB (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
    {c : Value} :
    ¬ RuleBodyB env (DDerivesB env O) els [] [] "%~>%" refTestTrueRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩, c]) := by
  intro hB
  obtain ⟨-, ρ₀, σ, hb, -, he, hp⟩ := ruleBody_of_ruleBodyB (by rfl) hB
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  exact hok (refOk_of_premB G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `ref.test-false` (rule 66). -/
theorem sread_refTestFalseB (h : HasRuleAt env "Step_read" "%~>%" 66 refTestFalseRule)
    (h₆₅ : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (hno : ∀ (j : Nat) (r' : Rule), (relRules env "Step_read")[j]? = some r' → hasOptNil (ruleConcl r') = false)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refTest rt)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) (adminsToV [constI32 0]) := by
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
  have hel := otherwiseB_of_ruleAt h hT (i := 66) (b := .list (adminsToV [constI32 0])) (by decide)
    (exc := [65]) ha (by decide) hno (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 65 := by simpa using hj
      rw [relRules_of_ruleAt h₆₅ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_refTestTrueB G K hok)
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (premsB_one (.elsePr hel))

/-- `ref.cast-succeed` (rule 67). -/
theorem sread_refCastSucceedB (h : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) (hok : RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refCast rt)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩) (adminsToV [.ref r]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.CAST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K _ r).2 hok)))

/-- `ref.cast-succeed` does not fire when the cast fails. -/
theorem not_refCastSucceedB (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
    {c : Value} :
    ¬ RuleBodyB env (DDerivesB env O) els [] [] "%~>%" refCastSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩, c]) := by
  intro hB
  obtain ⟨-, ρ₀, σ, hb, -, he, hp⟩ := ruleBody_of_ruleBodyB (by rfl) hB
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  exact hok (refOk_of_premB G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `ref.cast-fail` (rule 68). -/
theorem sread_refCastFailB (h : HasRuleAt env "Step_read" "%~>%" 68 refCastFailRule)
    (h₆₇ : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (hno : ∀ (j : Nat) (r' : Rule), (relRules env "Step_read")[j]? = some r' → hasOptNil (ruleConcl r') = false)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} (K : RefOkAtB env hn s (f.module.instRef rt)) (hok : ¬ RefOk s r (f.module.instRef rt))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refCast rt)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩) (adminsToV [.trap]) := by
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
  have hel := otherwiseB_of_ruleAt h hT (i := 68) (b := .list (adminsToV [.trap])) (by decide)
    (exc := [67]) ha (by decide) hno (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 67 := by simpa using hj
      rw [relRules_of_ruleAt h₆₇ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_refCastSucceedB G K hok)
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (premsB_one (.elsePr hel))

/-- `brOnCastSucceed` (rule 2). -/
theorem sread_brOnCastSucceedB (h : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAtB env hn s (f.module.instRef rt₂))
    (hok : RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCast l rt₁ rt₂)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩) (adminsToV [.ref r, .plain (.br l)]) := by
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
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ hq (by eval_tac)
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K _ r).2 hok)))

/-- `brOnCastSucceed` does not fire when the cast fails. -/
theorem not_brOnCastSucceedB (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAtB env hn s (f.module.instRef rt₂))
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) {c : Value} :
    ¬ RuleBodyB env (DDerivesB env O) els [] [] "%~>%" brOnCastSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩, c]) := by
  intro hB
  obtain ⟨-, ρ₀, σ, hb, -, he, hp⟩ := ruleBody_of_ruleBodyB (by rfl) hB
  obtain ⟨hs, hf, hr, ht⟩ := binds_brOnCast (lhs_of_concl he)
  exact hok (refOk_of_premB G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `brOnCastFail` (rule 3). -/
theorem sread_brOnCastFailB (h : HasRuleAt env "Step_read" "%~>%" 3 brOnCastFailRule)
    (h₀ : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (hno : ∀ (j : Nat) (r' : Rule), (relRules env "Step_read")[j]? = some r' → hasOptNil (ruleConcl r') = false)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAtB env hn s (f.module.instRef rt₂))
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCast l rt₁ rt₂)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩) (adminsToV [.ref r]) := by
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
  have hel := otherwiseB_of_ruleAt h hT (i := 3) (b := .list (adminsToV [.ref r])) (by decide)
    (exc := [2]) ha (by decide) hno (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 2 := by simpa using hj
      rw [relRules_of_ruleAt h₀ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_brOnCastSucceedB G K hok)
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ hq (by eval_tac) (premsB_one (.elsePr hel))

/-- `brOnCastFailSucceed` (rule 4). -/
theorem sread_brOnCastFailSucceedB (h : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAtB env hn s (f.module.instRef rt₂))
    (hok : RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩) (adminsToV [.ref r]) := by
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
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ hq (by eval_tac)
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_refOkArg G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) (by eval_tac) (by eval_tac))
      ((K _ r).2 hok)))

/-- `brOnCastFailSucceed` does not fire when the cast fails. -/
theorem not_brOnCastFailSucceedB (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAtB env hn s (f.module.instRef rt₂))
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) {c : Value} :
    ¬ RuleBodyB env (DDerivesB env O) els [] [] "%~>%" brOnCastFailSucceedRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩, c]) := by
  intro hB
  obtain ⟨-, ρ₀, σ, hb, -, he, hp⟩ := ruleBody_of_ruleBodyB (by rfl) hB
  obtain ⟨hs, hf, hr, ht⟩ := binds_brOnCast (lhs_of_concl he)
  exact hok (refOk_of_premB G K (valsOnly_scope hb) hs hf hr ht (hp _ (List.mem_singleton_self _)))

/-- `brOnCastFailFail` (rule 5). -/
theorem sread_brOnCastFailFailB (h : HasRuleAt env "Step_read" "%~>%" 5 brOnCastFailFailRule)
    (h₀ : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (hno : ∀ (j : Nat) (r' : Rule), (relRules env "Step_read")[j]? = some r' → hasOptNil (ruleConcl r') = false)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} (K : RefOkAtB env hn s (f.module.instRef rt₂))
    (hok : ¬ RefOk s r (f.module.instRef rt₂)) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]))) :
    SReadB env (configV hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩) (adminsToV [.ref r, .plain (.br l)]) := by
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
  have hel := otherwiseB_of_ruleAt h hT (i := 5) (b := .list (adminsToV [.ref r, .plain (.br l)])) (by decide)
    (exc := [4]) ha (by decide) hno (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 4 := by simpa using hj
      rw [relRules_of_ruleAt h₀ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_brOnCastFailSucceedB G K hok)
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) σ hq (by eval_tac) (premsB_one (.elsePr hel))

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
