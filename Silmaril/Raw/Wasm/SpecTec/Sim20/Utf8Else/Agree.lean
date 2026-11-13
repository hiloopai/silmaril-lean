module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseGood

/-!
# Away from `x₀`, `env₂` answers no more than `env₁` (unrefined)

`Utf8Mono.extMonoAt` shows that, for `EnvExt env₁ env₂ x₀`, `env₂` answers at least what `env₁` answers.
This file proves the converse on inputs that never reach `x₀` (`AgreeAt`): at every fuel, every
member of the evaluator answers in `env₁` at least what it answers in `env₂`, provided the syntax it
is given does not refer to the definition `x₀` (`GoodEvs x₀`), its scope binds no definition
variable to `x₀` (`DefsOk x₀`), its evaluated definition arguments are not `x₀` (`ArgOk x₀`), and
`env₁` itself never refers to `x₀` outside `x₀`'s clauses (`Clean env₁ x₀`).

The proof is round 7's `Round7.Script.agreeAt_succ` (`Raw/…/Round7/Script/Agree.lean`) with the
two environments abstracted and "reachable, not `$utf8`" replaced by "not `x₀`". `callDef` is a
congruence: the called name is not `x₀`, so both environments find the same clauses
(`EnvExt.defs`) and primitives (`EnvExt.call`), and those clauses are `GoodEvs x₀` (`Clean.defs`).
Every relation is `Clean.rels`, so `derives` needs no reachability hypothesis. Kept unrefined,
like its model.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evExp evExps evOExp evEFields evPath evIterExp evIter
  evDoms evArg evArgs evPrem evPrems evClause evRule defsPres bind_le_of mapM_le_of foldlM_le_of
  elimUndef_le_of)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (EnvExt)

/-- Unfold the events of a term into the conjunction of `GoodEvs` of its parts. -/
syntax "gsimp20 " ident : tactic
macro_rules
  | `(tactic| gsimp20 $h) => `(tactic| simp only [evExp, evExps, evOExp, evEFields, evPath,
      evIterExp, evIter, evDoms, evArg, evArgs, evPrem, evPrems, evClause, evRule, goodEvs_append,
      goodEvs_cons, goodEvs_nil, goodEv_atom, goodEv_comp, goodEv_upd, goodEv_ref0, goodEv_ref1,
      true_and, and_true, and_assoc] at $h:ident)

/-- **Reverse environment monotonicity at fuel `n`**, on inputs that never reach `x₀`: every
member of the evaluator answers in `env₁` at least what it answers in `env₂`. -/
structure AgreeAt (env₁ env₂ : Env) (x₀ : String) (n : Nat) : Prop where
  exp : ∀ ρ e, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    evalExp n env₂ ρ e ⊑ evalExp n env₁ ρ e
  exps : ∀ ρ es, DefsOk x₀ ρ → (∀ e ∈ es, GoodEvs x₀ (evExp e)) →
    evalExps n env₂ ρ es ⊑ evalExps n env₁ ρ es
  expFields : ∀ ρ fs, DefsOk x₀ ρ → GoodEvs x₀ (evEFields fs) →
    evalExpFields n env₂ ρ fs ⊑ evalExpFields n env₁ ρ fs
  arg : ∀ ρ a, DefsOk x₀ ρ → GoodEvs x₀ (evArg a) →
    evalArg n env₂ ρ a ⊑ evalArg n env₁ ρ a
  args : ∀ ρ ags, DefsOk x₀ ρ → GoodEvs x₀ (evArgs ags) →
    evalArgs n env₂ ρ ags ⊑ evalArgs n env₁ ρ ags
  doms : ∀ ρ ds, DefsOk x₀ ρ → GoodEvs x₀ (evDoms ds) →
    evalDoms n env₂ ρ ds ⊑ evalDoms n env₁ ρ ds
  iterE : ∀ ρ e it ds, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) → GoodEvs x₀ (evIter it) →
    GoodEvs x₀ (evDoms ds) → evalIterE n env₂ ρ e it ds ⊑ evalIterE n env₁ ρ e it ds
  iterList : ∀ ρ e xvs ido k, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    evalIterList n env₂ ρ e xvs ido k ⊑ evalIterList n env₁ ρ e xvs ido k
  rounds : ∀ ρ e rs, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    evalRounds n env₂ ρ e rs ⊑ evalRounds n env₁ ρ e rs
  pathGet : ∀ ρ v p, DefsOk x₀ ρ → GoodEvs x₀ (evPath p) →
    pathGet n env₂ ρ v p ⊑ pathGet n env₁ ρ v p
  pathSet : ∀ ρ v p w, DefsOk x₀ ρ → GoodEvs x₀ (evPath p) →
    pathSet n env₂ ρ v p w ⊑ pathSet n env₁ ρ v p w
  patLen : ∀ ρ e, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    patLen n env₂ ρ e ⊑ patLen n env₁ ρ e
  matchExp : ∀ ρ e v, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    matchExp n env₂ ρ e v ⊑ matchExp n env₁ ρ e v
  matchDefault : ∀ ρ e v, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    matchDefault n env₂ ρ e v ⊑ matchDefault n env₁ ρ e v
  matchExps : ∀ ρ es vs, DefsOk x₀ ρ → (∀ e ∈ es, GoodEvs x₀ (evExp e)) →
    matchExps n env₂ ρ es vs ⊑ matchExps n env₁ ρ es vs
  matchExpFields : ∀ ρ fs gs, DefsOk x₀ ρ → GoodEvs x₀ (evEFields fs) →
    matchExpFields n env₂ ρ fs gs ⊑ matchExpFields n env₁ ρ fs gs
  matchIterE : ∀ ρ e it ds v, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) → GoodEvs x₀ (evIter it) →
    GoodEvs x₀ (evDoms ds) → matchIterE n env₂ ρ e it ds v ⊑ matchIterE n env₁ ρ e it ds v
  matchIterList : ∀ ρ e ds ido vs, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) → GoodEvs x₀ (evDoms ds) →
    matchIterList n env₂ ρ e ds ido vs ⊑ matchIterList n env₁ ρ e ds ido vs
  matchRounds : ∀ ρ e xs ido i vs, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) →
    matchRounds n env₂ ρ e xs ido i vs ⊑ matchRounds n env₁ ρ e xs ido i vs
  matchArg : ∀ ρ a w, DefsOk x₀ ρ → GoodEvs x₀ (evArg a) →
    matchArg n env₂ ρ a w ⊑ matchArg n env₁ ρ a w
  matchArgs : ∀ ρ ags ws, DefsOk x₀ ρ → GoodEvs x₀ (evArgs ags) → (∀ w ∈ ws, ArgOk x₀ w) →
    matchArgs n env₂ ρ ags ws ⊑ matchArgs n env₁ ρ ags ws
  callDef : ∀ ρ x ags, DefsOk x₀ ρ → x ≠ x₀ → GoodEvs x₀ (evArgs ags) →
    callDef n env₂ ρ x ags ⊑ callDef n env₁ ρ x ags
  tryClauses : ∀ cs ws, (∀ c ∈ cs, GoodEvs x₀ (evClause c)) → (∀ w ∈ ws, ArgOk x₀ w) →
    tryClauses n env₂ cs ws ⊑ tryClauses n env₁ cs ws
  premHolds : ∀ ρ pr, DefsOk x₀ ρ → GoodEvs x₀ (evPrem pr) →
    premHolds n env₂ ρ pr ⊑ premHolds n env₁ ρ pr
  premsHold : ∀ ρ prs, DefsOk x₀ ρ → GoodEvs x₀ (evPrems prs) →
    premsHold n env₂ ρ prs ⊑ premsHold n env₁ ρ prs
  premIter : ∀ ρ pr it ds, DefsOk x₀ ρ → GoodEvs x₀ (evPrem pr) → GoodEvs x₀ (evIter it) →
    GoodEvs x₀ (evDoms ds) → premIter n env₂ ρ pr it ds ⊑ premIter n env₁ ρ pr it ds
  premRounds : ∀ ρ pr xvs ido k, DefsOk x₀ ρ → GoodEvs x₀ (evPrem pr) →
    premRounds n env₂ ρ pr xvs ido k ⊑ premRounds n env₁ ρ pr xvs ido k
  derives : ∀ x op ags v, (∀ w ∈ ags, ArgOk x₀ w) →
    derives n env₂ x op ags v = true → derives n env₁ x op ags v = true
  anyRule : ∀ op ps ags v rs, (∀ r ∈ rs, GoodEvs x₀ (evRule r)) → (∀ w ∈ ags, ArgOk x₀ w) →
    anyRule n env₂ op ps ags v rs = true → anyRule n env₁ op ps ags v rs = true

variable {env₁ env₂ : Env} {x₀ : String}

theorem agreeAt_zero : AgreeAt env₁ env₂ x₀ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intros; simp only [evalExp, evalExps, evalExpFields, evalArg, evalArgs, evalDoms,
        evalIterE, evalIterList, evalRounds, Sem.pathGet, Sem.pathSet, Sem.patLen, Sem.matchExp,
        Sem.matchDefault, Sem.matchExps, Sem.matchExpFields, Sem.matchIterE, Sem.matchIterList,
        Sem.matchRounds, Sem.matchArg, Sem.matchArgs, Sem.callDef, Sem.tryClauses, Sem.premHolds,
        Sem.premsHold, Sem.premIter, Sem.premRounds]; exact Res.oof_le _)
    | (intro _ _ _ _ _ h; simp [Sem.derives] at h)
    | (intro _ _ _ _ _ _ _ h; simp [Sem.anyRule] at h)

theorem agreeAt_succ (hS : EnvExt env₁ env₂ x₀) (hC : Clean env₁ x₀) (m : Nat)
    (ih : AgreeAt env₁ env₂ x₀ m) : AgreeAt env₁ env₂ x₀ (m + 1) := by
  have hexp := ih.exp
  have hexps := ih.exps
  have hefs := ih.expFields
  have harg := ih.arg
  have hargs := ih.args
  have hdoms := ih.doms
  have hit := ih.iterE
  have hitl := ih.iterList
  have hrnd := ih.rounds
  have hpg := ih.pathGet
  have hps := ih.pathSet
  have hpl := ih.patLen
  have hm := ih.matchExp
  have hmd := ih.matchDefault
  have hms := ih.matchExps
  have hmf := ih.matchExpFields
  have hmi := ih.matchIterE
  have hmil := ih.matchIterList
  have hmr := ih.matchRounds
  have hma := ih.matchArg
  have hmas := ih.matchArgs
  have hcd := ih.callDef
  have htc := ih.tryClauses
  have hph := ih.premHolds
  have hphs := ih.premsHold
  have hpi := ih.premIter
  have hpr := ih.premRounds
  have DP := defsPres env₂ m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `evalExp`
  · intro ρ e hD hG
    cases e with
    | varE x => simp only [evalExp]; exact Res.Le.refl _
    | boolE b => simp only [evalExp]; exact Res.Le.refl _
    | numE n => simp only [evalExp]; exact Res.Le.refl _
    | textE t => simp only [evalExp]; exact Res.Le.refl _
    | unE op t e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | binE op t e₁ e₂ =>
        gsimp20 hG
        simp only [evalExp]
        refine Res.bind_le (hexp _ _ hD hG.1) fun v₁ => ?_
        cases boolShort op v₁ with
        | none => exact Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
        | some v => exact Res.Le.refl _
    | cmpE op t e₁ e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | tupE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _ hD (goodEvs_exps hG))
    | projE e i =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | caseE op e => simp only [evalExp]; exact Res.map_le _ (hexp _ _ hD hG)
    | uncaseE e op =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | optE eo =>
        cases eo with
        | none => simp only [evalExp]; exact Res.Le.refl _
        | some e => simp only [evalExp]; exact Res.map_le _ (hexp _ _ hD hG)
    | theE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | strE fs => simp only [evalExp]; exact Res.map_le _ (hefs _ _ hD hG)
    | dotE e a =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | compE e₁ e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | listE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _ hD (goodEvs_exps hG))
    | liftE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | memE e₁ e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | lenE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | catE e₁ e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | idxE e₁ e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | sliceE e₁ e₂ e₃ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ => Res.Le.refl _
    | updE e₁ p e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun _ => hps _ _ _ _ hD hG.2.1
    | extE e₁ p e₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun _ =>
            Res.bind_le (hpg _ _ _ hD hG.2.1) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.2.1
    | callE x args₀ =>
        gsimp20 hG
        simp only [evalExp]
        exact hcd _ _ _ hD hG.1 hG.2
    | iterE e₀ it =>
        cases it with
        | mk i ds =>
          gsimp20 hG
          simp only [evalExp]
          exact hit _ _ _ _ hD hG.1 hG.2.1 hG.2.2
    | cvtE e t₁ t₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | subE e t₁ t₂ =>
        gsimp20 hG
        simp only [evalExp]
        exact hexp _ _ hD hG.1
  -- `evalExps`
  · intro ρ es hD hG
    simp only [evalExps]
    exact mapM_le_of es fun e he => hexp _ _ hD (hG e he)
  -- `evalExpFields`
  · intro ρ fs hD hG
    simp only [evalExpFields]
    refine mapM_le_of fs fun f hf => ?_
    cases f with
    | mk a e => exact Res.map_le _ (hexp _ _ hD (goodEvs_fields hG a e hf))
  -- `evalArg`
  · intro ρ a hD hG
    cases a <;> simp only [evalArg]
    case expA e => exact Res.map_le _ (hexp _ _ hD hG)
    all_goals exact Res.Le.refl _
  -- `evalArgs`
  · intro ρ args₀ hD hG
    simp only [evalArgs]
    exact mapM_le_of args₀ fun a ha => harg _ _ hD (goodEvs_args hG a ha)
  -- `evalDoms`
  · intro ρ ds hD hG
    simp only [evalDoms]
    exact mapM_le_of ds fun d hd => Res.map_le _ (hexp _ _ hD (goodEvs_doms' hG d hd))
  -- `evalIterE`
  · intro ρ e it ds hD hGe hGit hGds
    cases it with
    | opt =>
        simp only [evalIterE]
        refine Res.bind_le (hdoms _ _ hD hGds) fun xvs => Res.assert_le ?_
        refine Res.bind_le (Res.Le.refl _) fun os => ?_
        split
        · exact Res.Le.refl _
        · split
          · exact Res.bind_le (hexp _ _ (defsOk_bindVals hD _) hGe) fun _ => Res.Le.refl _
          · exact Res.Le.refl _
    | list =>
        simp only [evalIterE]
        exact Res.bind_le (hdoms _ _ hD hGds) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hitl _ _ _ _ _ hD hGe)
    | list1 =>
        simp only [evalIterE]
        exact Res.bind_le (hdoms _ _ hD hGds) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ =>
            Res.assert_le (hitl _ _ _ _ _ hD hGe))
    | listN eₙ x =>
        gsimp20 hGit
        simp only [evalIterE]
        exact Res.bind_le (hdoms _ _ hD hGds) fun _ =>
          Res.bind_le (hexp _ _ hD hGit) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ => hitl _ _ _ _ _ hD hGe
  -- `evalIterList`
  · intro ρ e xvs ido k hD hGe
    simp only [evalIterList]
    exact Res.bind_le (Res.Le.refl _) fun _ =>
      Res.assert_le (Res.bind_le (hrnd _ _ _ hD hGe) fun _ => Res.Le.refl _)
  -- `evalRounds`
  · intro ρ e rs hD hGe
    simp only [evalRounds]
    exact Res.mapM_le (fun r => hexp _ _ (defsOk_bindVals hD r) hGe) rs
  -- `pathGet`
  · intro ρ v p hD hG
    cases p with
    | rootP => simp only [Sem.pathGet]; exact Res.Le.refl _
    | idxP p e =>
        gsimp20 hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | sliceP p e₁ e₂ =>
        gsimp20 hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ => Res.Le.refl _
    | dotP p a =>
        gsimp20 hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG) fun _ => Res.Le.refl _
  -- `pathSet`
  · intro ρ v p w hD hG
    cases p with
    | rootP => simp only [Sem.pathSet]; exact Res.Le.refl _
    | idxP p e =>
        gsimp20 hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.1
    | sliceP p e₁ e₂ =>
        gsimp20 hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.1
    | dotP p a =>
        gsimp20 hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG) fun _ =>
          Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG
  -- `patLen`
  · intro ρ e hD hG
    cases e
    case listE es => simp only [Sem.patLen]; exact Res.Le.refl _
    case catE e₁ e₂ =>
      gsimp20 hG
      simp only [Sem.patLen]
      exact Res.bind_le (hpl _ _ hD hG.1) fun _ =>
        Res.bind_le (hpl _ _ hD hG.2) fun _ => Res.Le.refl _
    case iterE e₀ it =>
      cases it with
      | mk i ds =>
          cases i
          case listN eₙ x =>
            gsimp20 hG
            simp only [Sem.patLen]
            exact Res.bind_le (hexp _ _ hD hG.2.1) fun _ => Res.Le.refl _
          all_goals
            simp only [Sem.patLen]
            exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    case optE eo =>
      cases eo <;> simp only [Sem.patLen] <;>
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    all_goals
      simp only [Sem.patLen]
      exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
  -- `matchExp`
  · intro ρ e v hD hG
    cases e
    case varE x => simp only [Sem.matchExp]; exact Res.Le.refl _
    case boolE b => simp only [Sem.matchExp]; exact Res.Le.refl _
    case numE n => simp only [Sem.matchExp]; exact Res.Le.refl _
    case textE t => simp only [Sem.matchExp]; exact Res.Le.refl _
    case unE op t e =>
      cases op <;> cases v <;> simp only [Sem.matchExp] <;>
        first
          | exact hmd _ _ _ hD hG
          | exact Res.assert_le (hm _ _ _ hD hG)
          | exact Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ hD hG)
    case tupE es =>
      simp only [Sem.matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _ hD (goodEvs_exps hG)
    case projE e i =>
      simp only [Sem.matchExp]
      split
      · exact hm _ _ _ hD hG
      · exact hmd _ _ _ hD hG
    case caseE op e =>
      simp only [Sem.matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => Res.assert_le (hm _ _ _ hD hG)
    case uncaseE e op => simp only [Sem.matchExp]; exact hm _ _ _ hD hG
    case optE eo =>
      cases eo with
      | none => simp only [Sem.matchExp]; exact Res.Le.refl _
      | some e =>
        simp only [Sem.matchExp]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ hD hG
    case strE fs =>
      simp only [Sem.matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => hmf _ _ _ hD hG
    case listE es =>
      simp only [Sem.matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _ hD (goodEvs_exps hG)
    case catE e₁ e₂ =>
      gsimp20 hG
      simp only [Sem.matchExp]
      have hpair : ∀ a b, (Sem.matchExp m env₂ ρ e₁ a >>= fun ρ' =>
          Sem.matchExp m env₂ ρ' e₂ b) ⊑
          (Sem.matchExp m env₁ ρ e₁ a >>= fun ρ' => Sem.matchExp m env₁ ρ' e₂ b) :=
        fun a b => bind_le_of (hm _ _ _ hD hG.1) fun ρ' hρ' =>
          hm _ _ _ (defsOk_of_defs hD (DP.matchExp _ _ _ _ hρ')) hG.2
      refine Res.bind_le (Res.Le.refl _) fun vs => ?_
      refine Res.elimUndef_le (hpl _ _ hD hG.1) (fun k => ?_) (fun _ => ?_)
      · exact Res.assert_le (hpair _ _)
      · refine Res.elimUndef_le (hpl _ _ hD hG.2) (fun k => ?_) (fun _ => ?_)
        · exact Res.assert_le (hpair _ _)
        · exact Res.scan_le (fun _ => hpair _ _) _ _
    case iterE e₀ it =>
      cases it with
      | mk i ds =>
        gsimp20 hG
        simp only [Sem.matchExp]
        exact hmi _ _ _ _ _ hD hG.1 hG.2.1 hG.2.2
    case cvtE e t₁ t₂ =>
      cases v <;> simp only [Sem.matchExp] <;>
        first
          | exact hmd _ _ _ hD hG
          | exact Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ hD hG
    case subE e t₁ t₂ =>
      gsimp20 hG
      simp only [Sem.matchExp]
      exact hm _ _ _ hD hG.1
    all_goals (simp only [Sem.matchExp]; exact hmd _ _ _ hD hG)
  -- `matchDefault`
  · intro ρ e v hD hG
    simp only [Sem.matchDefault]
    exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
  -- `matchExps`
  · intro ρ es vs hD hG
    cases es with
    | nil => cases vs <;> simp only [Sem.matchExps] <;> exact Res.Le.refl _
    | cons e es =>
        cases vs with
        | nil => simp only [Sem.matchExps]; exact Res.Le.refl _
        | cons v vs =>
            simp only [Sem.matchExps]
            exact bind_le_of (hm _ _ _ hD (hG e List.mem_cons_self)) fun ρ' hρ' =>
              hms _ _ _ (defsOk_of_defs hD (DP.matchExp _ _ _ _ hρ'))
                fun e' he' => hG e' (List.mem_cons_of_mem _ he')
  -- `matchExpFields`
  · intro ρ fs gs hD hG
    cases fs with
    | nil => cases gs <;> simp only [Sem.matchExpFields] <;> exact Res.Le.refl _
    | cons f fs =>
        cases f with
        | mk a e =>
            gsimp20 hG
            cases gs with
            | nil => simp only [Sem.matchExpFields]; exact Res.Le.refl _
            | cons g gs =>
                simp only [Sem.matchExpFields]
                exact Res.assert_le (bind_le_of (hm _ _ _ hD hG.1) fun ρ' hρ' =>
                  hmf _ _ _ (defsOk_of_defs hD (DP.matchExp _ _ _ _ hρ')) hG.2)
  -- `matchIterE`
  · intro ρ e it ds v hD hGe hGit hGds
    cases it with
    | opt =>
        simp only [Sem.matchIterE]
        refine Res.bind_le (Res.Le.refl _) fun o => ?_
        cases o with
        | none => exact hms _ _ _ hD (goodEvs_doms hGds)
        | some w =>
            exact Res.bind_le (hm _ _ _ hD hGe) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _ hD (goodEvs_doms hGds)
    | list =>
        simp only [Sem.matchIterE]
        exact Res.bind_le (Res.Le.refl _) fun _ => hmil _ _ _ _ _ hD hGe hGds
    | list1 =>
        simp only [Sem.matchIterE]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          Res.assert_le (hmil _ _ _ _ _ hD hGe hGds)
    | listN eₙ x =>
        gsimp20 hGit
        simp only [Sem.matchIterE]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          bind_le_of (hm _ _ _ hD hGit) fun ρ₀ h₀ =>
            hmil _ _ _ _ _ (defsOk_of_defs hD (DP.matchExp _ _ _ _ h₀)) hGe hGds
  -- `matchIterList`
  · intro ρ e ds ido vs hD hGe hGds
    simp only [Sem.matchIterList]
    exact Res.bind_le (hmr _ _ _ _ _ _ hD hGe) fun _ => hms _ _ _ hD (goodEvs_doms hGds)
  -- `matchRounds`
  · intro ρ e xs ido i vs hD hGe
    cases vs with
    | nil => simp only [Sem.matchRounds]; exact Res.Le.refl _
    | cons v vs =>
        cases ido with
        | none =>
          simp only [Sem.matchRounds]
          exact Res.bind_le (hm _ _ _ hD hGe) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (hmr _ _ _ _ _ _ hD hGe) fun _ => Res.Le.refl _
        | some y =>
          simp only [Sem.matchRounds]
          exact Res.bind_le (hm _ _ _ (defsOk_bindVal hD _ _) hGe) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (hmr _ _ _ _ _ _ hD hGe) fun _ => Res.Le.refl _
  -- `matchArg`
  · intro ρ a w hD hG
    cases a <;> cases w <;> simp only [Sem.matchArg, hS.sub,
      hS.typV, hS.symV] <;>
      first
        | with_reducible exact Res.Le.refl _
        | (split
           · exact hm _ _ _ hD hG
           · exact Res.Le.refl _)
  -- `matchArgs`
  · intro ρ args₀ ws hD hG hW
    cases args₀ with
    | nil => cases ws <;> simp only [Sem.matchArgs] <;> exact Res.Le.refl _
    | cons a args₀ =>
        gsimp20 hG
        cases ws with
        | nil => simp only [Sem.matchArgs]; exact Res.Le.refl _
        | cons w ws =>
            simp only [Sem.matchArgs]
            exact bind_le_of (hma _ _ _ hD hG.1) fun ρ' hρ' =>
              hmas _ _ _ (matchArg_defsOk hD (hW w List.mem_cons_self) hρ') hG.2
                fun w' hw' => hW w' (List.mem_cons_of_mem _ hw')
  -- `callDef`: a congruence, since the called name is not `$utf8`
  · intro ρ x args₀ hD hx hG
    simp only [Sem.callDef]
    refine bind_le_of (hargs _ _ hD hG) fun argVs hav => ?_
    have hx' := goodName_resolve hD hx
    rw [hS.defs _ hx', hS.call _ hx']
    refine bind_le_of (Res.Le.refl _) fun d hd => ?_
    have hcl := hC.defs _ _ hx' (Res.ofOption_eq_ok.1 hd)
    exact Res.elimUndef_le (htc _ _ hcl (evalArgs_argOk hD hG hav)) (fun _ => Res.Le.refl _)
      (fun _ => Res.Le.refl _)
  -- `tryClauses`
  · intro cs ws hcs hW
    cases cs with
    | nil => simp only [Sem.tryClauses]; exact Res.Le.refl _
    | cons c cs =>
        cases c with
        | defD q pats e prems =>
            have hc := hcs _ List.mem_cons_self
            gsimp20 hc
            simp only [Sem.tryClauses]
            refine elimUndef_le_of
              (bind_le_of (hmas _ _ _ defsOk_empty hc.2.1 hW) fun ρ₀ h₀ =>
                hphs _ _ (matchArgs_defsOk m defsOk_empty hW h₀) hc.2.2.2)
              (fun ρ₁ h₁ => ?_) (fun _ => htc _ _ (fun c hc' => hcs c (List.mem_cons_of_mem _ hc')) hW)
            obtain ⟨ρ₀, h₀, h₁'⟩ := Res.bind_eq_ok.1 h₁
            exact hexp _ _ (defsOk_of_defs (matchArgs_defsOk m defsOk_empty hW h₀)
              (DP.premsHold _ _ _ h₁')) hc.2.2.1
  -- `premHolds`
  · intro ρ pr hD hG
    cases pr with
    | ifPr e =>
        simp only [Sem.premHolds]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | elsePr => simp only [Sem.premHolds]; exact Res.Le.refl _
    | letPr e₁ e₂ =>
        gsimp20 hG
        simp only [Sem.premHolds]
        exact Res.bind_le (hexp _ _ hD hG.2) fun _ => hm _ _ _ hD hG.1
    | rulePr x args₀ op e =>
        gsimp20 hG
        simp only [Sem.premHolds]
        refine bind_le_of (hargs _ _ hD hG.1) fun avs havs =>
          Res.bind_le (hexp _ _ hD hG.2) fun v => ?_
        cases hd : Sem.derives m env₂ x op avs v with
        | true =>
          rw [ih.derives _ _ _ _ (evalArgs_argOk hD hG.1 havs) hd]
        | false => exact Or.inl (by simp)
    | iterPr pr it =>
        cases it with
        | mk i ds =>
          gsimp20 hG
          simp only [Sem.premHolds]
          exact hpi _ _ _ _ hD hG.1 hG.2.1 hG.2.2
  -- `premsHold`
  · intro ρ prs hD hG
    simp only [Sem.premsHold]
    exact foldlM_le_of (P := DefsOk x₀) prs
      (fun b a hb ha => hph _ _ hb (goodEvs_prems hG a ha))
      (fun b a b' hb _ hok => defsOk_of_defs hb (DP.premHolds _ _ _ hok)) ρ hD
  -- `premIter`
  · intro ρ pr it ds hD hGpr hGit hGds
    cases it with
    | opt =>
        simp only [Sem.premIter]
        refine Res.bind_le (hdoms _ _ hD hGds) fun xvs => Res.assert_le ?_
        refine Res.bind_le (Res.Le.refl _) fun os => ?_
        split
        · exact Res.Le.refl _
        · split
          · exact Res.bind_le (hph _ _ (defsOk_bindVals hD _) hGpr) fun _ => Res.Le.refl _
          · exact Res.Le.refl _
    | list =>
        simp only [Sem.premIter]
        exact Res.bind_le (hdoms _ _ hD hGds) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hpr _ _ _ _ _ hD hGpr)
    | list1 =>
        simp only [Sem.premIter]
        exact Res.bind_le (hdoms _ _ hD hGds) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ =>
            Res.assert_le (hpr _ _ _ _ _ hD hGpr))
    | listN eₙ x =>
        gsimp20 hGit
        simp only [Sem.premIter]
        exact Res.bind_le (hdoms _ _ hD hGds) fun _ =>
          Res.bind_le (hexp _ _ hD hGit) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ => hpr _ _ _ _ _ hD hGpr
  -- `premRounds`
  · intro ρ pr xvs ido k hD hGpr
    simp only [Sem.premRounds]
    exact Res.bind_le (Res.Le.refl _) fun _ =>
      Res.assert_le (Res.bind_le (Res.mapM_le (fun r => hph _ _ (defsOk_bindVals hD r) hGpr) _)
        fun _ => Res.Le.refl _)
  -- `derives`
  · intro x op args₀ v hW h
    simp only [Sem.derives] at h ⊢
    rw [hS.rels] at h
    cases hr : env₁.findRel? x with
    | none => rw [hr] at h; simp at h
    | some d =>
        obtain ⟨ps, op', t, rules⟩ := d
        rw [hr] at h
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, ih.anyRule _ _ _ _ _ (hC.rels _ _ hr) hW h.2⟩
  -- `anyRule`
  · intro op ps args₀ v rs hrs hW h
    cases rs with
    | nil => simp only [Sem.anyRule] at h; exact absurd h (by simp)
    | cons r rs =>
        cases r with
        | ruleD y qs op' e prems =>
            have hr := hrs _ List.mem_cons_self
            gsimp20 hr
            simp only [Sem.anyRule, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
            rcases h with ⟨hop, hb⟩ | hrest
            · refine Or.inl ⟨hop, ?_⟩
              refine Res.isOk_le ?_ hb
              exact bind_le_of (Res.Le.refl _) fun ρ₀ h₀ => by
                have hD₀ := bindParams_defsOk defsOk_empty hW (Res.ofOption_eq_ok.1 h₀)
                exact bind_le_of (hm _ _ _ hD₀ hr.2.1) fun ρ₁ h₁ =>
                  hphs _ _ (defsOk_of_defs hD₀ (DP.matchExp _ _ _ _ h₁)) hr.2.2
            · exact Or.inr (ih.anyRule _ _ _ _ _ (fun r hr' => hrs r (List.mem_cons_of_mem _ hr'))
                hW hrest)

/-- **Reverse environment monotonicity**, at every fuel. -/
theorem agreeAt (hS : EnvExt env₁ env₂ x₀) (hC : Clean env₁ x₀) :
    ∀ n, AgreeAt env₁ env₂ x₀ n
  | 0 => agreeAt_zero
  | n + 1 => agreeAt_succ hS hC n (agreeAt hS hC n)

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
