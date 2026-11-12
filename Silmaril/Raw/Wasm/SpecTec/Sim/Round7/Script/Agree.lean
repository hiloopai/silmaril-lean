module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Good
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Utf8.Mono

/-!
# Round 7: away from `$utf8`, `utf8Env B` answers no more than `simEnv B` (unrefined)

`Round7.envMonoAt` shows that `utf8Env B` answers at least what `simEnv B` answers. This file
proves the converse on well-behaved inputs (`AgreeAt`): at every fuel, every member of the
evaluator answers in `simEnv B` at least what it answers in `utf8Env B`, provided the syntax it
is given only refers to reachable definitions other than `$utf8` and reachable relations
(`GoodEvs`), its scope binds definition variables only to such definitions (`DefsOk`), and its
evaluated definition arguments are such definitions (`ArgOk`).

The proof is `Round7.envMonoAt_succ` with the two environments exchanged and these invariants
threaded through. `callDef` is now a congruence too: the called name is `GoodName`, so it is not
`$utf8`, and the clauses `simEnv B` finds for it are `GoodEvs` by the kernel-checked closure
facts (`findDef?_reach`, `goodEvs_of_reach`). Scopes returned by matching keep their definition
variables (`defsPres`); argument matching and relation parameters bind only `ArgOk` names
(`matchArgs_defsOk`, `bindParams_defsOk`). Kept unrefined, like `Round7/Utf8/Mono.lean`; the
equalities it gives are in `Proofs/…/Round7/Script/AgreeEq.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res

variable (B : Builtins)

/-- Unfold the events of a term into the conjunction of `GoodEvs` of its parts. -/
syntax "gsimp " ident : tactic
macro_rules
  | `(tactic| gsimp $h) => `(tactic| simp only [evExp, evExps, evOExp, evEFields, evPath,
      evIterExp, evIter, evDoms, evArg, evArgs, evPrem, evPrems, evClause, evRule, goodEvs_append,
      goodEvs_cons, goodEvs_nil, goodEv_atom, goodEv_comp, goodEv_upd, goodEv_ref0, goodEv_ref1,
      true_and, and_true, and_assoc] at $h:ident)

/-- **Reverse environment monotonicity at fuel `n`**, on well-behaved inputs: every member of the
evaluator answers in `simEnv B` at least what it answers in `utf8Env B`. -/
structure AgreeAt (n : Nat) : Prop where
  exp : ∀ ρ e, DefsOk ρ → GoodEvs (evExp e) →
    evalExp n (utf8Env B) ρ e ⊑ evalExp n (simEnv B) ρ e
  exps : ∀ ρ es, DefsOk ρ → (∀ e ∈ es, GoodEvs (evExp e)) →
    evalExps n (utf8Env B) ρ es ⊑ evalExps n (simEnv B) ρ es
  expFields : ∀ ρ fs, DefsOk ρ → GoodEvs (evEFields fs) →
    evalExpFields n (utf8Env B) ρ fs ⊑ evalExpFields n (simEnv B) ρ fs
  arg : ∀ ρ a, DefsOk ρ → GoodEvs (evArg a) →
    evalArg n (utf8Env B) ρ a ⊑ evalArg n (simEnv B) ρ a
  args : ∀ ρ ags, DefsOk ρ → GoodEvs (evArgs ags) →
    evalArgs n (utf8Env B) ρ ags ⊑ evalArgs n (simEnv B) ρ ags
  doms : ∀ ρ ds, DefsOk ρ → GoodEvs (evDoms ds) →
    evalDoms n (utf8Env B) ρ ds ⊑ evalDoms n (simEnv B) ρ ds
  iterE : ∀ ρ e it ds, DefsOk ρ → GoodEvs (evExp e) → GoodEvs (evIter it) → GoodEvs (evDoms ds) →
    evalIterE n (utf8Env B) ρ e it ds ⊑ evalIterE n (simEnv B) ρ e it ds
  iterList : ∀ ρ e xvs ido k, DefsOk ρ → GoodEvs (evExp e) →
    evalIterList n (utf8Env B) ρ e xvs ido k ⊑ evalIterList n (simEnv B) ρ e xvs ido k
  rounds : ∀ ρ e rs, DefsOk ρ → GoodEvs (evExp e) →
    evalRounds n (utf8Env B) ρ e rs ⊑ evalRounds n (simEnv B) ρ e rs
  pathGet : ∀ ρ v p, DefsOk ρ → GoodEvs (evPath p) →
    pathGet n (utf8Env B) ρ v p ⊑ pathGet n (simEnv B) ρ v p
  pathSet : ∀ ρ v p w, DefsOk ρ → GoodEvs (evPath p) →
    pathSet n (utf8Env B) ρ v p w ⊑ pathSet n (simEnv B) ρ v p w
  patLen : ∀ ρ e, DefsOk ρ → GoodEvs (evExp e) →
    patLen n (utf8Env B) ρ e ⊑ patLen n (simEnv B) ρ e
  matchExp : ∀ ρ e v, DefsOk ρ → GoodEvs (evExp e) →
    matchExp n (utf8Env B) ρ e v ⊑ matchExp n (simEnv B) ρ e v
  matchDefault : ∀ ρ e v, DefsOk ρ → GoodEvs (evExp e) →
    matchDefault n (utf8Env B) ρ e v ⊑ matchDefault n (simEnv B) ρ e v
  matchExps : ∀ ρ es vs, DefsOk ρ → (∀ e ∈ es, GoodEvs (evExp e)) →
    matchExps n (utf8Env B) ρ es vs ⊑ matchExps n (simEnv B) ρ es vs
  matchExpFields : ∀ ρ fs gs, DefsOk ρ → GoodEvs (evEFields fs) →
    matchExpFields n (utf8Env B) ρ fs gs ⊑ matchExpFields n (simEnv B) ρ fs gs
  matchIterE : ∀ ρ e it ds v, DefsOk ρ → GoodEvs (evExp e) → GoodEvs (evIter it) →
    GoodEvs (evDoms ds) → matchIterE n (utf8Env B) ρ e it ds v ⊑ matchIterE n (simEnv B) ρ e it ds v
  matchIterList : ∀ ρ e ds ido vs, DefsOk ρ → GoodEvs (evExp e) → GoodEvs (evDoms ds) →
    matchIterList n (utf8Env B) ρ e ds ido vs ⊑ matchIterList n (simEnv B) ρ e ds ido vs
  matchRounds : ∀ ρ e xs ido i vs, DefsOk ρ → GoodEvs (evExp e) →
    matchRounds n (utf8Env B) ρ e xs ido i vs ⊑ matchRounds n (simEnv B) ρ e xs ido i vs
  matchArg : ∀ ρ a w, DefsOk ρ → GoodEvs (evArg a) →
    matchArg n (utf8Env B) ρ a w ⊑ matchArg n (simEnv B) ρ a w
  matchArgs : ∀ ρ ags ws, DefsOk ρ → GoodEvs (evArgs ags) → (∀ w ∈ ws, ArgOk w) →
    matchArgs n (utf8Env B) ρ ags ws ⊑ matchArgs n (simEnv B) ρ ags ws
  callDef : ∀ ρ x ags, DefsOk ρ → GoodName x → GoodEvs (evArgs ags) →
    callDef n (utf8Env B) ρ x ags ⊑ callDef n (simEnv B) ρ x ags
  tryClauses : ∀ cs ws, (∀ c ∈ cs, GoodEvs (evClause c)) → (∀ w ∈ ws, ArgOk w) →
    tryClauses n (utf8Env B) cs ws ⊑ tryClauses n (simEnv B) cs ws
  premHolds : ∀ ρ pr, DefsOk ρ → GoodEvs (evPrem pr) →
    premHolds n (utf8Env B) ρ pr ⊑ premHolds n (simEnv B) ρ pr
  premsHold : ∀ ρ prs, DefsOk ρ → GoodEvs (evPrems prs) →
    premsHold n (utf8Env B) ρ prs ⊑ premsHold n (simEnv B) ρ prs
  premIter : ∀ ρ pr it ds, DefsOk ρ → GoodEvs (evPrem pr) → GoodEvs (evIter it) →
    GoodEvs (evDoms ds) → premIter n (utf8Env B) ρ pr it ds ⊑ premIter n (simEnv B) ρ pr it ds
  premRounds : ∀ ρ pr xvs ido k, DefsOk ρ → GoodEvs (evPrem pr) →
    premRounds n (utf8Env B) ρ pr xvs ido k ⊑ premRounds n (simEnv B) ρ pr xvs ido k
  derives : ∀ x op ags v, (0, x) ∈ stepReach → (∀ w ∈ ags, ArgOk w) →
    derives n (utf8Env B) x op ags v = true → derives n (simEnv B) x op ags v = true
  anyRule : ∀ op ps ags v rs, (∀ r ∈ rs, GoodEvs (evRule r)) → (∀ w ∈ ags, ArgOk w) →
    anyRule n (utf8Env B) op ps ags v rs = true → anyRule n (simEnv B) op ps ags v rs = true

theorem agreeAt_zero : AgreeAt B 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intros; simp only [evalExp, evalExps, evalExpFields, evalArg, evalArgs, evalDoms,
        evalIterE, evalIterList, evalRounds, Sem.pathGet, Sem.pathSet, Sem.patLen, Sem.matchExp,
        Sem.matchDefault, Sem.matchExps, Sem.matchExpFields, Sem.matchIterE, Sem.matchIterList,
        Sem.matchRounds, Sem.matchArg, Sem.matchArgs, Sem.callDef, Sem.tryClauses, Sem.premHolds,
        Sem.premsHold, Sem.premIter, Sem.premRounds]; exact Res.oof_le _)
    | (intro _ _ _ _ _ _ h; simp [Sem.derives] at h)
    | (intro _ _ _ _ _ _ _ h; simp [Sem.anyRule] at h)

/-- The clauses `simEnv B` finds for a `GoodName` are `GoodEvs`. -/
theorem goodClauses {x : IL.Id} (hx : GoodName x) {d : DefDef}
    (hd : (simEnv B).findDef? x = some d) : ∀ c ∈ d.2.2, GoodEvs (evClause c) := by
  obtain ⟨hR, hok⟩ := findDef?_reach hx.1 hd
  have hn : (1, x) ∉ utf8Allowed := by simp [utf8Allowed, hx.2]
  have := goodEvs_of_reach hn hR hok
  simp only [defDefEv, goodEvs_append, goodEvs_flatMap] at this
  exact this.2

/-- The rules `simEnv B` finds for a reachable relation are `GoodEvs`. -/
theorem goodRules {x : IL.Id} (hx : (0, x) ∈ stepReach) {d : RelDef}
    (hd : (simEnv B).findRel? x = some d) : ∀ r ∈ d.2.2.2, GoodEvs (evRule r) := by
  obtain ⟨hR, hok⟩ := findRel?_reach hx hd
  have hn : (0, x) ∉ utf8Allowed := by simp [utf8Allowed]
  have := goodEvs_of_reach hn hR hok
  simp only [relDefEv, goodEvs_append, goodEvs_flatMap] at this
  exact this.2

theorem agreeAt_succ (m : Nat) (ih : AgreeAt B m) : AgreeAt B (m + 1) := by
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
  have DP := defsPres (utf8Env B) m
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
        gsimp hG
        simp only [evalExp]
        refine Res.bind_le (hexp _ _ hD hG.1) fun v₁ => ?_
        cases boolShort op v₁ with
        | none => exact Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
        | some v => exact Res.Le.refl _
    | cmpE op t e₁ e₂ =>
        gsimp hG
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
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | compE e₁ e₂ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | listE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _ hD (goodEvs_exps hG))
    | liftE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | memE e₁ e₂ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | lenE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | catE e₁ e₂ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | idxE e₁ e₂ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | sliceE e₁ e₂ e₃ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ => Res.Le.refl _
    | updE e₁ p e₂ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun _ => hps _ _ _ _ hD hG.2.1
    | extE e₁ p e₂ =>
        gsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun _ =>
            Res.bind_le (hpg _ _ _ hD hG.2.1) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.2.1
    | callE x args₀ =>
        gsimp hG
        simp only [evalExp]
        exact hcd _ _ _ hD hG.1 hG.2
    | iterE e₀ it =>
        cases it with
        | mk i ds =>
          gsimp hG
          simp only [evalExp]
          exact hit _ _ _ _ hD hG.1 hG.2.1 hG.2.2
    | cvtE e t₁ t₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | subE e t₁ t₂ =>
        gsimp hG
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
        gsimp hGit
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
        gsimp hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | sliceP p e₁ e₂ =>
        gsimp hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ => Res.Le.refl _
    | dotP p a =>
        gsimp hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG) fun _ => Res.Le.refl _
  -- `pathSet`
  · intro ρ v p w hD hG
    cases p with
    | rootP => simp only [Sem.pathSet]; exact Res.Le.refl _
    | idxP p e =>
        gsimp hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.1
    | sliceP p e₁ e₂ =>
        gsimp hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.1
    | dotP p a =>
        gsimp hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG) fun _ =>
          Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG
  -- `patLen`
  · intro ρ e hD hG
    cases e
    case listE es => simp only [Sem.patLen]; exact Res.Le.refl _
    case catE e₁ e₂ =>
      gsimp hG
      simp only [Sem.patLen]
      exact Res.bind_le (hpl _ _ hD hG.1) fun _ =>
        Res.bind_le (hpl _ _ hD hG.2) fun _ => Res.Le.refl _
    case iterE e₀ it =>
      cases it with
      | mk i ds =>
          cases i
          case listN eₙ x =>
            gsimp hG
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
      gsimp hG
      simp only [Sem.matchExp]
      have hpair : ∀ a b, (Sem.matchExp m (utf8Env B) ρ e₁ a >>= fun ρ' =>
          Sem.matchExp m (utf8Env B) ρ' e₂ b) ⊑
          (Sem.matchExp m (simEnv B) ρ e₁ a >>= fun ρ' => Sem.matchExp m (simEnv B) ρ' e₂ b) :=
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
        gsimp hG
        simp only [Sem.matchExp]
        exact hmi _ _ _ _ _ hD hG.1 hG.2.1 hG.2.2
    case cvtE e t₁ t₂ =>
      cases v <;> simp only [Sem.matchExp] <;>
        first
          | exact hmd _ _ _ hD hG
          | exact Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ hD hG
    case subE e t₁ t₂ =>
      gsimp hG
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
            gsimp hG
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
        gsimp hGit
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
    cases a <;> cases w <;> simp only [Sem.matchArg, Round7.argSubOk_utf8Env,
      Round7.matchTypV_utf8Env, Round7.matchSymV_utf8Env] <;>
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
        gsimp hG
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
    rw [Round7.findDef?_utf8Env_of_ne B hx'.2, Round7.call_utf8Env_of_ne B hx'.2]
    refine bind_le_of (Res.Le.refl _) fun d hd => ?_
    have hcl := goodClauses B hx' (Res.ofOption_eq_ok.1 hd)
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
            gsimp hc
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
        gsimp hG
        simp only [Sem.premHolds]
        exact Res.bind_le (hexp _ _ hD hG.2) fun _ => hm _ _ _ hD hG.1
    | rulePr x args₀ op e =>
        gsimp hG
        simp only [Sem.premHolds]
        refine bind_le_of (hargs _ _ hD hG.2.1) fun avs havs =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun v => ?_
        cases hd : Sem.derives m (utf8Env B) x op avs v with
        | true =>
          rw [ih.derives _ _ _ _ hG.1 (evalArgs_argOk hD hG.2.1 havs) hd]
        | false => exact Or.inl (by simp)
    | iterPr pr it =>
        cases it with
        | mk i ds =>
          gsimp hG
          simp only [Sem.premHolds]
          exact hpi _ _ _ _ hD hG.1 hG.2.1 hG.2.2
  -- `premsHold`
  · intro ρ prs hD hG
    simp only [Sem.premsHold]
    exact foldlM_le_of (P := DefsOk) prs
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
        gsimp hGit
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
  · intro x op args₀ v hx hW h
    simp only [Sem.derives] at h ⊢
    rw [Round7.findRel?_utf8Env] at h
    cases hr : (simEnv B).findRel? x with
    | none => rw [hr] at h; simp at h
    | some d =>
        obtain ⟨ps, op', t, rules⟩ := d
        rw [hr] at h
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, ih.anyRule _ _ _ _ _ (goodRules B hx hr) hW h.2⟩
  -- `anyRule`
  · intro op ps args₀ v rs hrs hW h
    cases rs with
    | nil => simp only [Sem.anyRule] at h; exact absurd h (by simp)
    | cons r rs =>
        cases r with
        | ruleD y qs op' e prems =>
            have hr := hrs _ List.mem_cons_self
            gsimp hr
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
theorem agreeAt : ∀ n, AgreeAt B n
  | 0 => agreeAt_zero B
  | n + 1 => agreeAt_succ B n (agreeAt n)

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
