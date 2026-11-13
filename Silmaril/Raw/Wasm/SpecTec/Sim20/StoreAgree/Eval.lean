module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval

/-!
# The evaluator reads its environment only through six lookups (unrefined)

`EnvSame e₁ e₂`: the two environments have the same definitions, relations and primitives, and
the three matchers that consult the type and grammar tables (`matchTypV`, `matchSymV`,
`argSubOk`) agree. Then at every fuel every member of the evaluator's mutual block answers in
`e₂` at least what it answers in `e₁` (`sameMonoAt`, in the order `Res.Le`). Since `EnvSame` is
symmetric, the equalities follow (`Proofs/…/Sim20/StoreAgreeEval.lean`).

The proof is round 7's `envMonoAt_succ` (`Raw/…/Round7/Utf8/Mono.lean`, itself a copy of
`Sem.monoAt_succ`) with the two environments abstracted; its one non-congruence case (`callDef`
at `$utf8`) is a congruence here. Kept unrefined, like its model. The use is the 2.0 `STORE`
erratum: `StoreFix.simEnv20T B` and `StepFix.simEnv20S B` differ only in the `STORE` cases of two
types, which `argSubOk` cannot see.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res

/-- **Two environments the evaluator cannot tell apart.** -/
structure EnvSame (e₁ e₂ : Env) : Prop where
  defs : ∀ x, e₂.findDef? x = e₁.findDef? x
  rels : ∀ x, e₂.findRel? x = e₁.findRel? x
  call : e₂.builtins = e₁.builtins
  typV : matchTypV e₂ = matchTypV e₁
  symV : matchSymV e₂ = matchSymV e₁
  sub : argSubOk e₂ = argSubOk e₁

theorem EnvSame.symm {e₁ e₂ : Env} (h : EnvSame e₁ e₂) : EnvSame e₂ e₁ :=
  ⟨fun x => (h.defs x).symm, fun x => (h.rels x).symm, h.call.symm, h.typV.symm, h.symV.symm,
    h.sub.symm⟩

theorem bind_ok {α β : Type} (a : α) (f : α → Res β) : (Except.ok a >>= f) = f a := rfl

/-- **Agreement at fuel `n`**: every member of the evaluator's mutual block answers in `e₂` at
least what it answers in `e₁` (`Res.Le`). The fields follow `Sem.MonoAt`. -/
structure SameMonoAt (e₁ e₂ : Env) (n : Nat) : Prop where
  exp : ∀ ρ e, evalExp n e₁ ρ e ⊑ evalExp n e₂ ρ e
  exps : ∀ ρ es, evalExps n e₁ ρ es ⊑ evalExps n e₂ ρ es
  expFields : ∀ ρ fs, evalExpFields n e₁ ρ fs ⊑ evalExpFields n e₂ ρ fs
  arg : ∀ ρ a, evalArg n e₁ ρ a ⊑ evalArg n e₂ ρ a
  args : ∀ ρ args₀, evalArgs n e₁ ρ args₀ ⊑ evalArgs n e₂ ρ args₀
  doms : ∀ ρ ds, evalDoms n e₁ ρ ds ⊑ evalDoms n e₂ ρ ds
  iterE : ∀ ρ e it ds, evalIterE n e₁ ρ e it ds ⊑ evalIterE n e₂ ρ e it ds
  iterList : ∀ ρ e xvs ido k,
    evalIterList n e₁ ρ e xvs ido k ⊑ evalIterList n e₂ ρ e xvs ido k
  rounds : ∀ ρ e rs, evalRounds n e₁ ρ e rs ⊑ evalRounds n e₂ ρ e rs
  pathGet : ∀ ρ v p, pathGet n e₁ ρ v p ⊑ pathGet n e₂ ρ v p
  pathSet : ∀ ρ v p w, pathSet n e₁ ρ v p w ⊑ pathSet n e₂ ρ v p w
  patLen : ∀ ρ e, patLen n e₁ ρ e ⊑ patLen n e₂ ρ e
  matchExp : ∀ ρ e v, matchExp n e₁ ρ e v ⊑ matchExp n e₂ ρ e v
  matchDefault : ∀ ρ e v, matchDefault n e₁ ρ e v ⊑ matchDefault n e₂ ρ e v
  matchExps : ∀ ρ es vs, matchExps n e₁ ρ es vs ⊑ matchExps n e₂ ρ es vs
  matchExpFields : ∀ ρ fs gs,
    matchExpFields n e₁ ρ fs gs ⊑ matchExpFields n e₂ ρ fs gs
  matchIterE : ∀ ρ e it ds v,
    matchIterE n e₁ ρ e it ds v ⊑ matchIterE n e₂ ρ e it ds v
  matchIterList : ∀ ρ e ds ido vs,
    matchIterList n e₁ ρ e ds ido vs ⊑ matchIterList n e₂ ρ e ds ido vs
  matchRounds : ∀ ρ e xs ido i vs,
    matchRounds n e₁ ρ e xs ido i vs ⊑ matchRounds n e₂ ρ e xs ido i vs
  matchArg : ∀ ρ a w, matchArg n e₁ ρ a w ⊑ matchArg n e₂ ρ a w
  matchArgs : ∀ ρ args₀ ws, matchArgs n e₁ ρ args₀ ws ⊑ matchArgs n e₂ ρ args₀ ws
  callDef : ∀ ρ x args₀, callDef n e₁ ρ x args₀ ⊑ callDef n e₂ ρ x args₀
  tryClauses : ∀ cs ws, tryClauses n e₁ cs ws ⊑ tryClauses n e₂ cs ws
  premHolds : ∀ ρ pr, premHolds n e₁ ρ pr ⊑ premHolds n e₂ ρ pr
  premsHold : ∀ ρ prs, premsHold n e₁ ρ prs ⊑ premsHold n e₂ ρ prs
  premIter : ∀ ρ pr it ds, premIter n e₁ ρ pr it ds ⊑ premIter n e₂ ρ pr it ds
  premRounds : ∀ ρ pr xvs ido k,
    premRounds n e₁ ρ pr xvs ido k ⊑ premRounds n e₂ ρ pr xvs ido k
  derives : ∀ x op args₀ v, derives n e₁ x op args₀ v = true → derives n e₂ x op args₀ v = true
  anyRule : ∀ op ps args₀ v rs,
    anyRule n e₁ op ps args₀ v rs = true → anyRule n e₂ op ps args₀ v rs = true

theorem sameMonoAt_zero (e₁ e₂ : Env) : SameMonoAt e₁ e₂ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; simp only [evalExp]; exact Res.oof_le _
  · intros; simp only [evalExps]; exact Res.oof_le _
  · intros; simp only [evalExpFields]; exact Res.oof_le _
  · intros; simp only [evalArg]; exact Res.oof_le _
  · intros; simp only [evalArgs]; exact Res.oof_le _
  · intros; simp only [evalDoms]; exact Res.oof_le _
  · intros; simp only [evalIterE]; exact Res.oof_le _
  · intros; simp only [evalIterList]; exact Res.oof_le _
  · intros; simp only [evalRounds]; exact Res.oof_le _
  · intros; simp only [pathGet]; exact Res.oof_le _
  · intros; simp only [pathSet]; exact Res.oof_le _
  · intros; simp only [patLen]; exact Res.oof_le _
  · intros; simp only [matchExp]; exact Res.oof_le _
  · intros; simp only [matchDefault]; exact Res.oof_le _
  · intros; simp only [matchExps]; exact Res.oof_le _
  · intros; simp only [matchExpFields]; exact Res.oof_le _
  · intros; simp only [matchIterE]; exact Res.oof_le _
  · intros; simp only [matchIterList]; exact Res.oof_le _
  · intros; simp only [matchRounds]; exact Res.oof_le _
  · intros; simp only [matchArg]; exact Res.oof_le _
  · intros; simp only [matchArgs]; exact Res.oof_le _
  · intros; simp only [callDef]; exact Res.oof_le _
  · intros; simp only [tryClauses]; exact Res.oof_le _
  · intros; simp only [premHolds]; exact Res.oof_le _
  · intros; simp only [premsHold]; exact Res.oof_le _
  · intros; simp only [premIter]; exact Res.oof_le _
  · intros; simp only [premRounds]; exact Res.oof_le _
  · intros _ _ _ _ h; simp [derives] at h
  · intros _ _ _ _ _ h; simp [anyRule] at h

/-- **The inductive step**: `Sem.monoAt_succ`'s case analysis, with the environment changing
instead of the fuel; every case is a congruence. -/
theorem sameMonoAt_succ {e₁ e₂ : Env} (hS : EnvSame e₁ e₂) (m : Nat) (ih : SameMonoAt e₁ e₂ m) :
    SameMonoAt e₁ e₂ (m + 1) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `evalExp`
  · intro ρ e
    cases e with
    | varE x => simp only [evalExp]; exact Res.Le.refl _
    | boolE b => simp only [evalExp]; exact Res.Le.refl _
    | numE n => simp only [evalExp]; exact Res.Le.refl _
    | textE t => simp only [evalExp]; exact Res.Le.refl _
    | unE op t e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | binE op t e₁ e₂ =>
        simp only [evalExp]
        refine Res.bind_le (hexp _ _) fun v₁ => ?_
        cases boolShort op v₁ with
        | none => exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
        | some v => exact Res.Le.refl _
    | cmpE op t e₁ e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | tupE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _)
    | projE e i =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | caseE op e => simp only [evalExp]; exact Res.map_le _ (hexp _ _)
    | uncaseE e op =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | optE eo =>
        cases eo <;> simp only [evalExp] <;>
          first
            | with_reducible exact Res.Le.refl _
            | exact Res.map_le _ (hexp _ _)
    | theE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | strE fs => simp only [evalExp]; exact Res.map_le _ (hefs _ _)
    | dotE e a =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | compE e₁ e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | listE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _)
    | liftE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | memE e₁ e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | lenE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | catE e₁ e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | idxE e₁ e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | sliceE e₁ e₂ e₃ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | updE e₁ p e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => hps _ _ _ _
    | extE e₁ p e₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (hpg _ _ _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _
    | callE x args₀ => simp only [evalExp]; exact hcd _ _ _
    | iterE e₀ it =>
        cases it with
        | mk i ds => simp only [evalExp]; exact hit _ _ _ _
    | cvtE e t₁ t₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | subE e t₁ t₂ => simp only [evalExp]; exact hexp _ _
  -- `evalExps`
  · intro ρ es
    simp only [evalExps]
    exact Res.mapM_le (fun _ => hexp _ _) es
  -- `evalExpFields`
  · intro ρ fs
    simp only [evalExpFields]
    refine Res.mapM_le (fun f => ?_) fs
    cases f with
    | mk a e => exact Res.map_le _ (hexp _ _)
  -- `evalArg`
  · intro ρ a
    cases a <;> simp only [evalArg] <;>
      first
        | exact Res.map_le _ (hexp _ _)
        | with_reducible exact Res.Le.refl _
  -- `evalArgs`
  · intro ρ args₀
    simp only [evalArgs]
    exact Res.mapM_le (fun _ => harg _ _) args₀
  -- `evalDoms`
  · intro ρ ds
    simp only [evalDoms]
    exact Res.mapM_le (fun _ => Res.map_le _ (hexp _ _)) ds
  -- `evalIterE`
  · intro ρ e it ds
    cases it with
    | opt =>
        simp only [evalIterE]
        refine Res.bind_le (hdoms _ _) fun xvs => Res.assert_le ?_
        refine Res.bind_le (Res.Le.refl _) fun os => ?_
        split
        · exact Res.Le.refl _
        · split
          · exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
          · exact Res.Le.refl _
    | list =>
        simp only [evalIterE]
        exact Res.bind_le (hdoms _ _) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hitl _ _ _ _ _)
    | list1 =>
        simp only [evalIterE]
        exact Res.bind_le (hdoms _ _) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ =>
            Res.assert_le (hitl _ _ _ _ _))
    | listN eₙ x =>
        simp only [evalIterE]
        exact Res.bind_le (hdoms _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ => hitl _ _ _ _ _
  -- `evalIterList`
  · intro ρ e xvs ido k
    simp only [evalIterList]
    exact Res.bind_le (Res.Le.refl _) fun _ =>
      Res.assert_le (Res.bind_le (hrnd _ _ _) fun _ => Res.Le.refl _)
  -- `evalRounds`
  · intro ρ e rs
    simp only [evalRounds]
    exact Res.mapM_le (fun _ => hexp _ _) rs
  -- `pathGet`
  · intro ρ v p
    cases p with
    | rootP => simp only [pathGet]; exact Res.Le.refl _
    | idxP p e =>
        simp only [pathGet]
        exact Res.bind_le (hpg _ _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | sliceP p e₁ e₂ =>
        simp only [pathGet]
        exact Res.bind_le (hpg _ _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | dotP p a =>
        simp only [pathGet]
        exact Res.bind_le (hpg _ _ _) fun _ => Res.Le.refl _
  -- `pathSet`
  · intro ρ v p w
    cases p with
    | rootP => simp only [pathSet]; exact Res.Le.refl _
    | idxP p e =>
        simp only [pathSet]
        exact Res.bind_le (hpg _ _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _
    | sliceP p e₁ e₂ =>
        simp only [pathSet]
        exact Res.bind_le (hpg _ _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (hexp _ _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _
    | dotP p a =>
        simp only [pathSet]
        exact Res.bind_le (hpg _ _ _) fun _ =>
          Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _
  -- `patLen`
  · intro ρ e
    cases e
    case listE es => simp only [patLen]; exact Res.Le.refl _
    case catE e₁ e₂ =>
      simp only [patLen]
      exact Res.bind_le (hpl _ _) fun _ =>
        Res.bind_le (hpl _ _) fun _ => Res.Le.refl _
    case iterE e₀ it =>
      cases it with
      | mk i ds =>
          cases i <;> simp only [patLen] <;>
            exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    case optE eo =>
      cases eo <;> simp only [patLen] <;>
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    all_goals
      simp only [patLen]
      exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
  -- `matchExp`
  · intro ρ e v
    cases e
    case varE x => simp only [matchExp]; exact Res.Le.refl _
    case boolE b => simp only [matchExp]; exact Res.Le.refl _
    case numE n => simp only [matchExp]; exact Res.Le.refl _
    case textE t => simp only [matchExp]; exact Res.Le.refl _
    case unE op t e =>
      cases op <;> cases v <;> simp only [matchExp] <;>
        first
          | exact hmd _ _ _
          | exact Res.assert_le (hm _ _ _)
          | exact Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _)
    case tupE es =>
      simp only [matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _
    case projE e i =>
      simp only [matchExp]
      split
      · exact hm _ _ _
      · exact hmd _ _ _
    case caseE op e =>
      simp only [matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => Res.assert_le (hm _ _ _)
    case uncaseE e op => simp only [matchExp]; exact hm _ _ _
    case optE eo =>
      cases eo <;> simp only [matchExp] <;>
        first
          | with_reducible exact Res.Le.refl _
          | exact Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _
    case strE fs =>
      simp only [matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => hmf _ _ _
    case listE es =>
      simp only [matchExp]
      exact Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _
    case catE e₁ e₂ =>
      simp only [matchExp]
      refine Res.bind_le (Res.Le.refl _) fun vs => ?_
      refine Res.elimUndef_le (hpl _ _) (fun k => ?_) (fun _ => ?_)
      · exact Res.assert_le (Res.bind_le (hm _ _ _) fun _ => hm _ _ _)
      · refine Res.elimUndef_le (hpl _ _) (fun k => ?_) (fun _ => ?_)
        · exact Res.assert_le (Res.bind_le (hm _ _ _) fun _ => hm _ _ _)
        · exact Res.scan_le (fun _ => Res.bind_le (hm _ _ _) fun _ => hm _ _ _) _ _
    case iterE e₀ it =>
      cases it with
      | mk i ds => simp only [matchExp]; exact hmi _ _ _ _ _
    case cvtE e t₁ t₂ =>
      cases v <;> simp only [matchExp] <;>
        first
          | exact hmd _ _ _
          | exact Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _
    case subE e t₁ t₂ => simp only [matchExp]; exact hm _ _ _
    all_goals (simp only [matchExp]; exact hmd _ _ _)
  -- `matchDefault`
  · intro ρ e v
    simp only [matchDefault]
    exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
  -- `matchExps`
  · intro ρ es vs
    cases es with
    | nil => cases vs <;> simp only [matchExps] <;> exact Res.Le.refl _
    | cons e es =>
        cases vs with
        | nil => simp only [matchExps]; exact Res.Le.refl _
        | cons v vs =>
            simp only [matchExps]
            exact Res.bind_le (hm _ _ _) fun _ => hms _ _ _
  -- `matchExpFields`
  · intro ρ fs gs
    cases fs with
    | nil => cases gs <;> simp only [matchExpFields] <;> exact Res.Le.refl _
    | cons f fs =>
        cases f with
        | mk a e =>
            cases gs with
            | nil => simp only [matchExpFields]; exact Res.Le.refl _
            | cons g gs =>
                simp only [matchExpFields]
                exact Res.assert_le (Res.bind_le (hm _ _ _) fun _ => hmf _ _ _)
  -- `matchIterE`
  · intro ρ e it ds v
    cases it with
    | opt =>
        simp only [matchIterE]
        refine Res.bind_le (Res.Le.refl _) fun o => ?_
        cases o with
        | none => exact hms _ _ _
        | some w =>
            exact Res.bind_le (hm _ _ _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hms _ _ _
    | list =>
        simp only [matchIterE]
        exact Res.bind_le (Res.Le.refl _) fun _ => hmil _ _ _ _ _
    | list1 =>
        simp only [matchIterE]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          Res.assert_le (hmil _ _ _ _ _)
    | listN eₙ x =>
        simp only [matchIterE]
        exact Res.bind_le (Res.Le.refl _) fun _ =>
          Res.bind_le (hm _ _ _) fun _ => hmil _ _ _ _ _
  -- `matchIterList`
  · intro ρ e ds ido vs
    simp only [matchIterList]
    exact Res.bind_le (hmr _ _ _ _ _ _) fun _ => hms _ _ _
  -- `matchRounds`
  · intro ρ e xs ido i vs
    cases vs with
    | nil => simp only [matchRounds]; exact Res.Le.refl _
    | cons v vs =>
        cases ido <;> simp only [matchRounds] <;>
          exact Res.bind_le (hm _ _ _) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (hmr _ _ _ _ _ _) fun _ => Res.Le.refl _
  -- `matchArg`
  · intro ρ a w
    cases a <;> cases w <;> simp only [matchArg, hS.sub, hS.typV, hS.symV] <;>
      first
        | with_reducible exact Res.Le.refl _
        | (split
           · exact hm _ _ _
           · exact Res.Le.refl _)
  -- `matchArgs`
  · intro ρ args₀ ws
    cases args₀ with
    | nil => cases ws <;> simp only [matchArgs] <;> exact Res.Le.refl _
    | cons a args₀ =>
        cases ws with
        | nil => simp only [matchArgs]; exact Res.Le.refl _
        | cons w ws =>
            simp only [matchArgs]
            exact Res.bind_le (hma _ _ _) fun _ => hmas _ _ _
  -- `callDef`
  · intro ρ x args₀
    simp only [callDef, hS.defs, hS.call]
    refine Res.bind_le (hargs _ _) fun argVs => ?_
    exact Res.bind_le (Res.Le.refl _) fun _ =>
      Res.elimUndef_le (htc _ _) (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)
  -- `tryClauses`
  · intro cs ws
    cases cs with
    | nil => simp only [tryClauses]; exact Res.Le.refl _
    | cons c cs =>
        cases c with
        | defD q pats e prems =>
            simp only [tryClauses]
            exact Res.elimUndef_le
              (Res.bind_le (hmas _ _ _) fun _ => hphs _ _)
              (fun _ => hexp _ _) (fun _ => htc _ _)
  -- `premHolds`
  · intro ρ pr
    cases pr with
    | ifPr e =>
        simp only [premHolds]
        exact Res.bind_le (hexp _ _) fun _ => Res.Le.refl _
    | elsePr => simp only [premHolds]; exact Res.Le.refl _
    | letPr e₁ e₂ =>
        simp only [premHolds]
        exact Res.bind_le (hexp _ _) fun _ => hm _ _ _
    | rulePr x args₀ op e =>
        simp only [premHolds]
        refine Res.bind_le (hargs _ _) fun avs =>
          Res.bind_le (hexp _ _) fun v => ?_
        cases hd : derives m e₁ x op avs v with
        | true => rw [ih.derives _ _ _ _ hd]
        | false => exact Or.inl (by simp)
    | iterPr pr it =>
        cases it with
        | mk i ds => simp only [premHolds]; exact hpi _ _ _ _
  -- `premsHold`
  · intro ρ prs
    simp only [premsHold]
    exact Res.foldlM_le (fun _ _ => hph _ _) prs ρ
  -- `premIter`
  · intro ρ pr it ds
    cases it with
    | opt =>
        simp only [premIter]
        refine Res.bind_le (hdoms _ _) fun xvs => Res.assert_le ?_
        refine Res.bind_le (Res.Le.refl _) fun os => ?_
        split
        · exact Res.Le.refl _
        · split
          · exact Res.bind_le (hph _ _) fun _ => Res.Le.refl _
          · exact Res.Le.refl _
    | list =>
        simp only [premIter]
        exact Res.bind_le (hdoms _ _) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ => hpr _ _ _ _ _)
    | list1 =>
        simp only [premIter]
        exact Res.bind_le (hdoms _ _) fun _ =>
          Res.assert_le (Res.bind_le (Res.Le.refl _) fun _ =>
            Res.assert_le (hpr _ _ _ _ _))
    | listN eₙ x =>
        simp only [premIter]
        exact Res.bind_le (hdoms _ _) fun _ =>
          Res.bind_le (hexp _ _) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ => hpr _ _ _ _ _
  -- `premRounds`
  · intro ρ pr xvs ido k
    simp only [premRounds]
    exact Res.bind_le (Res.Le.refl _) fun _ =>
      Res.assert_le (Res.bind_le (Res.mapM_le (fun _ => hph _ _) _) fun _ =>
        Res.Le.refl _)
  -- `derives`
  · intro x op args₀ v h
    simp only [derives] at h ⊢
    rw [hS.rels]
    cases hr : e₁.findRel? x with
    | none => rw [hr] at h; simp at h
    | some d =>
        obtain ⟨ps, op', t, rules⟩ := d
        rw [hr] at h
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, ih.anyRule _ _ _ _ _ h.2⟩
  -- `anyRule`
  · intro op ps args₀ v rs h
    cases rs with
    | nil => simp only [anyRule] at h; exact absurd h (by simp)
    | cons r rs =>
        cases r with
        | ruleD y qs op' e prems =>
            simp only [anyRule, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
            rcases h with ⟨hop, hb⟩ | hrest
            · refine Or.inl ⟨hop, ?_⟩
              refine Res.isOk_le ?_ hb
              exact Res.bind_le (Res.Le.refl _) fun _ =>
                Res.bind_le (hm _ _ _) fun _ => hphs _ _
            · exact Or.inr (ih.anyRule _ _ _ _ _ hrest)

/-- **Agreement**, at every fuel. -/
theorem sameMonoAt {e₁ e₂ : Env} (h : EnvSame e₁ e₂) : ∀ n, SameMonoAt e₁ e₂ n
  | 0 => sameMonoAt_zero e₁ e₂
  | n + 1 => sameMonoAt_succ h n (sameMonoAt h n)


/-! ## The equalities -/

theorem le_antisymm {α : Type} {r₁ r₂ : Res α} (h₁ : r₁ ⊑ r₂) (h₂ : r₂ ⊑ r₁) : r₁ = r₂ := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · rw [h₁, h₂]
    · exact h₂
  · exact h₁.symm

theorem evalExp_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (e : Exp) :
    evalExp n e₂ ρ e = evalExp n e₁ ρ e :=
  le_antisymm ((sameMonoAt h.symm n).exp ρ e) ((sameMonoAt h n).exp ρ e)

theorem evalArgs_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (as : List Arg) :
    evalArgs n e₂ ρ as = evalArgs n e₁ ρ as :=
  le_antisymm ((sameMonoAt h.symm n).args ρ as) ((sameMonoAt h n).args ρ as)

theorem evalDoms_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (ds : List Dom) :
    evalDoms n e₂ ρ ds = evalDoms n e₁ ρ ds :=
  le_antisymm ((sameMonoAt h.symm n).doms ρ ds) ((sameMonoAt h n).doms ρ ds)

theorem matchExp_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (e : Exp)
    (v : Value) : matchExp n e₂ ρ e v = matchExp n e₁ ρ e v :=
  le_antisymm ((sameMonoAt h.symm n).matchExp ρ e v) ((sameMonoAt h n).matchExp ρ e v)

theorem matchArgs_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (as : List Arg)
    (ws : List ArgV) : matchArgs n e₂ ρ as ws = matchArgs n e₁ ρ as ws :=
  le_antisymm ((sameMonoAt h.symm n).matchArgs ρ as ws) ((sameMonoAt h n).matchArgs ρ as ws)

theorem premsHold_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (ps : List Prem) :
    premsHold n e₂ ρ ps = premsHold n e₁ ρ ps :=
  le_antisymm ((sameMonoAt h.symm n).premsHold ρ ps) ((sameMonoAt h n).premsHold ρ ps)

theorem derives_eq {e₁ e₂ : Env} (h : EnvSame e₁ e₂) (n : Nat) (x : IL.Id) (op : MixopS)
    (as : List ArgV) (v : Value) : derives n e₂ x op as v = derives n e₁ x op as v := by
  cases h₁ : derives n e₁ x op as v
  · cases h₂ : derives n e₂ x op as v
    · rfl
    · exact absurd ((sameMonoAt h.symm n).derives x op as v h₂) (by simp [h₁])
  · exact (sameMonoAt h n).derives x op as v h₁

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree
