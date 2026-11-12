module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.MonoCall

/-!
# Round 7: environment monotonicity of the evaluator, `simEnv B` to `utf8Env B` (unrefined)

`Sem.monoAt_succ` shows that more fuel only refines the evaluator's answers. This file copies its
proof with the **environment** changing instead of the fuel: at every fuel, every member of the
evaluator's mutual block answers in `utf8Env B` at least what it answers in `simEnv B`, in the
order `Res.Le` (`envMonoAt`). The two environments differ only in the clauses of `$utf8` and in
the primitive for `$utf8` (`findDef?_utf8Env_of_ne`, `call_utf8Env_of_ne`, `findRel?_utf8Env`,
…), so every case is the congruence of `monoAt_succ` except `callDef` at `$utf8`, which is
`utf8_le`. The only hypothesis is that `B` leaves `$utf8` uninterpreted.

The proof is a copy of `Sem.monoAt_succ` (in `Raw/…/SpecTec/Sem/Eval.lean`), kept unrefined
here for the same reason: it is one long congruence over the 29 members. The fuel-free
consequences are in `Proofs/…/Round7/Utf8/MonoDerive.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Round6.MemSimd (utf8Call)

variable (B : Builtins)

/-! ## The environment-independent helpers -/

theorem memTyp_utf8Env (x : IL.Id) : (utf8Env B).memTyp x = (simEnv B).memTyp x := by
  simp only [Env.memTyp, Map.mem]
  exact congrArg Option.isSome (findTyp?_utf8Env B x)

theorem memGram_utf8Env (x : IL.Id) : (utf8Env B).memGram x = (simEnv B).memGram x := by
  simp only [Env.memGram, Map.mem]
  exact congrArg Option.isSome (findGram?_utf8Env B x)

theorem matchTypV_utf8Env : matchTypV (utf8Env B) = matchTypV (simEnv B) := by
  funext ρ pat t
  simp only [matchTypV, memTyp_utf8Env]

theorem matchSymV_utf8Env : matchSymV (utf8Env B) = matchSymV (simEnv B) := by
  funext ρ pat g
  simp only [matchSymV, memGram_utf8Env]

theorem subCaseOk_utf8Env : subCaseOk (utf8Env B) = subCaseOk (simEnv B) := by
  funext ρ t v
  simp only [subCaseOk, findTyp?_utf8Env]

theorem argSubOk_utf8Env : argSubOk (utf8Env B) = argSubOk (simEnv B) := by
  funext ρ e v
  simp only [argSubOk, subCaseOk_utf8Env]

theorem simEnv_call (x : IL.Id) (ws : List ArgV) : (simEnv B).builtins.call x ws = B.call x ws :=
  rfl

theorem bind_ok {α β : Type} (a : α) (f : α → Res β) : (Except.ok a >>= f) = f a := rfl

/-! ## Monotonicity at one fuel -/

/-- **Environment monotonicity at fuel `n`**: every member of the evaluator's mutual block
answers in `utf8Env B` at least what it answers in `simEnv B` (`Res.Le`). The fields follow
`Sem.MonoAt`. -/
structure EnvMonoAt (n : Nat) : Prop where
  exp : ∀ ρ e, evalExp n (simEnv B) ρ e ⊑ evalExp n (utf8Env B) ρ e
  exps : ∀ ρ es, evalExps n (simEnv B) ρ es ⊑ evalExps n (utf8Env B) ρ es
  expFields : ∀ ρ fs, evalExpFields n (simEnv B) ρ fs ⊑ evalExpFields n (utf8Env B) ρ fs
  arg : ∀ ρ a, evalArg n (simEnv B) ρ a ⊑ evalArg n (utf8Env B) ρ a
  args : ∀ ρ args₀, evalArgs n (simEnv B) ρ args₀ ⊑ evalArgs n (utf8Env B) ρ args₀
  doms : ∀ ρ ds, evalDoms n (simEnv B) ρ ds ⊑ evalDoms n (utf8Env B) ρ ds
  iterE : ∀ ρ e it ds, evalIterE n (simEnv B) ρ e it ds ⊑ evalIterE n (utf8Env B) ρ e it ds
  iterList : ∀ ρ e xvs ido k,
    evalIterList n (simEnv B) ρ e xvs ido k ⊑ evalIterList n (utf8Env B) ρ e xvs ido k
  rounds : ∀ ρ e rs, evalRounds n (simEnv B) ρ e rs ⊑ evalRounds n (utf8Env B) ρ e rs
  pathGet : ∀ ρ v p, pathGet n (simEnv B) ρ v p ⊑ pathGet n (utf8Env B) ρ v p
  pathSet : ∀ ρ v p w, pathSet n (simEnv B) ρ v p w ⊑ pathSet n (utf8Env B) ρ v p w
  patLen : ∀ ρ e, patLen n (simEnv B) ρ e ⊑ patLen n (utf8Env B) ρ e
  matchExp : ∀ ρ e v, matchExp n (simEnv B) ρ e v ⊑ matchExp n (utf8Env B) ρ e v
  matchDefault : ∀ ρ e v, matchDefault n (simEnv B) ρ e v ⊑ matchDefault n (utf8Env B) ρ e v
  matchExps : ∀ ρ es vs, matchExps n (simEnv B) ρ es vs ⊑ matchExps n (utf8Env B) ρ es vs
  matchExpFields : ∀ ρ fs gs,
    matchExpFields n (simEnv B) ρ fs gs ⊑ matchExpFields n (utf8Env B) ρ fs gs
  matchIterE : ∀ ρ e it ds v,
    matchIterE n (simEnv B) ρ e it ds v ⊑ matchIterE n (utf8Env B) ρ e it ds v
  matchIterList : ∀ ρ e ds ido vs,
    matchIterList n (simEnv B) ρ e ds ido vs ⊑ matchIterList n (utf8Env B) ρ e ds ido vs
  matchRounds : ∀ ρ e xs ido i vs,
    matchRounds n (simEnv B) ρ e xs ido i vs ⊑ matchRounds n (utf8Env B) ρ e xs ido i vs
  matchArg : ∀ ρ a w, matchArg n (simEnv B) ρ a w ⊑ matchArg n (utf8Env B) ρ a w
  matchArgs : ∀ ρ args₀ ws, matchArgs n (simEnv B) ρ args₀ ws ⊑ matchArgs n (utf8Env B) ρ args₀ ws
  callDef : ∀ ρ x args₀, callDef n (simEnv B) ρ x args₀ ⊑ callDef n (utf8Env B) ρ x args₀
  tryClauses : ∀ cs ws, tryClauses n (simEnv B) cs ws ⊑ tryClauses n (utf8Env B) cs ws
  premHolds : ∀ ρ pr, premHolds n (simEnv B) ρ pr ⊑ premHolds n (utf8Env B) ρ pr
  premsHold : ∀ ρ prs, premsHold n (simEnv B) ρ prs ⊑ premsHold n (utf8Env B) ρ prs
  premIter : ∀ ρ pr it ds, premIter n (simEnv B) ρ pr it ds ⊑ premIter n (utf8Env B) ρ pr it ds
  premRounds : ∀ ρ pr xvs ido k,
    premRounds n (simEnv B) ρ pr xvs ido k ⊑ premRounds n (utf8Env B) ρ pr xvs ido k
  derives : ∀ x op args₀ v, derives n (simEnv B) x op args₀ v = true → derives n (utf8Env B) x op args₀ v = true
  anyRule : ∀ op ps args₀ v rs,
    anyRule n (simEnv B) op ps args₀ v rs = true → anyRule n (utf8Env B) op ps args₀ v rs = true

theorem envMonoAt_zero : EnvMonoAt B 0 := by
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
instead of the fuel. -/
theorem envMonoAt_succ (hB : ∀ ws, B.call "utf8" ws = none) (m : Nat) (ih : EnvMonoAt B m) :
    EnvMonoAt B (m + 1) := by
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
    cases a <;> cases w <;> simp only [matchArg, argSubOk_utf8Env, matchTypV_utf8Env,
      matchSymV_utf8Env] <;>
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
  -- `callDef`: the one non-congruence case
  · intro ρ x args₀
    simp only [callDef]
    refine Res.bind_le (hargs _ _) fun argVs => ?_
    by_cases hx : (ρ.findDef? x).getD x = "utf8"
    · simp only [hx, findDef?_utf8_simEnv, findDef?_utf8Env, Res.ofOption, bind_ok, simEnv_call,
        call_utf8Env_utf8]
      exact utf8_le B hB utf8Rest (findDef?_utf8_simEnv B) utf8Rest_pats m argVs
    · rw [findDef?_utf8Env_of_ne B hx, call_utf8Env_of_ne B hx]
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
        cases hd : derives m (simEnv B) x op avs v with
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
    rw [findRel?_utf8Env]
    cases hr : (simEnv B).findRel? x with
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

/-- **Environment monotonicity**, at every fuel. -/
theorem envMonoAt (hB : ∀ ws, B.call "utf8" ws = none) : ∀ n, EnvMonoAt B n
  | 0 => envMonoAt_zero B
  | n + 1 => envMonoAt_succ B hB n (envMonoAt hB n)

end Silmaril.Wasm.SpecTec.Sim.Round7
