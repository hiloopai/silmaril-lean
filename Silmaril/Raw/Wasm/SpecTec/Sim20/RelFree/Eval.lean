module

public import Silmaril.Wasm.SpecTec.Sim20.RelFree.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms

/-!
# Relation-free syntax evaluates alike under any relation table (unrefined)

`AgreeAt bad env r n`: at fuel `n`, every member of the evaluator that relation-free syntax can
reach answers in `withRels env r` at least what it answers in `env`, provided the syntax it is
given is `GoodEvs bad`, its scope's definition variables avoid `bad` (`DefsOk`), its evaluated
definition arguments avoid `bad` (`ArgOk`), and the clauses of every definition of `env` outside
`bad` are harmless (`DefsGood bad env`).

The proof is `Round7.Script.agreeAt_succ` (`Round7/Script/Agree.lean`) with the two environments
`env` and `withRels env r` in place of `utf8Env B` and `simEnv B`, and two changes:

* `derives` and `anyRule` are not members: a `GoodEvs` premise is never a `rulePr`, so the
  `rulePr` case of `premHolds` is absurd and nothing else reaches `derives`;
* `callDef` is a congruence for every name, since `withRels env r` has the definitions of `env`
  (definitionally); the clauses found are harmless by `DefsGood`.

Kept unrefined, like its model; the equalities are in `Proofs/…/Sim20/RelFreeEq.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evExps evOExp evEFields evPath evIterExp evIter
  evDoms evArg evArgs evPrem evPrems evClause evRule evTyp defsPres bind_le_of mapM_le_of
  foldlM_le_of elimUndef_le_of mapM_ok_mem matchTypV_defs matchSymV_defs mem_of_find?)

variable {bad : List String}

/-! ## The invariants -/

@[simp] theorem goodEvs_nil : GoodEvs bad [] := by simp [GoodEvs]

@[simp] theorem goodEvs_cons {e : Ev} {l : List Ev} :
    GoodEvs bad (e :: l) ↔ rfEvB bad e = true ∧ GoodEvs bad l := by
  simp [GoodEvs]

@[simp] theorem goodEvs_append {l₁ l₂ : List Ev} :
    GoodEvs bad (l₁ ++ l₂) ↔ GoodEvs bad l₁ ∧ GoodEvs bad l₂ := by
  simp only [GoodEvs, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

@[simp] theorem rfEvB_atom (a : String) : rfEvB bad (.atom a) = true ↔ True := by simp [rfEvB]
@[simp] theorem rfEvB_comp : rfEvB bad .comp = true ↔ True := by simp [rfEvB]
@[simp] theorem rfEvB_upd (e : Exp) (ats : List String) : rfEvB bad (.upd e ats) = true ↔ True := by
  simp [rfEvB]
@[simp] theorem rfEvB_ref1 (x : String) : rfEvB bad (.ref 1 x) = true ↔ GoodName bad x := by
  simp [rfEvB, GoodName]

@[simp] theorem goodEvs_flatMap {α : Type} {f : α → List Ev} {l : List α} :
    GoodEvs bad (l.flatMap f) ↔ ∀ x ∈ l, GoodEvs bad (f x) := by
  simp only [GoodEvs, List.mem_flatMap]
  exact ⟨fun h x hx e he => h e ⟨x, hx, he⟩, fun h e ⟨x, hx, he⟩ => h x hx e he⟩

/-- Unfold the events of a term into the conjunction of `GoodEvs` of its parts. -/
syntax "rsimp " ident : tactic
macro_rules
  | `(tactic| rsimp $h) => `(tactic| simp only [evExp, evExps, evOExp, evEFields, evPath,
      evIterExp, evIter, evDoms, evArg, evArgs, evPrem, evPrems, evClause, evRule, goodEvs_append,
      goodEvs_cons, goodEvs_nil, rfEvB_atom, rfEvB_comp, rfEvB_upd, rfEvB_ref1,
      true_and, and_true, and_assoc] at $h:ident)

theorem goodEvs_exps : ∀ {es : List Exp}, GoodEvs bad (evExps es) → ∀ e ∈ es, GoodEvs bad (evExp e)
  | [], _ => by simp
  | e :: es, h => by
    simp only [evExps, goodEvs_append] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact goodEvs_exps h.2 e' he'

theorem goodEvs_doms : ∀ {ds : List Dom}, GoodEvs bad (evDoms ds) →
    ∀ e ∈ ds.map domSrc, GoodEvs bad (evExp e)
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodEvs_append] at h
    intro e' he'
    simp only [List.map_cons, List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact h.1
    · exact goodEvs_doms h.2 e' he'

theorem goodEvs_doms' : ∀ {ds : List Dom}, GoodEvs bad (evDoms ds) →
    ∀ d ∈ ds, GoodEvs bad (evExp (domSrc d))
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodEvs_append] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact goodEvs_doms' h.2 d hd

theorem goodEvs_args : ∀ {ags : List Arg}, GoodEvs bad (evArgs ags) → ∀ a ∈ ags, GoodEvs bad (evArg a)
  | [], _ => by simp
  | a :: ags, h => by
    simp only [evArgs, goodEvs_append] at h
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h.1
    · exact goodEvs_args h.2 a' ha'

theorem goodEvs_prems : ∀ {ps : List Prem}, GoodEvs bad (evPrems ps) → ∀ p ∈ ps, GoodEvs bad (evPrem p)
  | [], _ => by simp
  | p :: ps, h => by
    simp only [evPrems, goodEvs_append] at h
    intro p' hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact h.1
    · exact goodEvs_prems h.2 p' hp'

theorem goodEvs_fields : ∀ {fs : List ExpField}, GoodEvs bad (evEFields fs) →
    ∀ a e, ExpField.mk a e ∈ fs → GoodEvs bad (evExp e)
  | [], _ => by simp
  | .mk a e :: fs, h => by
    simp only [evEFields, goodEvs_cons, goodEvs_append] at h
    intro a' e' he'
    rcases List.mem_cons.1 he' with he' | he'
    · cases he'; exact h.2.1
    · exact goodEvs_fields h.2.2 a' e' he'

/-! ## Scopes -/

theorem defsOk_empty : DefsOk bad VarEnv.empty := by simp [DefsOk, VarEnv.empty, Map.empty]

theorem defsOk_of_defs {ρ ρ' : VarEnv} (h : DefsOk bad ρ) (he : ρ'.defs = ρ.defs) :
    DefsOk bad ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem defsOk_bindVal {ρ : VarEnv} (h : DefsOk bad ρ) (x : IL.Id) (v : Value) :
    DefsOk bad (ρ.bindVal x v) := h

theorem defsOk_bindVals {ρ : VarEnv} (h : DefsOk bad ρ) (xs : List (IL.Id × Value)) :
    DefsOk bad (ρ.bindVals xs) := h

theorem defsOk_bindDef {ρ : VarEnv} (h : DefsOk bad ρ) (x : IL.Id) {y : IL.Id}
    (hy : GoodName bad y) : DefsOk bad (ρ.bindDef x y) := by
  intro p hp
  simp only [VarEnv.bindDef, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact hy
    · exact h p hp

theorem goodName_resolve {ρ : VarEnv} (h : DefsOk bad ρ) {x : IL.Id} (hx : GoodName bad x) :
    GoodName bad ((ρ.findDef? x).getD x) := by
  cases hf : ρ.findDef? x with
  | none => exact hx
  | some y => exact h (x, y) (mem_of_find? hf)

theorem matchArg_defsOk {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV}
    (h : DefsOk bad ρ) (hw : ArgOk bad w) (hm : matchArg n env ρ a w = .ok ρ') :
    DefsOk bad ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact defsOk_of_defs h ((defsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact defsOk_of_defs h (matchTypV_defs hm)
  case defA.defName y x => cases hm; exact defsOk_bindDef h y hw
  case gramA.gram => exact defsOk_of_defs h (matchSymV_defs hm)
  all_goals cases hm

theorem matchArgs_defsOk {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, DefsOk bad ρ →
      (∀ w ∈ ws, ArgOk bad w) → matchArgs n env ρ ags ws = .ok ρ' → DefsOk bad ρ'
  | 0, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | n + 1, ρ, ρ', ags, ws, h, hw, hm => by
    cases ags with
    | nil => cases ws <;> simp only [matchArgs] at hm <;> cases hm; exact h
    | cons a ags =>
      cases ws with
      | nil => simp only [matchArgs] at hm; cases hm
      | cons w ws =>
        simp only [matchArgs, Res.bind_eq_ok] at hm
        obtain ⟨ρ₁, h₁, h₂⟩ := hm
        exact matchArgs_defsOk n (matchArg_defsOk h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

/-- **Evaluated arguments are `ArgOk`.** -/
theorem evalArgs_argOk {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (h : DefsOk bad ρ) (hG : GoodEvs bad (evArgs ags)) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgOk bad w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem he w hw
  have hGa := goodEvs_args hG a ha
  rcases n with _ | n
  · simp [evalArg] at hfa
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA => cases hfa; trivial
  case defA x =>
    cases hfa
    simp only [evArg, goodEvs_cons, rfEvB_ref1, goodEvs_nil, and_true] at hGa
    exact goodName_resolve h hGa
  case gramA => cases hfa; trivial

/-! ## The agreement -/

theorem argSubOk_withRels (env : Env) (r : Map RelDef) : argSubOk (withRels env r) = argSubOk env :=
  rfl

theorem matchTypV_withRels (env : Env) (r : Map RelDef) : matchTypV (withRels env r) = matchTypV env :=
  rfl

theorem matchSymV_withRels (env : Env) (r : Map RelDef) : matchSymV (withRels env r) = matchSymV env :=
  rfl

variable (bad) (env : Env) (r : Map RelDef)

/-- **Environment monotonicity in the relation table at fuel `n`**, on relation-free inputs. -/
structure AgreeAt (n : Nat) : Prop where
  exp : ∀ ρ e, DefsOk bad ρ → GoodEvs bad (evExp e) →
    evalExp n env ρ e ⊑ evalExp n (withRels env r) ρ e
  exps : ∀ ρ es, DefsOk bad ρ → (∀ e ∈ es, GoodEvs bad (evExp e)) →
    evalExps n env ρ es ⊑ evalExps n (withRels env r) ρ es
  expFields : ∀ ρ fs, DefsOk bad ρ → GoodEvs bad (evEFields fs) →
    evalExpFields n env ρ fs ⊑ evalExpFields n (withRels env r) ρ fs
  arg : ∀ ρ a, DefsOk bad ρ → GoodEvs bad (evArg a) →
    evalArg n env ρ a ⊑ evalArg n (withRels env r) ρ a
  args : ∀ ρ ags, DefsOk bad ρ → GoodEvs bad (evArgs ags) →
    evalArgs n env ρ ags ⊑ evalArgs n (withRels env r) ρ ags
  doms : ∀ ρ ds, DefsOk bad ρ → GoodEvs bad (evDoms ds) →
    evalDoms n env ρ ds ⊑ evalDoms n (withRels env r) ρ ds
  iterE : ∀ ρ e it ds, DefsOk bad ρ → GoodEvs bad (evExp e) → GoodEvs bad (evIter it) → GoodEvs bad (evDoms ds) →
    evalIterE n env ρ e it ds ⊑ evalIterE n (withRels env r) ρ e it ds
  iterList : ∀ ρ e xvs ido k, DefsOk bad ρ → GoodEvs bad (evExp e) →
    evalIterList n env ρ e xvs ido k ⊑ evalIterList n (withRels env r) ρ e xvs ido k
  rounds : ∀ ρ e rs, DefsOk bad ρ → GoodEvs bad (evExp e) →
    evalRounds n env ρ e rs ⊑ evalRounds n (withRels env r) ρ e rs
  pathGet : ∀ ρ v p, DefsOk bad ρ → GoodEvs bad (evPath p) →
    pathGet n env ρ v p ⊑ pathGet n (withRels env r) ρ v p
  pathSet : ∀ ρ v p w, DefsOk bad ρ → GoodEvs bad (evPath p) →
    pathSet n env ρ v p w ⊑ pathSet n (withRels env r) ρ v p w
  patLen : ∀ ρ e, DefsOk bad ρ → GoodEvs bad (evExp e) →
    patLen n env ρ e ⊑ patLen n (withRels env r) ρ e
  matchExp : ∀ ρ e v, DefsOk bad ρ → GoodEvs bad (evExp e) →
    matchExp n env ρ e v ⊑ matchExp n (withRels env r) ρ e v
  matchDefault : ∀ ρ e v, DefsOk bad ρ → GoodEvs bad (evExp e) →
    matchDefault n env ρ e v ⊑ matchDefault n (withRels env r) ρ e v
  matchExps : ∀ ρ es vs, DefsOk bad ρ → (∀ e ∈ es, GoodEvs bad (evExp e)) →
    matchExps n env ρ es vs ⊑ matchExps n (withRels env r) ρ es vs
  matchExpFields : ∀ ρ fs gs, DefsOk bad ρ → GoodEvs bad (evEFields fs) →
    matchExpFields n env ρ fs gs ⊑ matchExpFields n (withRels env r) ρ fs gs
  matchIterE : ∀ ρ e it ds v, DefsOk bad ρ → GoodEvs bad (evExp e) → GoodEvs bad (evIter it) →
    GoodEvs bad (evDoms ds) → matchIterE n env ρ e it ds v ⊑ matchIterE n (withRels env r) ρ e it ds v
  matchIterList : ∀ ρ e ds ido vs, DefsOk bad ρ → GoodEvs bad (evExp e) → GoodEvs bad (evDoms ds) →
    matchIterList n env ρ e ds ido vs ⊑ matchIterList n (withRels env r) ρ e ds ido vs
  matchRounds : ∀ ρ e xs ido i vs, DefsOk bad ρ → GoodEvs bad (evExp e) →
    matchRounds n env ρ e xs ido i vs ⊑ matchRounds n (withRels env r) ρ e xs ido i vs
  matchArg : ∀ ρ a w, DefsOk bad ρ → GoodEvs bad (evArg a) →
    matchArg n env ρ a w ⊑ matchArg n (withRels env r) ρ a w
  matchArgs : ∀ ρ ags ws, DefsOk bad ρ → GoodEvs bad (evArgs ags) → (∀ w ∈ ws, ArgOk bad w) →
    matchArgs n env ρ ags ws ⊑ matchArgs n (withRels env r) ρ ags ws
  callDef : ∀ ρ x ags, DefsOk bad ρ → GoodName bad x → GoodEvs bad (evArgs ags) →
    callDef n env ρ x ags ⊑ callDef n (withRels env r) ρ x ags
  tryClauses : ∀ cs ws, (∀ c ∈ cs, GoodEvs bad (evClause c)) → (∀ w ∈ ws, ArgOk bad w) →
    tryClauses n env cs ws ⊑ tryClauses n (withRels env r) cs ws
  premHolds : ∀ ρ pr, DefsOk bad ρ → GoodEvs bad (evPrem pr) →
    premHolds n env ρ pr ⊑ premHolds n (withRels env r) ρ pr
  premsHold : ∀ ρ prs, DefsOk bad ρ → GoodEvs bad (evPrems prs) →
    premsHold n env ρ prs ⊑ premsHold n (withRels env r) ρ prs
  premIter : ∀ ρ pr it ds, DefsOk bad ρ → GoodEvs bad (evPrem pr) → GoodEvs bad (evIter it) →
    GoodEvs bad (evDoms ds) → premIter n env ρ pr it ds ⊑ premIter n (withRels env r) ρ pr it ds
  premRounds : ∀ ρ pr xvs ido k, DefsOk bad ρ → GoodEvs bad (evPrem pr) →
    premRounds n env ρ pr xvs ido k ⊑ premRounds n (withRels env r) ρ pr xvs ido k

theorem agreeAt_zero : AgreeAt bad env r 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intros; simp only [evalExp, evalExps, evalExpFields, evalArg, evalArgs, evalDoms,
        evalIterE, evalIterList, evalRounds, Sem.pathGet, Sem.pathSet, Sem.patLen, Sem.matchExp,
        Sem.matchDefault, Sem.matchExps, Sem.matchExpFields, Sem.matchIterE, Sem.matchIterList,
        Sem.matchRounds, Sem.matchArg, Sem.matchArgs, Sem.callDef, Sem.tryClauses, Sem.premHolds,
        Sem.premsHold, Sem.premIter, Sem.premRounds]; exact Res.oof_le _)

/-- The clauses `env` finds for a good name are harmless. -/
theorem goodClauses {bad : List String} {env : Env} (hDG : DefsGood bad env) {x : IL.Id}
    (hx : GoodName bad x) {d : DefDef} (hd : env.findDef? x = some d) :
    ∀ c ∈ d.2.2, GoodEvs bad (evClause c) :=
  hDG x d hx hd

theorem agreeAt_succ (hDG : DefsGood bad env) (m : Nat) (ih : AgreeAt bad env r m) : AgreeAt bad env r (m + 1) := by
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
  have DP := defsPres env m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        rsimp hG
        simp only [evalExp]
        refine Res.bind_le (hexp _ _ hD hG.1) fun v₁ => ?_
        cases boolShort op v₁ with
        | none => exact Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
        | some v => exact Res.Le.refl _
    | cmpE op t e₁ e₂ =>
        rsimp hG
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
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | compE e₁ e₂ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | listE es => simp only [evalExp]; exact Res.map_le _ (hexps _ _ hD (goodEvs_exps hG))
    | liftE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | memE e₁ e₂ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | lenE e =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | catE e₁ e₂ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | idxE e₁ e₂ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | sliceE e₁ e₂ e₃ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ => Res.Le.refl _
    | updE e₁ p e₂ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun _ => hps _ _ _ _ hD hG.2.1
    | extE e₁ p e₂ =>
        rsimp hG
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.2) fun _ =>
            Res.bind_le (hpg _ _ _ hD hG.2.1) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.2.1
    | callE x args₀ =>
        rsimp hG
        simp only [evalExp]
        exact hcd _ _ _ hD hG.1 hG.2
    | iterE e₀ it =>
        cases it with
        | mk i ds =>
          rsimp hG
          simp only [evalExp]
          exact hit _ _ _ _ hD hG.1 hG.2.1 hG.2.2
    | cvtE e t₁ t₂ =>
        simp only [evalExp]
        exact Res.bind_le (hexp _ _ hD hG) fun _ => Res.Le.refl _
    | subE e t₁ t₂ =>
        rsimp hG
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
        rsimp hGit
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
        rsimp hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ => Res.Le.refl _
    | sliceP p e₁ e₂ =>
        rsimp hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ => Res.Le.refl _
    | dotP p a =>
        rsimp hG
        simp only [Sem.pathGet]
        exact Res.bind_le (hpg _ _ _ hD hG) fun _ => Res.Le.refl _
  -- `pathSet`
  · intro ρ v p w hD hG
    cases p with
    | rootP => simp only [Sem.pathSet]; exact Res.Le.refl _
    | idxP p e =>
        rsimp hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2) fun _ =>
            Res.bind_le (Res.Le.refl _) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.1
    | sliceP p e₁ e₂ =>
        rsimp hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG.1) fun _ =>
          Res.bind_le (hexp _ _ hD hG.2.1) fun _ =>
            Res.bind_le (hexp _ _ hD hG.2.2) fun _ =>
              Res.bind_le (Res.Le.refl _) fun _ =>
                Res.bind_le (Res.Le.refl _) fun _ =>
                  Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG.1
    | dotP p a =>
        rsimp hG
        simp only [Sem.pathSet]
        exact Res.bind_le (hpg _ _ _ hD hG) fun _ =>
          Res.bind_le (Res.Le.refl _) fun _ => hps _ _ _ _ hD hG
  -- `patLen`
  · intro ρ e hD hG
    cases e
    case listE es => simp only [Sem.patLen]; exact Res.Le.refl _
    case catE e₁ e₂ =>
      rsimp hG
      simp only [Sem.patLen]
      exact Res.bind_le (hpl _ _ hD hG.1) fun _ =>
        Res.bind_le (hpl _ _ hD hG.2) fun _ => Res.Le.refl _
    case iterE e₀ it =>
      cases it with
      | mk i ds =>
          cases i
          case listN eₙ x =>
            rsimp hG
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
      rsimp hG
      simp only [Sem.matchExp]
      have hpair : ∀ a b, (Sem.matchExp m env ρ e₁ a >>= fun ρ' =>
          Sem.matchExp m env ρ' e₂ b) ⊑
          (Sem.matchExp m (withRels env r) ρ e₁ a >>= fun ρ' => Sem.matchExp m (withRels env r) ρ' e₂ b) :=
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
        rsimp hG
        simp only [Sem.matchExp]
        exact hmi _ _ _ _ _ hD hG.1 hG.2.1 hG.2.2
    case cvtE e t₁ t₂ =>
      cases v <;> simp only [Sem.matchExp] <;>
        first
          | exact hmd _ _ _ hD hG
          | exact Res.bind_le (Res.Le.refl _) fun _ => hm _ _ _ hD hG
    case subE e t₁ t₂ =>
      rsimp hG
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
            rsimp hG
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
        rsimp hGit
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
    cases a <;> cases w
    case expA.val e v =>
      simp only [Sem.matchArg]
      by_cases hc : argSubOk env ρ e v = true
      · have hc' : argSubOk (withRels env r) ρ e v = true := hc
        simp only [hc, hc', ↓reduceIte]
        exact hm _ _ _ hD hG
      · have hc' : ¬ argSubOk (withRels env r) ρ e v = true := hc
        simp only [hc, hc', ↓reduceIte, Bool.false_eq_true]
        exact Res.Le.refl _
    all_goals simp only [Sem.matchArg, matchTypV_withRels, matchSymV_withRels]
    all_goals exact Res.Le.refl _
  -- `matchArgs`
  · intro ρ args₀ ws hD hG hW
    cases args₀ with
    | nil => cases ws <;> simp only [Sem.matchArgs] <;> exact Res.Le.refl _
    | cons a args₀ =>
        rsimp hG
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
    refine bind_le_of (Res.Le.refl _) fun d hd => ?_
    have hcl := goodClauses hDG hx' (Res.ofOption_eq_ok.1 hd)
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
            rsimp hc
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
        rsimp hG
        simp only [Sem.premHolds]
        exact Res.bind_le (hexp _ _ hD hG.2) fun _ => hm _ _ _ hD hG.1
    | rulePr x args₀ op e =>
        exact absurd (hG (.ref 0 x) (by simp [evPrem])) (by simp [rfEvB])
    | iterPr pr it =>
        cases it with
        | mk i ds =>
          rsimp hG
          simp only [Sem.premHolds]
          exact hpi _ _ _ _ hD hG.1 hG.2.1 hG.2.2
  -- `premsHold`
  · intro ρ prs hD hG
    simp only [Sem.premsHold]
    exact foldlM_le_of (P := DefsOk bad) prs
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
        rsimp hGit
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

/-- **Relation-free syntax evaluates in `withRels env r` at least as in `env`**, at every fuel. -/
theorem agreeAt (hDG : DefsGood bad env) : ∀ n, AgreeAt bad env r n
  | 0 => agreeAt_zero bad env r
  | n + 1 => agreeAt_succ bad env r hDG n (agreeAt hDG n)

end Silmaril.Wasm.SpecTec.Sim20.RelFree
