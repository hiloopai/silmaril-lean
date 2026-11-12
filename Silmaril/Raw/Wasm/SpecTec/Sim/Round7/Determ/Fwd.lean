module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Determ.Match

/-!
# Round 7, determination: the evaluator keeps values `ExpFree` (unrefined)

`EvalEF B n`: at fuel `n`, in `utf8Env B`, every member of the evaluator that builds a value
answers an `ExpFree` one, and every member that returns a scope returns an `AllEF` one, provided

* the scope is `AllEF` and its definition variables are `GoodName` (`Round7.Script.DefsOk`);
* the syntax is `GoodXs`: it calls only reachable definitions other than `$utf8`, refers only to
  reachable relations, and uses no `EXPORTS` atom, so no record it builds or updates gets an
  `EXPORTS` field;
* the primitives preserve `ExpFree` (`BuiltinsEF B`).

The clauses `utf8Env B` finds for a `GoodName` are `GoodXs` (`goodXClauses`), and arguments are
matched against them by `MatchEF`. The proof is one case per constructor, the shape of
`Round7.Script.agreeAt_succ`, kept unrefined like it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

/-- Unfold the events of a term into the conjunction of `GoodXs` of its parts. -/
syntax "gxsimp " ident : tactic
macro_rules
  | `(tactic| gxsimp $h) => `(tactic| simp only [evExp, evExps, evOExp, evEFields, evPath,
      evIterExp, evIter, evDoms, evArg, evArgs, evPrem, evPrems, evClause, evRule, goodXs_append,
      goodXs_cons, goodXs_nil, goodX_atom, goodX_comp, goodX_upd, goodX_ref0, goodX_ref1,
      true_and, and_true, and_assoc] at $h:ident)

/-! ## Helpers -/

theorem matchTypV_vals {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : matchTypV env ρ pat t = .ok ρ') : ρ'.vals = ρ.vals := by
  unfold matchTypV at h
  repeat (first | (split at h) | (cases h; rfl) | (cases h))

theorem matchSymV_vals {env : Env} {ρ ρ' : VarEnv} {pat g : Sym}
    (h : matchSymV env ρ pat g = .ok ρ') : ρ'.vals = ρ.vals := by
  unfold matchSymV at h
  repeat (first | (split at h) | (cases h; rfl) | (cases h))

theorem matchArg_allEF {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV}
    (h : AllEF ρ) (hw : ∀ u, w = .val u → ExpFree u) (hm : matchArg n env ρ a w = .ok ρ') :
    AllEF ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact (matchEF env n).matchExp _ _ _ _ h (hw v rfl) hm
    · cases hm
  case typA.typ => exact allEF_of_vals h (matchTypV_vals hm)
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact allEF_of_vals h (matchSymV_vals hm)
  all_goals cases hm

theorem matchArgs_allEF {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, AllEF ρ →
      (∀ u, ArgV.val u ∈ ws → ExpFree u) → matchArgs n env ρ ags ws = .ok ρ' → AllEF ρ'
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
        exact matchArgs_allEF n (matchArg_allEF h (fun u hu => hw u (hu ▸ List.mem_cons_self)) h₁)
          (fun u hu => hw u (List.mem_cons_of_mem _ hu)) h₂

theorem ef_optRow {xvs : List (IL.Id × Value)} {os : List (IL.Id × Option Value)}
    (hx : ∀ p ∈ xvs, ExpFree p.2)
    (h : xvs.mapM (fun p => p.2.asOpt?.map fun o => (p.1, o)) = some os) :
    ∀ p ∈ os.filterMap (fun p => p.2.map fun w => (p.1, w)), ExpFree p.2 := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.1 hp
  obtain ⟨r, hr, hrq⟩ := mapM_option_mem h q hq
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hrq
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hqp
  cases hw
  exact ef_of_asOpt (hx r hr) ho

theorem ef_listDs {xvs : List (IL.Id × Value)} {ds : List (IL.Id × List Value)}
    (hx : ∀ p ∈ xvs, ExpFree p.2)
    (h : xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds) :
    ∀ d ∈ ds, ∀ v ∈ d.2, ExpFree v := by
  intro d hd v hv
  obtain ⟨r, hr, hrd⟩ := mapM_option_mem h d hd
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hrd
  exact ef_of_asList (hx r hr) hl v hv

theorem ef_iterRows {ds : List (IL.Id × List Value)} (hd : ∀ d ∈ ds, ∀ v ∈ d.2, ExpFree v)
    (ido : Option IL.Id) (k : Nat) : ∀ r ∈ iterRows ds ido k, ∀ p ∈ r, ExpFree p.2 := by
  intro r hr p hp
  simp only [iterRows, List.mem_map, List.mem_range] at hr
  obtain ⟨i, _, rfl⟩ := hr
  simp only [iterRow, List.mem_append, List.mem_filterMap, Option.mem_toList,
    Option.map_eq_some_iff] at hp
  rcases hp with ⟨d, hd', v, hv, rfl⟩ | ⟨y, _, rfl⟩
  · exact hd d hd' v (List.mem_of_getElem? hv)
  · exact ef_num _

theorem foldlM_inv {α β : Type} {P : β → Prop} {f : β → α → Res β} :
    ∀ (xs : List α), (∀ b a b', P b → a ∈ xs → f b a = .ok b' → P b') →
      ∀ b b', P b → xs.foldlM f b = .ok b' → P b'
  | [], _, b, b', hb, h => by simp only [List.foldlM_nil] at h; cases h; exact hb
  | x :: xs, hP, b, b', hb, h => by
    simp only [List.foldlM_cons, Res.bind_eq_ok] at h
    obtain ⟨b₁, h₁, h₂⟩ := h
    exact foldlM_inv xs (fun c a c' hc ha => hP c a c' hc (List.mem_cons_of_mem _ ha)) b₁ b'
      (hP b x b₁ hb List.mem_cons_self h₁) h₂

/-! ## The invariant -/

variable (B : Builtins)

/-- **The evaluator keeps values `ExpFree` at fuel `n`**, on harmless syntax and `AllEF` scopes. -/
structure EvalEF (n : Nat) : Prop where
  exp : ∀ ρ e v, AllEF ρ → DefsOk ρ → GoodXs (evExp e) →
    evalExp n (utf8Env B) ρ e = .ok v → ExpFree v
  exps : ∀ ρ es vs, AllEF ρ → DefsOk ρ → (∀ e ∈ es, GoodXs (evExp e)) →
    evalExps n (utf8Env B) ρ es = .ok vs → ∀ v ∈ vs, ExpFree v
  expFields : ∀ ρ fs gs, AllEF ρ → DefsOk ρ → GoodXs (evEFields fs) →
    evalExpFields n (utf8Env B) ρ fs = .ok gs →
      (∀ g ∈ gs, ExpFree g.2) ∧ ∀ g ∈ gs, g.1 ≠ "EXPORTS"
  arg : ∀ ρ a w, AllEF ρ → DefsOk ρ → GoodXs (evArg a) →
    evalArg n (utf8Env B) ρ a = .ok w → ∀ u, w = .val u → ExpFree u
  args : ∀ ρ ags ws, AllEF ρ → DefsOk ρ → GoodXs (evArgs ags) →
    evalArgs n (utf8Env B) ρ ags = .ok ws → ∀ u, ArgV.val u ∈ ws → ExpFree u
  doms : ∀ ρ ds xvs, AllEF ρ → DefsOk ρ → GoodXs (evDoms ds) →
    evalDoms n (utf8Env B) ρ ds = .ok xvs → ∀ p ∈ xvs, ExpFree p.2
  iterE : ∀ ρ e it ds v, AllEF ρ → DefsOk ρ → GoodXs (evExp e) → GoodXs (evIter it) →
    GoodXs (evDoms ds) → evalIterE n (utf8Env B) ρ e it ds = .ok v → ExpFree v
  iterList : ∀ ρ e xvs ido k v, AllEF ρ → DefsOk ρ → GoodXs (evExp e) →
    (∀ p ∈ xvs, ExpFree p.2) → evalIterList n (utf8Env B) ρ e xvs ido k = .ok v → ExpFree v
  rounds : ∀ ρ e rs vs, AllEF ρ → DefsOk ρ → GoodXs (evExp e) →
    (∀ r ∈ rs, ∀ p ∈ r, ExpFree p.2) → evalRounds n (utf8Env B) ρ e rs = .ok vs →
      ∀ v ∈ vs, ExpFree v
  pathGet : ∀ ρ v p u, AllEF ρ → DefsOk ρ → GoodXs (evPath p) → ExpFree v →
    pathGet n (utf8Env B) ρ v p = .ok u → ExpFree u
  pathSet : ∀ ρ v p w u, AllEF ρ → DefsOk ρ → GoodXs (evPath p) → ExpFree v → ExpFree w →
    pathSet n (utf8Env B) ρ v p w = .ok u → ExpFree u
  callDef : ∀ ρ x ags v, AllEF ρ → DefsOk ρ → GoodName x → GoodXs (evArgs ags) →
    callDef n (utf8Env B) ρ x ags = .ok v → ExpFree v
  tryClauses : ∀ cs ws v, (∀ c ∈ cs, GoodXs (evClause c)) → (∀ w ∈ ws, ArgOk w) →
    (∀ u, ArgV.val u ∈ ws → ExpFree u) → tryClauses n (utf8Env B) cs ws = .ok v → ExpFree v
  premHolds : ∀ ρ pr ρ', AllEF ρ → DefsOk ρ → GoodXs (evPrem pr) →
    premHolds n (utf8Env B) ρ pr = .ok ρ' → AllEF ρ'
  premsHold : ∀ ρ prs ρ', AllEF ρ → DefsOk ρ → GoodXs (evPrems prs) →
    premsHold n (utf8Env B) ρ prs = .ok ρ' → AllEF ρ'
  premIter : ∀ ρ pr it ds ρ', AllEF ρ → premIter n (utf8Env B) ρ pr it ds = .ok ρ' → AllEF ρ'
  premRounds : ∀ ρ pr xvs ido k ρ', AllEF ρ →
    premRounds n (utf8Env B) ρ pr xvs ido k = .ok ρ' → AllEF ρ'

theorem evalEF_zero : EvalEF B 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [Sem.evalExp, Sem.evalExps, Sem.evalExpFields, Sem.evalArg, Sem.evalArgs,
      Sem.evalDoms, Sem.evalIterE, Sem.evalIterList, Sem.evalRounds, Sem.pathGet, Sem.pathSet,
      Sem.callDef, Sem.tryClauses, Sem.premHolds, Sem.premsHold, Sem.premIter, Sem.premRounds]

theorem evalEF_succ (hB : BuiltinsEF B) (m : Nat) (ih : EvalEF B m) : EvalEF B (m + 1) := by
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
  have hcd := ih.callDef
  have htc := ih.tryClauses
  have hph := ih.premHolds
  have hphs := ih.premsHold
  have hpi := ih.premIter
  have hpr := ih.premRounds
  have ME := matchEF (utf8Env B) m
  have DP := defsPres (utf8Env B) m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `evalExp`
  · intro ρ e v hρ hD hG h
    cases e with
    | varE x =>
        simp only [Sem.evalExp, Res.ofOption_eq_ok] at h
        exact ef_findVal hρ h
    | boolE b => simp only [Sem.evalExp] at h; cases h; exact ef_bool _
    | numE n => simp only [Sem.evalExp] at h; cases h; exact ef_num _
    | textE t => simp only [Sem.evalExp] at h; cases h; exact .text _
    | unE op t e =>
        simp only [Sem.evalExp, Res.bind_eq_ok] at h
        obtain ⟨_, _, h⟩ := h
        exact ef_unValue h
    | binE op t e₁ e₂ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok] at h
        obtain ⟨v₁, _, h⟩ := h
        cases hb : boolShort op v₁ with
        | some w => simp only [hb] at h; cases h; exact ef_boolShort hb
        | none =>
          simp only [hb, Res.bind_eq_ok] at h
          obtain ⟨_, _, h⟩ := h
          exact ef_binValues h
    | cmpE op t e₁ e₂ =>
        simp only [Sem.evalExp, Res.bind_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        exact ef_cmpValues h
    | tupE es =>
        simp only [Sem.evalExp, Res.map_eq_ok] at h
        obtain ⟨vs, hvs, rfl⟩ := h
        exact ef_tuple.2 (hexps _ _ _ hρ hD (goodXs_exps hG) hvs)
    | projE e i =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u, hu, vs, hvs, h⟩ := h
        split at h
        · exact ef_of_asTuple (hexp _ _ _ hρ hD hG hu) hvs _ (List.mem_of_getElem? h)
        · cases h
    | caseE op e =>
        gxsimp hG
        simp only [Sem.evalExp, Res.map_eq_ok] at h
        obtain ⟨u, hu, rfl⟩ := h
        exact ef_case.2 (hexp _ _ _ hρ hD hG hu)
    | uncaseE e op =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u, hu, ⟨op', w⟩, hc, h⟩ := h
        simp only [Res.assert_eq_ok] at h
        cases h.2
        exact ef_of_asCase (hexp _ _ _ hρ hD hG hu) hc
    | optE eo =>
        cases eo with
        | none => simp only [Sem.evalExp] at h; cases h; exact ef_optNone
        | some e =>
          simp only [evExp, evOExp] at hG
          simp only [Sem.evalExp, Res.map_eq_ok] at h
          obtain ⟨u, hu, rfl⟩ := h
          exact ef_optSome.2 (hexp _ _ _ hρ hD hG hu)
    | theE e =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u, hu, o, ho, h⟩ := h
        subst h
        exact ef_of_asOpt (hexp _ _ _ hρ hD hG hu) ho
    | strE fs =>
        simp only [Sem.evalExp, Res.map_eq_ok] at h
        obtain ⟨gs, hgs, rfl⟩ := h
        obtain ⟨h₁, h₂⟩ := hefs _ _ _ hρ hD hG hgs
        exact .struct h₁ fun p hp hpa => absurd hpa (h₂ p hp)
    | dotE e a =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u, hu, h⟩ := h
        exact ef_field (hexp _ _ _ hρ hD hG.2 hu) h
    | compE e₁ e₂ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := h
        exact ef_comp (hexp _ _ _ hρ hD hG.1 hu₁) (hexp _ _ _ hρ hD hG.2 hu₂) h
    | listE es =>
        simp only [Sem.evalExp, Res.map_eq_ok] at h
        obtain ⟨vs, hvs, rfl⟩ := h
        exact ef_list.2 (hexps _ _ _ hρ hD (goodXs_exps hG) hvs)
    | liftE e =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u, hu, o, ho, h⟩ := h
        cases h
        refine ef_list.2 fun w hw => ?_
        cases o with
        | none => cases hw
        | some w' =>
          simp only [Option.toList_some, List.mem_singleton] at hw
          subst hw
          exact ef_of_asOpt (hexp _ _ _ hρ hD hG hu) ho
    | memE e₁ e₂ =>
        simp only [Sem.evalExp, Res.bind_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        exact ef_memValue h
    | lenE e =>
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨_, _, h⟩ := h
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ef_num _
    | catE e₁ e₂ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := h
        exact ef_cat (hexp _ _ _ hρ hD hG.1 hu₁) (hexp _ _ _ hρ hD hG.2 hu₂) h
    | idxE e₁ e₂ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, _, _, _, _, h⟩ := h
        exact ef_idx (hexp _ _ _ hρ hD hG.1 hu₁) h
    | sliceE e₁ e₂ e₃ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, _, _, _, _, _, _, _, _, h⟩ := h
        exact ef_slice (hexp _ _ _ hρ hD hG.1 hu₁) h
    | updE e₁ p e₂ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok] at h
        obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := h
        exact hps _ _ _ _ _ hρ hD hG.2.1 (hexp _ _ _ hρ hD hG.1 hu₁)
          (hexp _ _ _ hρ hD hG.2.2 hu₂) h
    | extE e₁ p e₂ =>
        gxsimp hG
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, u₂, hu₂, u, hu, u', hu', h⟩ := h
        have e₁' := hexp _ _ _ hρ hD hG.1 hu₁
        exact hps _ _ _ _ _ hρ hD hG.2.1 e₁'
          (ef_cat (hpg _ _ _ _ hρ hD hG.2.1 e₁' hu) (hexp _ _ _ hρ hD hG.2.2 hu₂) hu') h
    | callE x args₀ =>
        gxsimp hG
        simp only [Sem.evalExp] at h
        exact hcd _ _ _ _ hρ hD hG.1 hG.2 h
    | iterE e₀ it =>
        cases it with
        | mk i ds =>
          gxsimp hG
          simp only [Sem.evalExp] at h
          exact hit _ _ _ _ _ hρ hD hG.1 hG.2.1 hG.2.2 h
    | cvtE e t₁ t₂ =>
        simp only [Sem.evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ef_num _
    | subE e t₁ t₂ =>
        gxsimp hG
        simp only [Sem.evalExp] at h
        exact hexp _ _ _ hρ hD hG.1 h
  -- `evalExps`
  · intro ρ es vs hρ hD hG h
    simp only [Sem.evalExps] at h
    intro v hv
    obtain ⟨e, he, hev⟩ := mapM_ok_mem h v hv
    exact hexp _ _ _ hρ hD (hG e he) hev
  -- `evalExpFields`
  · intro ρ fs gs hρ hD hG h
    simp only [Sem.evalExpFields] at h
    have key : ∀ g ∈ gs, ExpFree g.2 ∧ g.1 ≠ "EXPORTS" := by
      intro g hg
      obtain ⟨f, hf, hfg⟩ := mapM_ok_mem h g hg
      cases f with
      | mk a e =>
        obtain ⟨ha, hGe⟩ := goodXs_fields hG a e hf
        simp only [Res.map_eq_ok] at hfg
        obtain ⟨u, hu, rfl⟩ := hfg
        exact ⟨hexp _ _ _ hρ hD hGe hu, ha⟩
    exact ⟨fun g hg => (key g hg).1, fun g hg => (key g hg).2⟩
  -- `evalArg`
  · intro ρ a w hρ hD hG h u hu
    subst hu
    cases a <;> simp only [Sem.evalArg] at h
    case expA e =>
      obtain ⟨u', hu', hw⟩ := Res.map_eq_ok.1 h
      cases hw
      exact hexp _ _ _ hρ hD hG hu'
    all_goals cases h
  -- `evalArgs`
  · intro ρ ags ws hρ hD hG h u hu
    simp only [Sem.evalArgs] at h
    obtain ⟨a, ha, hfa⟩ := mapM_ok_mem h _ hu
    exact harg _ _ _ hρ hD (goodXs_args hG a ha) hfa u rfl
  -- `evalDoms`
  · intro ρ ds xvs hρ hD hG h p hp
    simp only [Sem.evalDoms] at h
    obtain ⟨d, hd, hfd⟩ := mapM_ok_mem h p hp
    obtain ⟨u, hu, rfl⟩ := Res.map_eq_ok.1 hfd
    exact hexp _ _ _ hρ hD (goodXs_doms' hG d hd) hu
  -- `evalIterE`
  · intro ρ e it ds v hρ hD hGe hGit hGds h
    cases it with
    | opt =>
        simp only [Sem.evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, os, hos, h⟩ := h
        have hx := hdoms _ _ _ hρ hD hGds hxvs
        split at h
        · cases h; exact ef_optNone
        · split at h
          · simp only [Res.bind_eq_ok] at h
            obtain ⟨u, hu, h⟩ := h
            cases h
            exact ef_optSome.2 (hexp _ _ _ (allEF_bindVals hρ (ef_optRow hx hos))
              (defsOk_bindVals hD _) hGe hu)
          · cases h
    | list =>
        simp only [Sem.evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, k, _, h⟩ := h
        exact hitl _ _ _ _ _ _ hρ hD hGe (hdoms _ _ _ hρ hD hGds hxvs) h
    | list1 =>
        simp only [Sem.evalIterE, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, k, _, _, h⟩ := h
        exact hitl _ _ _ _ _ _ hρ hD hGe (hdoms _ _ _ hρ hD hGds hxvs) h
    | listN eₙ x =>
        simp only [Sem.evalIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨xvs, hxvs, _, _, _, _, h⟩ := h
        exact hitl _ _ _ _ _ _ hρ hD hGe (hdoms _ _ _ hρ hD hGds hxvs) h
  -- `evalIterList`
  · intro ρ e xvs ido k v hρ hD hGe hx h
    simp only [Sem.evalIterList, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨ds, hds, _, vs, hvs, h⟩ := h
    cases h
    exact ef_list.2 (hrnd _ _ _ _ hρ hD hGe (ef_iterRows (ef_listDs hx hds) ido k) hvs)
  -- `evalRounds`
  · intro ρ e rs vs hρ hD hGe hrs h v hv
    simp only [Sem.evalRounds] at h
    obtain ⟨r, hr, hrv⟩ := mapM_ok_mem h v hv
    exact hexp _ _ _ (allEF_bindVals hρ (hrs r hr)) (defsOk_bindVals hD r) hGe hrv
  -- `pathGet`
  · intro ρ v p u hρ hD hG hv h
    cases p with
    | rootP => simp only [Sem.pathGet] at h; cases h; exact hv
    | idxP p e =>
        gxsimp hG
        simp only [Sem.pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, _, _, _, _, h⟩ := h
        exact ef_idx (hpg _ _ _ _ hρ hD hG.1 hv hu₁) h
    | sliceP p e₁ e₂ =>
        gxsimp hG
        simp only [Sem.pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, _, _, _, _, _, _, _, _, h⟩ := h
        exact ef_slice (hpg _ _ _ _ hρ hD hG.1 hv hu₁) h
    | dotP p a =>
        gxsimp hG
        simp only [Sem.pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, h⟩ := h
        exact ef_field (hpg _ _ _ _ hρ hD hG.2 hv hu₁) h
  -- `pathSet`
  · intro ρ v p w u hρ hD hG hv hw h
    cases p with
    | rootP => simp only [Sem.pathSet] at h; cases h; exact hw
    | idxP p e =>
        gxsimp hG
        simp only [Sem.pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, _, _, _, _, u', hu', h⟩ := h
        exact hps _ _ _ _ _ hρ hD hG.1 hv (ef_setIdx (hpg _ _ _ _ hρ hD hG.1 hv hu₁) hw hu') h
    | sliceP p e₁ e₂ =>
        gxsimp hG
        simp only [Sem.pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, _, _, _, _, _, _, _, _, u', hu', h⟩ := h
        exact hps _ _ _ _ _ hρ hD hG.1 hv (ef_setSlice (hpg _ _ _ _ hρ hD hG.1 hv hu₁) hw hu') h
    | dotP p a =>
        gxsimp hG
        simp only [Sem.pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨u₁, hu₁, u', hu', h⟩ := h
        exact hps _ _ _ _ _ hρ hD hG.2 hv
          (ef_setField hG.1 (hpg _ _ _ _ hρ hD hG.2 hv hu₁) hw hu') h
  -- `callDef`
  · intro ρ x ags v hρ hD hx hG h
    simp only [Sem.callDef, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨argVs, hav, d, hd, h⟩ := h
    have hx' := goodName_resolve hD hx
    have hcl := goodXClauses B hx' hd
    have hW := evalArgs_argOk hD (goodEvs_of_goodXs hG) hav
    have hE := hargs _ _ _ hρ hD hG hav
    rcases elimUndef_eq_ok h with ⟨u, hu, h⟩ | ⟨_, h⟩
    · cases h; exact htc _ _ _ hcl hW hE hu
    · rw [Round7.call_utf8Env_of_ne B hx'.2] at h
      exact hB _ _ _ hE (Res.ofOption_eq_ok.1 h)
  -- `tryClauses`
  · intro cs ws v hcs hW hE h
    cases cs with
    | nil => simp only [Sem.tryClauses] at h; cases h
    | cons c cs =>
        cases c with
        | defD q pats e prems =>
            have hc := hcs _ List.mem_cons_self
            gxsimp hc
            simp only [Sem.tryClauses] at h
            rcases elimUndef_eq_ok h with ⟨ρ₁, h₁, h⟩ | ⟨_, h⟩
            · obtain ⟨ρ₀, h₀, h₁'⟩ := Res.bind_eq_ok.1 h₁
              have hρ₀ := matchArgs_allEF m allEF_empty hE h₀
              have hD₀ := matchArgs_defsOk m defsOk_empty hW h₀
              exact hexp _ _ _ (hphs _ _ _ hρ₀ hD₀ hc.2.2.2 h₁')
                (defsOk_of_defs hD₀ (DP.premsHold _ _ _ h₁')) hc.2.2.1 h
            · exact htc _ _ _ (fun c hc' => hcs c (List.mem_cons_of_mem _ hc')) hW hE h
  -- `premHolds`
  · intro ρ pr ρ' hρ hD hG h
    cases pr with
    | ifPr e =>
        simp only [Sem.premHolds, Res.bind_eq_ok, Res.assert_eq_ok] at h
        obtain ⟨_, _, _, h⟩ := h
        cases h; exact hρ
    | elsePr => simp only [Sem.premHolds] at h; cases h; exact hρ
    | letPr e₁ e₂ =>
        gxsimp hG
        simp only [Sem.premHolds, Res.bind_eq_ok] at h
        obtain ⟨u, hu, h⟩ := h
        exact ME.matchExp _ _ _ _ hρ (hexp _ _ _ hρ hD hG.2 hu) h
    | rulePr x args₀ op e =>
        simp only [Sem.premHolds, Res.bind_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        split at h
        · cases h; exact hρ
        · cases h
    | iterPr pr it =>
        cases it with
        | mk i ds => simp only [Sem.premHolds] at h; exact hpi _ _ _ _ _ hρ h
  -- `premsHold`
  · intro ρ prs ρ' hρ hD hG h
    simp only [Sem.premsHold] at h
    have := foldlM_inv (P := fun ρ => AllEF ρ ∧ DefsOk ρ) prs
      (fun b a b' hb ha hok => ⟨hph _ _ _ hb.1 hb.2 (goodXs_prems hG a ha) hok,
        defsOk_of_defs hb.2 (DP.premHolds _ _ _ hok)⟩) ρ ρ' ⟨hρ, hD⟩ h
    exact this.1
  -- `premIter`
  · intro ρ pr it ds ρ' hρ h
    cases it with
    | opt =>
      simp only [Sem.premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      split at h
      · cases h; exact hρ
      · split at h
        · simp only [Res.bind_eq_ok] at h
          obtain ⟨_, _, h⟩ := h
          cases h; exact hρ
        · cases h
    | list =>
      simp only [Sem.premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      exact hpr _ _ _ _ _ _ hρ h
    | list1 =>
      simp only [Sem.premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      exact hpr _ _ _ _ _ _ hρ h
    | listN eₙ x =>
      simp only [Sem.premIter, Res.bind_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, h⟩ := h
      exact hpr _ _ _ _ _ _ hρ h
  -- `premRounds`
  · intro ρ pr xvs ido k ρ' hρ h
    simp only [Sem.premRounds, Res.bind_eq_ok, Res.assert_eq_ok] at h
    obtain ⟨_, _, _, _, _, h⟩ := h
    cases h; exact hρ

/-- **The evaluator keeps values `ExpFree`**, at every fuel. -/
theorem evalEF (hB : BuiltinsEF B) : ∀ n, EvalEF B n
  | 0 => evalEF_zero B
  | n + 1 => evalEF_succ B hB n (evalEF hB n)

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
