module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Mode
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.CheckR
public import Silmaril.Wasm.SpecTec.Sim.Round7.Transfer.Thms

/-!
# Round 7, determination: scopes of iterated premises, and the facts at one rule

* Binding `ExpFree` rows keeps a scope `ExpFree` on a known set (`efOn_bindVals`); the rows of an
  iterated premise whose domains are known are `ExpFree` (`ef_domSomes`, `ef_iterRows'`).
* `DetFacts`: what the kernel checks `Round7.Determ.detRelsOk_fixed` and
  `Round7.Transfer.relRulesOk_fixed` say about one rule of a reachable relation (`detFacts`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree tyA tyB tyOk goodEvsB goodEvs_of_goodEvsB)
open Round6.Reading (conclAlts)

/-! ## Scopes -/

theorem find?_binds {x : IL.Id} {w : Value} :
    ∀ (xs : List (IL.Id × Value)) (m : Map Value), Map.find? (m.binds xs) x = some w →
      (∃ p ∈ xs, p.2 = w) ∨ Map.find? m x = some w
  | [], m, h => Or.inr h
  | (y, u) :: xs, m, h => by
    have h' : Map.find? ((m.bind y u).binds xs) x = some w := h
    rcases find?_binds xs _ h' with ⟨p, hp, hpw⟩ | hm
    · exact Or.inl ⟨p, List.mem_cons_of_mem _ hp, hpw⟩
    · unfold Map.bind at hm
      split at hm
      · exact Or.inr hm
      · by_cases hyx : y = x
        · subst hyx
          simp only [Map.find?_cons, ↓reduceIte, Option.some.injEq] at hm
          exact Or.inl ⟨(y, u), List.mem_cons_self, hm⟩
        · simp only [Map.find?_cons, hyx, ↓reduceIte] at hm
          exact Or.inr hm

/-- **Binding `ExpFree` rows keeps a scope `ExpFree` on `K`.** -/
theorem efOn_bindVals {ρ : VarEnv} {K : List IL.Id} (hK : EFOn ρ K) {row : List (IL.Id × Value)}
    (hrow : ∀ p ∈ row, ExpFree p.2) : EFOn (ρ.bindVals row) K := by
  intro x hx w hw
  rcases find?_binds row ρ.vals hw with ⟨p, hp, hpw⟩ | hm
  · exact hpw ▸ hrow p hp
  · exact hK x hx w hm

theorem goodXs_of_goodXsB {l : List Ev} (h : goodXsB l = true) : GoodXs l := by
  simp only [goodXsB, Bool.and_eq_true, List.all_eq_true] at h
  intro e he
  refine ⟨goodEvs_of_goodEvsB h.1 e he, fun a ha => ?_⟩
  have := h.2 e he
  subst ha
  simpa using this

/-- **The domains of an iteration over known variables are `ExpFree`.** -/
theorem ef_evalDoms {B : Builtins} (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id}
    {ds : List Dom} {xvs : List (IL.Id × Value)} (hD : DefsOk ρ) (hG : GoodXs (evDoms ds))
    (hK : EFOn ρ K) (hfv : ∀ d ∈ ds, fvIn K (domSrc d) = true)
    (h : EvalDoms (utf8Env B) ρ ds xvs) : ∀ p ∈ xvs, ExpFree p.2 := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp [evalDoms] at hn
  intro p hp
  simp only [evalDoms] at hn
  obtain ⟨d, hd, hfd⟩ := mapM_ok_mem hn p hp
  obtain ⟨u, hu, rfl⟩ := Res.map_eq_ok.1 hfd
  exact ef_eval_on hB hD (goodXs_doms' hG d hd) hK (hfv d hd) ⟨n, hu⟩

theorem ef_domSomes {xvs row : List (IL.Id × Value)} (hx : ∀ p ∈ xvs, ExpFree p.2)
    (h : domSomes xvs = some row) : ∀ p ∈ row, ExpFree p.2 := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := mapM_option_mem h p hp
  have hq2 := hx q hq
  revert hqp hq2
  rcases q with ⟨y, v⟩
  cases v with
  | opt o =>
    cases o with
    | some w =>
      intro hqp hq2
      cases hqp
      exact ef_optSome.1 hq2
    | none => intro hqp; cases hqp
  | _ => intro hqp; cases hqp

theorem ef_rows {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
    (hx : ∀ p ∈ xvs, ExpFree p.2) (h : domLists xvs = some dls) (ido : Option IL.Id) (k : Nat) :
    ∀ r ∈ iterRows dls ido k, ∀ p ∈ r, ExpFree p.2 :=
  ef_iterRows (ef_listDs hx h) ido k

/-! ## The facts at one rule -/

/-- What the kernel checks say about one rule of a reachable relation. -/
structure DetFacts (ps qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  params : ps = []
  goodPrems : ∀ pr ∈ prems, GoodXs (evPrem pr)
  quants : ∀ y t, Param.expP y t ∈ qs → tyOk tyA tyB t = true
  concl : ∀ e' ∈ conclAlts e, GoodXs (evExp e') ∧ (quantNames qs).all (ruleK qs e' prems).contains
    = true ∧ fvIn (ruleK qs e' prems) e' = true ∧
    ∀ pr ∈ prems, premDetOk (ruleK qs e' prems) pr = true

theorem goodXs_prems' {ps : List Prem} (h : GoodXs (evPrems ps)) : ∀ p ∈ ps, GoodXs (evPrem p) :=
  goodXs_prems h

theorem detFacts {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hx : (0, x) ∈ stepReach) (hrel : (simEnv B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) : DetFacts ps qs e prems := by
  have hf := Transfer.ruleFacts hx hrel hrule
  have hm := Transfer.mem_rels_of_findRel hrel
  have hc : stepReach.contains (0, x) = true := by simpa using hx
  have h₁ := List.all_eq_true.1 detRelsOk_fixed _ hm
  simp only [hc, Bool.not_true, Bool.false_or] at h₁
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have h₂ : ruleDetOk (.ruleD nm qs op e prems) = true := List.all_eq_true.1 h₁ _ hr
  simp only [ruleDetOk, Bool.and_eq_true, List.all_eq_true] at h₂
  refine ⟨hf.params, goodXs_prems (goodXs_of_goodXsB h₂.1), hf.quants, fun e' he' => ?_⟩
  obtain ⟨⟨⟨hg, hq⟩, hfv⟩, hp⟩ := h₂.2 e' he'
  exact ⟨goodXs_of_goodXsB hg, List.all_eq_true.2 hq, hfv, hp⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
