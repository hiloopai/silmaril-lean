module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEnv

/-!
# Three ways an earlier rule reads back from `utf8Env20T` to `simEnv20T`

`PairBackU (simEnv20T B) (utf8Env20T B) [] args ri rj` holds for an `otherwise` rule `ri` and an
earlier rule `rj` that pass `pairOkU`, a Boolean check. It is round 4's `ElseAgree.pairOkB`, with
the type check of the same-left-hand-side case moved from `tbad20` to `badU20` and two syntactic
conditions added:

* both conclusions have no empty-domain option iteration, so each is its own only alternative
  (`conclAlts_of_noOpt`);
* in the same-left-hand-side case, the conclusion and the premises of `rj` never refer to `$utf8`.

The three cases, each with a soundness lemma:

* **different atoms** (`ElseAgree.atomSepB`, `pairBackU_atomSep`): the two left-hand sides end in
  different constructors and never meet; the argument is environment-free.
* **the same left-hand side** (`sameOkU`, `pairBackU_same`): every quantifier of `rj` either has a
  type off `badU20` that never refers to `$utf8` (typed alike, `hasTyp_u20T_iff`) or is the shared
  state `z` (`ElseAgree.z_back`); the conclusion evaluates alike and the relation-free premises
  read back (`premBack_of`), by `Utf8Else.evalExp_iff`.
* **a trap against a code without one** (`pairBackU_trap`): as , at `simEnv20T`
  (`not_hasTyp_ref_trap20T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SameLhs PremW noElse EvalDoms)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evTyp evPrem evPrems evIterExp evIter evDoms)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB conclAlts hasOptNil ruleConcl)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (hasElseB caseOp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (AtomSound atomSepB zShapeB hasZB isZState isZState_eq
  z_back trapLhsB noTrapB noTrapElB isRefQ isRefQ_eq refCases20 not_hasTyp_variant
  trapLhs_eval evalExps_mem bindParams_nil relFreeB tyEvB GoodT goodT_of_all ruleElseB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T envExt20T)

/-! ## The checks -/

/-- An event that does not refer to the definition `x₀`, as a check. -/
def evFreeB (x₀ : String) : Ev → Bool
  | .ref 1 x => x != x₀
  | _ => true

theorem goodEvs_of_all {x₀ : String} {l : List Ev} (h : l.all (evFreeB x₀) = true) :
    GoodEvs x₀ l := by
  intro e he
  have := List.all_eq_true.1 h e he
  cases e with
  | ref k x =>
    rcases k with _ | _ | k
    · trivial
    · simpa [evFreeB] using this
    · trivial
  | atom => trivial
  | comp => trivial
  | upd => trivial

/-- A conclusion without empty-domain option iterations. -/
def noOptB (r : Rule) : Bool := !hasOptNil (ruleConcl r)

/-- A quantifier whose type is off `badU20` and free of `$utf8`, or, when `zOk`, the state `z`. -/
def quantOffU (zOk : Bool) : Param → Bool
  | .expP y t => ((evTyp t).all (tyEvB badU20) && (evTyp t).all (evFreeB "utf8")) ||
      (zOk && isZState (.expP y t))
  | _ => true

/-- The same-left-hand-side check. -/
def sameOkU (ri rj : Rule) : Bool :=
  match rj with
  | .ruleD _ qsj _ ej premsj =>
    premsj.all relFreeB && (evExp ej).all (evFreeB "utf8") &&
      (evPrems premsj).all (evFreeB "utf8") &&
      qsj.all (quantOffU (zShapeB ri && zShapeB rj && hasZB ri))

/-- **The pair check.** -/
def pairOkU (atom : Rule → Option MixopS) (ri rj : Rule) : Bool :=
  noOptB ri && noOptB rj &&
    (atomSepB atom ri rj || sameOkU ri rj || (trapLhsB rj && noTrapB ri))

/-- Every `otherwise` rule passes `pairOkU` against every earlier rule. -/
def pairsOkU (atom : Rule → Option MixopS) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i => match rules[i]? with
    | some ri => !ruleElseB ri || (List.range i).all fun j => match rules[j]? with
      | some rj => pairOkU atom ri rj
      | none => true
    | none => true

/-- A conclusion without empty-domain option iterations is its own only alternative. -/
theorem conclAlts_of_noOpt {e e' : Exp} (h : hasOptNil e = false) (he : e' ∈ conclAlts e) :
    e' = e := by
  simpa [conclAlts, h] using he

/-! ## Premises that read back -/

theorem goodEvs_letPr {x₀ : String} {a b : Exp} (h : GoodEvs x₀ (evPrem (.letPr a b))) :
    GoodEvs x₀ (evExp a) ∧ GoodEvs x₀ (evExp b) := by
  simpa only [evPrem, goodEvs_append] using h

theorem goodEvs_iterPr {x₀ : String} {pr : Prem} {it : Iter} {ds : List Dom}
    (h : GoodEvs x₀ (evPrem (.iterPr pr (.mk it ds)))) :
    GoodEvs x₀ (evPrem pr) ∧ GoodEvs x₀ (evIter it) ∧ GoodEvs x₀ (evDoms ds) := by
  simpa only [evPrem, evIterExp, goodEvs_append] using h

/-- **A relation-free premise that never refers to `$utf8` reads back**, in a scope whose
definition variables avoid `$utf8`. -/
theorem premBack_of {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {els els' : Prop}
    {ρ : VarEnv} {pr : Prem}
    (h : PremW (utf8Env20T B) (DDerivesB (utf8Env20T B) noElse) els ρ pr) :
    relFreeB pr = true → GoodEvs "utf8" (evPrem pr) → DefsOk "utf8" ρ →
      (hasElseB pr = true → els → els') →
      PremW (simEnv20T B) (DDerivesB (simEnv20T B) noElse) els' ρ pr := by
  have hS : Utf8Mono.EnvExt (simEnv20T B) (utf8Env20T B) "utf8" := envExt20T B hB
  have hC : Clean (simEnv20T B) "utf8" := clean20T B
  induction h with
  | ifPr he =>
    intro _ hG hD _
    exact .ifPr ((evalExp_iff hS hC hD hG).1 he)
  | elsePr h => intro _ _ _ hel; exact .elsePr (hel rfl h)
  | letPr h₁ h₂ =>
    intro _ hG hD _
    exact .letPr ((evalExp_iff hS hC hD (goodEvs_letPr hG).2).1 h₁)
      ((evalExp_iff hS hC hD (goodEvs_letPr hG).1).1 h₂)
  | rulePr => intro hr; exact absurd hr (by simp [relFreeB])
  | iterOptNone hd hne hall =>
    intro _ hG hD _
    exact .iterOptNone ((evalDoms_iff hS hC hD (goodEvs_iterPr hG).2.2).1 hd) hne hall
  | iterOptSome hd hne hs _ ih =>
    intro hr hG hD hel
    exact .iterOptSome ((evalDoms_iff hS hC hD (goodEvs_iterPr hG).2.2).1 hd) hne hs
      (ih hr (goodEvs_iterPr hG).1 (defsOk_bindVals hD _) hel)
  | iterList hit hd hne hdl hlen _ ih =>
    intro hr hG hD hel
    exact .iterList hit ((evalDoms_iff hS hC hD (goodEvs_iterPr hG).2.2).1 hd) hne hdl hlen
      fun r hr' => ih r hr' hr (goodEvs_iterPr hG).1 (defsOk_bindVals hD _) hel
  | iterListN hd hn hk hdl hlen _ ih =>
    intro hr hG hD hel
    exact .iterListN ((evalDoms_iff hS hC hD (goodEvs_iterPr hG).2.2).1 hd)
      ((evalExp_iff hS hC hD (goodEvs_iterPr hG).2.1).1 hn) hk hdl hlen
      fun r hr' => ih r hr' hr (goodEvs_iterPr hG).1 (defsOk_bindVals hD _) hel

/-! ## The three cases -/

/-- **Rules whose left-hand sides end in different constructors never meet.** -/
theorem pairBackU_atomSep {e₁ e₂ : Env} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {ps : List Param} {args : List ArgV} {ri rj : Rule} (hoi : noOptB ri = true)
    (hoj : noOptB rj = true) (h : atomSepB atom ri rj = true) :
    PairBackU e₁ e₂ ps args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' _ _ hei hej hsame _
  exfalso
  have h₁ : ei' = ei := conclAlts_of_noOpt (by simpa [noOptB, ruleConcl] using hoi) hei'
  have h₂ : ej' = ej := conclAlts_of_noOpt (by simpa [noOptB, ruleConcl] using hoj) hej'
  subst h₁ h₂
  unfold atomSepB at h
  split at h
  · rename_i a b ha hb
    obtain ⟨l, r, rfl, hl⟩ := hA _ _ _ _ _ _ _ _ _ ha hei
    obtain ⟨l', r', rfl, hl'⟩ := hA _ _ _ _ _ _ _ _ _ hb hej
    obtain ⟨x, y, z, h₁, h₂⟩ := hsame
    simp only [Value.tuple.injEq, List.cons.injEq] at h₁ h₂
    have hll : l = l' := h₁.1.trans h₂.1.symm
    subst hll
    rw [hl] at hl'
    exact absurd (Option.some.inj hl') (by simpa using h)
  · cases h

/-- **Rules on the same left-hand side read back**, when their other quantifiers are off
`badU20` and `$utf8`. -/
theorem pairBackU_same {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {args : List ArgV}
    {ri rj : Rule} (hoi : noOptB ri = true) (hoj : noOptB rj = true) (h : sameOkU ri rj = true) :
    PairBackU (simEnv20T B) (utf8Env20T B) [] args ri rj := by
  rcases hri : ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases hrj : rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' hps hq hei hej hsame hq'
  obtain rfl := bindParams_nil hps
  have h₁ : ei' = ei := conclAlts_of_noOpt (by simpa [hri, noOptB, ruleConcl] using hoi) hei'
  have h₂ : ej' = ej := conclAlts_of_noOpt (by simpa [hrj, noOptB, ruleConcl] using hoj) hej'
  subst h₁ h₂
  have h' : ((premsj.all relFreeB = true ∧ (evExp ej').all (evFreeB "utf8") = true) ∧
      (evPrems premsj).all (evFreeB "utf8") = true) ∧
      qsj.all (quantOffU (zShapeB ri && zShapeB rj && hasZB ri)) = true := by
    simpa only [hrj, sameOkU, Bool.and_eq_true] using h
  obtain ⟨⟨⟨hrf, hge⟩, hgp⟩, hqs⟩ := h'
  have hD : DefsOk "utf8" (VarEnv.empty.bindVals σ') := defsOk_bindVals defsOk_empty σ'
  have hej₁ := (evalExp_iff (envExt20T B hB) (clean20T B) hD (goodEvs_of_all hge)).1 hej
  refine ⟨fun y t hy => ?_, hej₁, fun pr hm els els' hel hp => ?_⟩
  · show ∃ u, (VarEnv.empty.bindVals σ').findVal? y = some u ∧
      HasTyp (simEnv20T B) (VarEnv.empty.bindVals σ') t u
    obtain ⟨u, hu, ht⟩ := hq' y t hy
    have hqb : ((evTyp t).all (tyEvB badU20) = true ∧ (evTyp t).all (evFreeB "utf8") = true) ∨
        ((zShapeB ri = true ∧ zShapeB rj = true) ∧ hasZB ri = true) ∧
          isZState (.expP y t) = true := by
      simpa only [quantOffU, Bool.or_eq_true, Bool.and_eq_true] using
        List.all_eq_true.1 hqs _ hy
    rcases hqb with ⟨hoff, hfree⟩ | ⟨⟨⟨hzi, hzj⟩, hhz⟩, hz⟩
    · exact ⟨u, hu, (hasTyp_u20T_iff hB rfl hD (goodT_of_all hoff) (goodEvs_of_all hfree)).1 ht⟩
    · obtain ⟨rfl, rfl⟩ := isZState_eq hz
      exact ⟨u, hu, z_back hri hrj hzi hzj hhz hq hei hej₁ hsame hu⟩
  · exact premBack_of hB hp (List.all_eq_true.1 hrf pr hm)
      (goodEvs_prems (goodEvs_of_all hgp) pr hm) hD hel

/-! ## A trap against a code without one -/

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `ref`, as `simEnv20T B` finds it. -/
theorem findTyp_ref20T (B : Builtins) :
    (simEnv20T B).findTyp? "ref" = some ([], [.instD [] [] (.variantT refCases20)]) := rfl

/-- **A typed wasm-2.0 `ref` is not a `TRAP`**, in `simEnv20T`. -/
theorem not_hasTyp_ref_trap20T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {w : Value} :
    ¬ HasTyp (simEnv20T B) ρ (.varT "ref" []) (.case "TRAP" w) :=
  not_hasTyp_variant hρ (findTyp_ref20T B) (by simp [refCases20, caseOp])

/-- An element without a `TRAP` evaluates to a value other than a `TRAP`. -/
theorem noTrapEl_eval20T {B : Builtins} {ρ : VarEnv} (hρ : ρ.typs = []) {qs : List Param}
    {e : Exp} {u : Value} (h : noTrapElB qs e = true) (hq : QuantsOk (simEnv20T B) ρ qs)
    (he : EvalExp (simEnv20T B) ρ e u) (x : Value) : u ≠ .case "TRAP" x := by
  rintro rfl
  unfold noTrapElB at h
  split at h
  · obtain ⟨_, -, hc⟩ := evalExp_caseE_iff.1 he
    obtain ⟨rfl, -⟩ := Value.case.inj hc
    simp at h
  · have hy := evalExp_varE_iff.1 (evalExp_subE_iff.1 he)
    obtain ⟨q, hq', hqy⟩ := List.any_eq_true.1 h
    obtain rfl := isRefQ_eq hqy
    obtain ⟨w, hw, ht⟩ := hq _ _ hq'
    have hwx : w = .case "TRAP" x := Option.some.inj (hw.symm.trans hy)
    exact not_hasTyp_ref_trap20T B hρ (hwx ▸ ht)
  · cases h

/-- A code without a `TRAP` evaluates to a list without one. -/
theorem noTrap_eval20T {B : Builtins} {ρ : VarEnv} (hρ : ρ.typs = []) {nm : IL.Id}
    {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem} {v : Value}
    (h : noTrapB (.ruleD nm qs op e prems) = true) (hq : QuantsOk (simEnv20T B) ρ qs)
    (he : EvalExp (simEnv20T B) ρ e v) :
    ∃ cs r, v = .tuple [.list cs, r] ∧ ∀ x, .case "TRAP" x ∉ cs := by
  unfold noTrapB at h
  split at h
  · rename_i qs' es rhs _ heq
    injection heq with _ hqs _ hee _
    subst hqs hee
    obtain ⟨n, hn⟩ := he
    obtain ⟨m, v₁, v₂, h₁, -, rfl⟩ := Sim.Round7.VDecl.evalExp_tupE2 hn
    obtain ⟨cs, hcs, rfl⟩ := evalExp_listE_iff.1 ⟨m, h₁⟩
    refine ⟨cs, v₂, rfl, fun x hx => ?_⟩
    obtain ⟨e, hm, heu⟩ := evalExps_mem hcs _ hx
    exact noTrapEl_eval20T hρ (List.all_eq_true.1 h e hm) hq heu x rfl
  · cases h

/-- **A `TRAP` pattern never meets a code without one.** -/
theorem pairBackU_trap {B : Builtins} {args : List ArgV} {ri rj : Rule}
    (hoi : noOptB ri = true) (hoj : noOptB rj = true) (h : (trapLhsB rj && noTrapB ri) = true) :
    PairBackU (simEnv20T B) (utf8Env20T B) [] args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' hps hq hei hej hsame _
  exfalso
  obtain rfl := bindParams_nil hps
  have h₁ : ei' = ei := conclAlts_of_noOpt (by simpa [noOptB, ruleConcl] using hoi) hei'
  have h₂ : ej' = ej := conclAlts_of_noOpt (by simpa [noOptB, ruleConcl] using hoj) hej'
  subst h₁ h₂
  simp only [Bool.and_eq_true] at h
  obtain ⟨cs, r, rfl, hno⟩ := noTrap_eval20T rfl h.2 hq hei
  obtain ⟨cs', r', x, rfl, hx⟩ := trapLhs_eval h.1 hej
  obtain ⟨a, b, c, h₁, h₂⟩ := hsame
  simp only [Value.tuple.injEq, List.cons.injEq] at h₁ h₂
  have hl := h₁.1.trans h₂.1.symm
  simp only [Value.list.injEq] at hl
  exact hno x (hl ▸ hx)

/-! ## The pair check -/

/-- **`pairOkU` is sound.** -/
theorem pairBackU_of_pairOkU {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none)
    {atom : Rule → Option MixopS} (hA : AtomSound atom) {args : List ArgV} {ri rj : Rule}
    (h : pairOkU atom ri rj = true) : PairBackU (simEnv20T B) (utf8Env20T B) [] args ri rj := by
  simp only [pairOkU, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hoi, hoj⟩, (h | h) | h⟩ := h
  · exact pairBackU_atomSep hA hoi hoj h
  · exact pairBackU_same hB hoi hoj h
  · exact pairBackU_trap hoi hoj (by simpa using h)

/-- `RuleHasElseB`, as a check. -/
theorem ruleElseB_of' {r : Rule} (h : RuleHasElseB r) : ruleElseB r = true := by
  rcases r with ⟨nm, qs, op, e, prems⟩
  obtain ⟨pr, hm, hp⟩ := h
  simp only [ruleElseB, List.any_eq_true]
  exact ⟨pr, hm, hp⟩

/-- **`pairsOkU` gives the hypothesis of `otherwiseAtB_moveU`.** -/
theorem pairBackU_of_pairsOkU {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none)
    {atom : Rule → Option MixopS} (hA : AtomSound atom) {args : List ArgV} {rules : List Rule}
    (h : pairsOkU atom rules = true) :
    ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj → RuleHasElseB ri →
      PairBackU (simEnv20T B) (utf8Env20T B) [] args ri rj := by
  intro i j ri rj hj hri hrj hel
  have hi : i < rules.length := (List.getElem?_eq_some_iff.1 hri).1
  have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [hri] at h₁
  simp only [ruleElseB_of' hel, Bool.not_true, Bool.false_or] at h₁
  have h₂ := List.all_eq_true.1 h₁ j (List.mem_range.2 hj)
  rw [hrj] at h₂
  exact pairBackU_of_pairOkU hB hA h₂

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
