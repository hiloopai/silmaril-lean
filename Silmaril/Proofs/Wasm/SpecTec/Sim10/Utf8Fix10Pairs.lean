module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Typ

/-!
# Earlier rules read back from `utf8Env10T` to `simEnv10T`

The 1.0 instance 's `Sim20.Utf8Else.pairOkU`, without its third case. The 1.0 script
has no reference types, and the kernel finds that no `otherwise` pair of 1.0's `Step_read` or
`Step_pure` needs the trap case (`Utf8Fix10Task`). So `pairOkN` keeps two cases:

* **different atoms** (`Utf8Else.pairBackU_atomSep`, environment-free);
* **the same left-hand side** (`pairBackU_same10`): every quantifier of the earlier rule has a
  type off the twelve types that reach `name` and free of `$utf8` (typed alike,
  `hasTyp_u10T_iff`), or is the shared state `z`; the conclusion evaluates alike and the
  relation-free premises read back (`premBack_of10`).

`pairBackU_of_pairsOkN`: a relation whose pairs pass `pairsOkN` satisfies the hypothesis of
`Utf8Else.otherwiseAtB_moveU`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (QuantsOk PremW noElse)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evExp evTyp evPrem evPrems)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB ruleConcl)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (hasElseB)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (AtomSound atomSepB zShapeB hasZB isZState isZState_eq
  z_back bindParams_nil relFreeB tyEvB goodT_of_all ruleElseB)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (DefsOk GoodEvs badU20 evFreeB goodEvs_of_all noOptB
  quantOffU sameOkU conclAlts_of_noOpt goodEvs_letPr goodEvs_iterPr evalExp_iff evalDoms_iff
  defsOk_bindVals defsOk_empty goodEvs_prems PremBack PairBackU pairBackU_atomSep RuleHasElseB
  ruleElseB_of')
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

/-! ## The checks -/

/-- **The 1.0 pair check**: `Utf8Else.pairOkU` without the trap case. -/
def pairOkN (atom : Rule → Option MixopS) (ri rj : Rule) : Bool :=
  noOptB ri && noOptB rj && (atomSepB atom ri rj || sameOkU ri rj)

/-- Every `otherwise` rule passes `pairOkN` against every earlier rule. -/
def pairsOkN (atom : Rule → Option MixopS) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i => match rules[i]? with
    | some ri => !ruleElseB ri || (List.range i).all fun j => match rules[j]? with
      | some rj => pairOkN atom ri rj
      | none => true
    | none => true

/-! ## Premises that read back -/

/-- **A relation-free premise that never refers to `$utf8` reads back**, in a scope whose
definition variables avoid `$utf8`. -/
theorem premBack_of10 {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {els els' : Prop}
    {ρ : VarEnv} {pr : Prem}
    (h : PremW (utf8Env10T B) (DDerivesB (utf8Env10T B) noElse) els ρ pr) :
    relFreeB pr = true → GoodEvs "utf8" (evPrem pr) → DefsOk "utf8" ρ →
      (hasElseB pr = true → els → els') →
      PremW (simEnv10T B) (DDerivesB (simEnv10T B) noElse) els' ρ pr := by
  have hS : Sim20.Utf8Mono.EnvExt (simEnv10T B) (utf8Env10T B) "utf8" := envExt10T B hB
  have hC : Silmaril.Wasm.SpecTec.Sim20.Utf8Else.Clean (simEnv10T B) "utf8" := clean10T B
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

/-! ## The same left-hand side -/

/-- **Rules on the same left-hand side read back**, when their other quantifiers are off the
types that reach `name` and off `$utf8`. -/
theorem pairBackU_same10 {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none)
    {args : List ArgV} {ri rj : Rule} (hoi : noOptB ri = true) (hoj : noOptB rj = true)
    (h : sameOkU ri rj = true) : PairBackU (simEnv10T B) (utf8Env10T B) [] args ri rj := by
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
  have hej₁ := (evalExp_iff (envExt10T B hB) (clean10T B) hD (goodEvs_of_all hge)).1 hej
  refine ⟨fun y t hy => ?_, hej₁, fun pr hm els els' hel hp => ?_⟩
  · show ∃ u, (VarEnv.empty.bindVals σ').findVal? y = some u ∧
      HasTyp (simEnv10T B) (VarEnv.empty.bindVals σ') t u
    obtain ⟨u, hu, ht⟩ := hq' y t hy
    have hqb : ((evTyp t).all (tyEvB badU20) = true ∧ (evTyp t).all (evFreeB "utf8") = true) ∨
        ((zShapeB ri = true ∧ zShapeB rj = true) ∧ hasZB ri = true) ∧
          isZState (.expP y t) = true := by
      simpa only [quantOffU, Bool.or_eq_true, Bool.and_eq_true] using
        List.all_eq_true.1 hqs _ hy
    rcases hqb with ⟨hoff, hfree⟩ | ⟨⟨⟨hzi, hzj⟩, hhz⟩, hz⟩
    · exact ⟨u, hu, (hasTyp_u10T_iff hB rfl hD (goodT_of_all hoff) (goodEvs_of_all hfree)).1 ht⟩
    · obtain ⟨rfl, rfl⟩ := isZState_eq hz
      exact ⟨u, hu, z_back hri hrj hzi hzj hhz hq hei hej₁ hsame hu⟩
  · exact premBack_of10 hB hp (List.all_eq_true.1 hrf pr hm)
      (goodEvs_prems (goodEvs_of_all hgp) pr hm) hD hel

/-! ## The pair check -/

/-- **`pairOkN` is sound.** -/
theorem pairBackU_of_pairOkN {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none)
    {atom : Rule → Option MixopS} (hA : AtomSound atom) {args : List ArgV} {ri rj : Rule}
    (h : pairOkN atom ri rj = true) : PairBackU (simEnv10T B) (utf8Env10T B) [] args ri rj := by
  simp only [pairOkN, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hoi, hoj⟩, h | h⟩ := h
  · exact pairBackU_atomSep hA hoi hoj h
  · exact pairBackU_same10 hB hoi hoj h

/-- **`pairsOkN` gives the hypothesis of `otherwiseAtB_moveU`.** -/
theorem pairBackU_of_pairsOkN {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none)
    {atom : Rule → Option MixopS} (hA : AtomSound atom) {args : List ArgV} {rules : List Rule}
    (h : pairsOkN atom rules = true) :
    ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj → RuleHasElseB ri →
      PairBackU (simEnv10T B) (utf8Env10T B) [] args ri rj := by
  intro i j ri rj hj hri hrj hel
  have hi : i < rules.length := (List.getElem?_eq_some_iff.1 hri).1
  have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [hri] at h₁
  simp only [ruleElseB_of' hel, Bool.not_true, Bool.false_or] at h₁
  have h₂ := List.all_eq_true.1 h₁ j (List.mem_range.2 hj)
  rw [hrj] at h₂
  exact pairBackU_of_pairOkN hB hA h₂

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
