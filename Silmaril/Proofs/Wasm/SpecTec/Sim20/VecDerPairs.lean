module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerElse

/-!
# Three ways an earlier rule types alike in `simEnv20T` and `simEnv20V`

`PairSym (simEnv20T B) (simEnv20V B) [] args ri rj` holds for an `otherwise` rule `ri` and an
earlier rule `rj` that pass `pairOkV`, a Boolean check. It is round 7's `Utf8Else.pairOkU` with the
type check of the same-left-hand-side case moved to `vbad20` and no `$utf8` condition (the two
environments evaluate alike everywhere).

* **different atoms** (`ElseAgree.atomSepB`, `pairSym_atomSep`): the left-hand sides end in
  different constructors and never meet; environment-free.
* **the same left-hand side** (`sameOkV`, `pairSym_same`): every quantifier of `rj` has a type off
  `vbad20` (typed alike both ways, `hasTyp_offV_iff`) or is the shared state `z`, which rule `ri`
  types in both environments (`ElseAgree.z_back`, used once per environment).
* **a trap against a code without one** (`pairSym_trap`): as , read in `simEnv20T`
  (`Utf8Else.noTrap_eval20T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SameLhs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (conclAlts ruleConcl)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (evalExp_of)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (AtomSound atomSepB zShapeB hasZB isZState isZState_eq
  z_back trapLhsB noTrapB trapLhs_eval bindParams_nil relFreeB tyEvB goodT_of_all ruleElseB)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (noOptB conclAlts_of_noOpt noTrap_eval20T)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

/-! ## The checks -/

/-- A quantifier whose type is off `vbad20`, or, when `zOk`, the state `z`. -/
def quantOffV (zOk : Bool) : Param → Bool
  | .expP y t => (evTyp t).all (tyEvB vbad20) || (zOk && isZState (.expP y t))
  | _ => true

/-- The same-left-hand-side check. -/
def sameOkV (ri rj : Rule) : Bool :=
  match rj with
  | .ruleD _ qsj _ _ premsj =>
    premsj.all relFreeB && qsj.all (quantOffV (zShapeB ri && zShapeB rj && hasZB ri))

/-- **The pair check.** -/
def pairOkV (atom : Rule → Option MixopS) (ri rj : Rule) : Bool :=
  noOptB ri && noOptB rj &&
    (atomSepB atom ri rj || sameOkV ri rj || (trapLhsB rj && noTrapB ri))

/-- Every `otherwise` rule passes `pairOkV` against every earlier rule. -/
def pairsOkV (atom : Rule → Option MixopS) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i => match rules[i]? with
    | some ri => !ruleElseB ri || (List.range i).all fun j => match rules[j]? with
      | some rj => pairOkV atom ri rj
      | none => true
    | none => true

/-! ## Different atoms -/

/-- **Rules whose left-hand sides end in different constructors never meet.** -/
theorem pairSym_atomSep {e₁ e₂ : Env} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {ps : List Param} {args : List ArgV} {ri rj : Rule} (hoi : noOptB ri = true)
    (hoj : noOptB rj = true) (h : atomSepB atom ri rj = true) :
    PairSym e₁ e₂ ps args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' _ _ _ hei hej hsame
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

/-! ## The same left-hand side -/

/-- One quantifier of `rj` moves from `e` to `e'`, when it is off `vbad20` or the shared `z`. -/
theorem quant_same {e e' : Env}
    (hoff : ∀ ρ t u, ρ.typs = [] → ElseAgree.GoodT vbad20 (evTyp t) → HasTyp e ρ t u → HasTyp e' ρ t u)
    {ri rj : Rule} {nmi qsi opi ei premsi nmj qsj opj ej premsj}
    (hri : ri = .ruleD nmi qsi opi ei premsi) (hrj : rj = .ruleD nmj qsj opj ej premsj)
    {σ σ' : List (IL.Id × Value)} {v w : Value}
    (hq' : QuantsOk e' (VarEnv.empty.bindVals σ) qsi)
    (hei' : EvalExp e' (VarEnv.empty.bindVals σ) ei v)
    (hej' : EvalExp e' (VarEnv.empty.bindVals σ') ej w) (hsame : SameLhs v w)
    {y : IL.Id} {t : Typ} (hy : Param.expP y t ∈ qsj)
    (hqs : qsj.all (quantOffV (zShapeB ri && zShapeB rj && hasZB ri)) = true)
    {u : Value} (hu : (VarEnv.empty.bindVals σ').findVal? y = some u)
    (ht : HasTyp e (VarEnv.empty.bindVals σ') t u) :
    HasTyp e' (VarEnv.empty.bindVals σ') t u := by
  have hqb : (evTyp t).all (tyEvB vbad20) = true ∨ ((zShapeB ri = true ∧ zShapeB rj = true) ∧
      hasZB ri = true) ∧ isZState (.expP y t) = true := by
    simpa only [quantOffV, Bool.or_eq_true, Bool.and_eq_true] using List.all_eq_true.1 hqs _ hy
  rcases hqb with hof | ⟨⟨⟨hzi, hzj⟩, hhz⟩, hz⟩
  · exact hoff _ _ _ rfl (goodT_of_all hof) ht
  · obtain ⟨rfl, rfl⟩ := isZState_eq hz
    exact z_back hri hrj hzi hzj hhz hq' hei' hej' hsame hu

/-- **Rules on the same left-hand side type alike**, when their other quantifiers are off
`vbad20`. -/
theorem pairSym_same {B : Builtins} {args : List ArgV} {ri rj : Rule} (hoi : noOptB ri = true)
    (hoj : noOptB rj = true) (h : sameOkV ri rj = true) :
    PairSym (simEnv20T B) (simEnv20V B) [] args ri rj := by
  rcases hri : ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases hrj : rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' hps hq₁ hq₂ hei hej hsame
  obtain rfl := bindParams_nil hps
  have h₁ : ei' = ei := conclAlts_of_noOpt (by simpa [hri, noOptB, ruleConcl] using hoi) hei'
  have h₂ : ej' = ej := conclAlts_of_noOpt (by simpa [hrj, noOptB, ruleConcl] using hoj) hej'
  subst h₁ h₂
  have h' : premsj.all relFreeB = true ∧
      qsj.all (quantOffV (zShapeB ri && zShapeB rj && hasZB ri)) = true := by
    simpa only [hrj, sameOkV, Bool.and_eq_true] using h
  have hS := envSameTV B
  refine ⟨⟨fun hqj y t hy => ?_, fun hqj y t hy => ?_⟩, h'.1⟩
  · obtain ⟨u, hu, ht⟩ := hqj y t hy
    exact ⟨u, hu, quant_same (fun ρ t u hρ hg h => (hasTyp_offV_iff B hρ hg).2 h)
      hri hrj hq₂ (evalExp_of hS hei) (evalExp_of hS hej) hsame hy h'.2 hu ht⟩
  · obtain ⟨u, hu, ht⟩ := hqj y t hy
    exact ⟨u, hu, quant_same (fun ρ t u hρ hg h => (hasTyp_offV_iff B hρ hg).1 h)
      hri hrj hq₁ hei hej hsame hy h'.2 hu ht⟩

/-! ## A trap against a code without one -/

/-- **A `TRAP` pattern never meets a code without one.** -/
theorem pairSym_trap {B : Builtins} {args : List ArgV} {ri rj : Rule}
    (hoi : noOptB ri = true) (hoj : noOptB rj = true) (h : (trapLhsB rj && noTrapB ri) = true) :
    PairSym (simEnv20T B) (simEnv20V B) [] args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w ei' ej' hei' hej' hps hq _ hei hej hsame
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

/-- **`pairOkV` is sound.** -/
theorem pairSym_of_pairOkV {B : Builtins} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {args : List ArgV} {ri rj : Rule} (h : pairOkV atom ri rj = true) :
    PairSym (simEnv20T B) (simEnv20V B) [] args ri rj := by
  simp only [pairOkV, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hoi, hoj⟩, (h | h) | h⟩ := h
  · exact pairSym_atomSep hA hoi hoj h
  · exact pairSym_same hoi hoj h
  · exact pairSym_trap hoi hoj (by simpa using h)

/-- **`pairsOkV` is sound**: every `otherwise` rule is in `PairSym` with every earlier rule. -/
theorem pairSym_of_pairsOkV {B : Builtins} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {args : List ArgV} {rules : List Rule} (h : pairsOkV atom rules = true) :
    ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj →
      Utf8Else.RuleHasElseB ri → PairSym (simEnv20T B) (simEnv20V B) [] args ri rj := by
  intro i j ri rj hj hi hj' hel
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.1 hi).1
  have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hlt)
  simp only [hi] at h₁
  rw [Utf8Else.ruleElseB_of' hel] at h₁
  simp only [Bool.not_true, Bool.false_or] at h₁
  have h₂ := List.all_eq_true.1 h₁ j (List.mem_range.2 hj)
  simp only [hj'] at h₂
  exact pairSym_of_pairOkV hA h₂

end Silmaril.Wasm.SpecTec.Sim20.VecDer
