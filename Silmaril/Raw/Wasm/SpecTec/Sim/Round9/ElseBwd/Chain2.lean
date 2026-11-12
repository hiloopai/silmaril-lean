module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Chain

/-!
# Round 9, RE: two levels of `otherwise` chains (unrefined)

At `table.copy-gt` and `memory.copy-gt` against `…-le` (`chain2Pairs`), the `…-le` rule's own
earlier rules include the `…-zero` rule, a chain rule of the first level. That rule's firing goes
forward (`fireFwd_elseRule`): its `otherwise` premise goes forward by `otherwiseAtB_map`, given the
backward firing at its own pairs, which are all adjacency-clashing or simple.

* `fireFwd_elseRule`: a rule passing `simpleRuleE` fires on the erased side when it fires on the
  original one, given `PairReflectB` at its pairs.
* `pairReflect_chain2`: `PairReflectB` along `eraseV` at the 2 pairs of `chain2Pairs`.
* `elseBwdBLeft'_of_left''`: `ElseBwdBLeft'` from the 9 pairs of `leftPairs''`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

/-- The second-level chain rules: first-level chain rules whose own pairs are adjacency-clashing or
simple. -/
def chainOk1 (i k : Nat) : Bool :=
  (i, k) ∈ chainPairs && (elsePairs.filter (·.1 == k)).all fun q => q ∈ adjPairs || q ∈ simplePairs

theorem chainOk1_spec {i k : Nat} (h : chainOk1 i k = true) :
    (i, k) ∈ chainPairs ∧ ∀ q ∈ elsePairs.filter (·.1 == k), q ∈ adjPairs ∨ q ∈ simplePairs := by
  simp only [chainOk1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    at h
  exact h

/-- Every rule `k < j` of a pair `(i, j)` of `chain2Pairs` is, against `i`, outside `elsePairs`,
in `adjPairs`, in `simplePairs`, or a first-level chain rule whose own pairs are in `adjPairs` or
`simplePairs`. -/
theorem chain2_cover : ∀ p ∈ chain2Pairs, p.2 < p.1 ∧ ∀ k, k < p.2 →
    (p.1, k) ∉ elsePairs ∨ (p.1, k) ∈ adjPairs ∨ (p.1, k) ∈ simplePairs ∨
      chainOk1 p.1 k = true := by
  decide +kernel

theorem chain2Pairs_sub : ∀ p ∈ chain2Pairs, p ∈ elsePairs := by decide

/-- The kernel check `chain2Pairs_fixed`, read at a pair, with `hasElse` of the `otherwise`
rule. -/
theorem chain2Pairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ chain2Pairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsRule ri = true ∧
      simpleRuleE rj = true ∧ hasElse ri = true := by
  rw [findRel?_utf8Env] at hrel
  have hmem := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 chain2Pairs_fixed _ hmem
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h
  have h' := h _ hij
  split at h'
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at h'
    have he := List.all_eq_true.1 elsePairs_fixed _ hmem
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at he
    have hin : (i, j) ∈ elsePairsOf rules := by
      rw [he.1]
      exact chain2Pairs_sub _ hij
    obtain ⟨ri', hri', hel⟩ := mem_elsePairsOf_inv hin
    rw [hri] at hri'
    cases hri'
    exact ⟨ri, rj, hri, hrj, h'.1, h'.2, hel⟩
  · cases h'

section Chain2

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

theorem fireFwd_elseRule {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {k : Nat}
    {nm : IL.Id} {qs : List Param} {opk : MixopS} {e : Exp} {prems : List Prem}
    {D D' : Interp} {w : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some (.ruleD nm qs opk e prems))
    (hsE : simpleRuleE (.ruleD nm qs opk e prems) = true)
    (hRk : Prem.elsePr ∈ prems → ∀ m, m < k → ∀ rm, rules[m]? = some rm →
      headsDiffer (.ruleD nm qs opk e prems) rm = false →
      PairReflectB (utf8Env B) eraseV "Step_read" [] [] k m)
    (hbody : RuleBodyB (utf8Env B) D (otherwiseAtB (utf8Env B) "Step_read" [] k w) ps [] op
      (.ruleD nm qs opk e prems) w) :
    RuleBodyB (utf8Env B) D' (otherwiseAtB (utf8Env B) "Step_read" [] k (eraseV w)) ps [] op
      (.ruleD nm qs opk e prems) (eraseV w) := by
  have hrd : reach 0 "Step_read" = true := by decide
  have hsr : Script.stepReach.contains (0, "Step_read") = true := by decide
  have hD := NxFlow.flowSound B hB
  have hF := NxRule.rFacts hrd hrel hrk
  obtain ⟨e', halt, hop, ρ₀, σ, hps, hq, ⟨n, hn⟩, hpr⟩ := hbody
  obtain ⟨-, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
  subst hρ
  subst hop
  have hrk' := hrk
  simp only [simpleRuleE, Bool.and_eq_true, List.all_eq_true] at hsE
  obtain ⟨hsc, hsp⟩ := hsE
  have hsc' := hsc e' halt
  split at hsc'
  case h_2 => cases hsc'
  simp only [Bool.and_eq_true] at hsc'
  obtain ⟨-, hxe⟩ := hsc'
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  refine ⟨e', halt, rfl, VarEnv.empty, σ.map eraseP, hps, ?_, ⟨n, ?_⟩, fun pr hp => ?_⟩
  · rw [← Round8.NxDer.eraseScope_inst]
    exact Round8.NxTyp.typFwdN_utf8Env hsr hrel hrk hq
  · rw [← Round8.NxDer.eraseScope_inst, NxErase.erase_alt hD H hrd hrel hrk hq hCE halt hxe n, hn]
    rfl
  · have hspr := hsp pr hp
    split at hspr
    case h_3 => cases hspr
    case h_2 =>
      cases hpr _ hp with
      | elsePr h =>
        have hFk : Round8.NxElse.Fired (utf8Env B) "Step_read" [] k w :=
          ⟨ps, _, t, rules, nm, qs, e, prems, e', VarEnv.empty, σ, hrel, hrk', elseIn_of_mem hp,
            halt, hps, hq, ⟨n, hn⟩⟩
        refine .elsePr (otherwiseAtB_map (fun _ _ _ => eraseV_pair) vHead_eraseV hFk ?_ h)
        intro m hm ps₂ op₂ t₂ rules₂ ri rm hrel₂ hri hrm hd
        rw [hrel] at hrel₂
        cases hrel₂
        rw [hrk'] at hri
        cases hri
        exact hRk hp m hm rm hrm hd
    rename_i c₀
    simp only [Bool.and_eq_true] at hspr
    cases hpr _ hp with
    | ifPr h =>
      rw [← Round8.NxDer.eraseScope_inst]
      exact .ifPr (NxClause.ifPr_fwd hD H hrd hrel hrk hq hCE hp hspr.1 h)

/-- **The backward firing at a chain pair of the second level.** -/
theorem pairReflect_chain2 {i j : Nat} (hij : (i, j) ∈ chain2Pairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj, hel⟩ := chain2Pairs_at hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨hji, hcov⟩ := chain2_cover _ hij
  refine reflect_core hB H hrel hri hr hli hsj hFi (fun _ c hO => ?_) hbody
  -- the `otherwise` premise of rule `j`, backward
  rw [otherwiseAtB] at hO ⊢
  intro k hk ps' op' t' rules' rk hrel' hrk w hw hbk
  rw [hrel] at hrel'
  cases hrel'
  obtain ⟨a', b', c₂, hv, rfl⟩ := hw
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, -⟩ := hv
  obtain ⟨ps₁, op₁, t₁, rules₁, nmi, qsi, ei, premsi, ei', ρ₀i, σi, hrel₁, hrulei, -, halti, -,
    -, hevi⟩ := hFi
  rw [hrel] at hrel₁
  cases hrel₁
  rw [hrulei] at hri
  cases hri
  obtain ⟨nmk, qsk, opk, ek, premsk⟩ := rk
  rcases hcov k hk with hne | had | hsi | hok1
  rotate_left 3
  obtain ⟨hch, hk2⟩ := chainOk1_spec hok1
  rotate_left 1
  · -- the heads of `i` and `k` differ
    cases hd : headsDiffer (.ruleD nmi qsi op ei premsi) (.ruleD nmk qsk opk ek premsk) with
    | false => exact hne (elsePairs_mem hrel hrulei hel (by omega) hrk hd)
    | true =>
      obtain ⟨ek', haltk, -, ρ₂, σ₂, -, -, hevk, -⟩ := hbk
      exact heads_clash (ε := id) (fun _ => rfl) rfl hevi hevk (headsDiffer_alt hd halti haltk)
  · -- the adjacency clash
    obtain ⟨ri', rk', hri', hrk', hd⟩ := adjPairs_at (by rw [← findRel?_utf8Env]; exact hrel) had
    rw [hrulei] at hri'
    cases hri'
    rw [hrk] at hrk'
    cases hrk'
    obtain ⟨ek', haltk, -, ρ₂, σ₂, -, -, hevk, -⟩ := hbk
    obtain ⟨hs, o₁, o₂, hh, ha, hn⟩ := adjDiffer_alt hd halti haltk
    exact fire_clash (ε := id) (fun v o u h => ⟨u, h⟩) (fun zv vs => by simp) hh ha hn hevi hevk
  · -- a simple rule: it would fire at the erased left-hand side
    obtain ⟨ri', rk', hri', hrk', -, hsk⟩ := simplePairs_at hB H hrel hsi
    rw [hrk] at hrk'
    cases hrk'
    have hf := fireFwd_simple hB H (D' := DDerivesB (utf8Env B) Sim.noElse)
      (els' := otherwiseAtB (utf8Env B) "Step_read" [] k (.tuple [eraseV a, eraseV c₂]))
      hrel hrk hsk hbk
    exact hO k hk ps op t rules _ hrel hrk _ ⟨eraseV a, c', eraseV c₂, rfl, rfl⟩ hf
  · -- a first-level chain rule: it would fire at the erased left-hand side
    obtain ⟨ri', rk', hri', hrk', -, hsk, -⟩ := chainPairs_at hrel hch
    rw [hrk] at hrk'
    cases hrk'
    have hf := fireFwd_elseRule hB H (D' := DDerivesB (utf8Env B) Sim.noElse) hrel hrk hsk
      (fun hp m hm rm hrm hd => by
        have hkm := elsePairs_mem hrel hrk (hasElse_of_mem hp) hm hrm hd
        rcases hk2 _ (List.mem_filter.2 ⟨hkm, by simp⟩) with ha | hs
        · exact pairReflectB_adj ha
        · exact pairReflect_simple hB H hs) hbk
    exact hO k hk ps op t rules _ hrel hrk _ ⟨eraseV a, c', eraseV c₂, rfl, rfl⟩ hf

/-- **`ElseBwdBLeft'` from the 9 pairs of `leftPairs''`.** -/
theorem elseBwdBLeft'_of_left'' (hL : ElseBwdBLeft'' (utf8Env B)) : ElseBwdBLeft' (utf8Env B) := by
  intro p hp
  by_cases hc : p ∈ chain2Pairs
  · exact pairReflect_chain2 hB H hc
  · have : p ∈ leftPairs'' := by revert hp hc; revert p; decide
    exact hL p this

end Chain2

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
