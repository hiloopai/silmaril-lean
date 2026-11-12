module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Simple
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Adj
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.CheckChain

/-!
# Round 9, RE: one level of `otherwise` chains (unrefined)

At a chain pair `(i, j)` the earlier rule `j` is itself an `otherwise` rule (`…-zero`). Reading it
backward (`reflect_core`) needs its own `otherwise` premise read backward: no rule `k < j` fires at
the original left-hand side `a`, given that none fires at `eraseV a`. For every such `k`, the pair
`(i, k)` is outside `elsePairs` (the heads of `i` and `k` differ, so `k` cannot fire at `a`), in
`adjPairs` (the same, by the adjacency clash), or in `simplePairs`; a simple rule `k` that fires at
`a` fires at `eraseV a` (`fireFwd_simple`), which the erased `otherwise` premise excludes.

* `fireFwd_simple`: a simple rule's firing goes to the erased side (forward, under any reading of
  `otherwise`, since it has none).
* `pairReflect_chain`: `PairReflectB` along `eraseV` at the 12 chain pairs.
* `elseBwdBLeft_of_left'`: `ElseBwdBLeft` from the 11 pairs of `leftPairs'`.
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

/-- Every rule `k < j` of a chain pair `(i, j)` is, against `i`, outside `elsePairs`, in
`adjPairs` or in `simplePairs`. -/
theorem chain_cover : ∀ p ∈ chainPairs, p.2 < p.1 ∧ ∀ k, k < p.2 →
    (p.1, k) ∉ elsePairs ∨ (p.1, k) ∈ adjPairs ∨ (p.1, k) ∈ simplePairs := by
  decide +kernel

theorem chainPairs_sub : ∀ p ∈ chainPairs, p ∈ elsePairs := by decide

theorem mem_elsePairsOf_inv {rules : List Rule} {i j : Nat} (h : (i, j) ∈ elsePairsOf rules) :
    ∃ ri, rules[i]? = some ri ∧ hasElse ri = true := by
  simp only [elsePairsOf, List.mem_flatMap, List.mem_range] at h
  obtain ⟨i', -, hi'⟩ := h
  split at hi'
  · rename_i ri hri
    split at hi'
    · rename_i hel
      simp only [List.mem_filterMap, List.mem_range] at hi'
      obtain ⟨j', -, hj'⟩ := hi'
      split at hj'
      · split at hj'
        · cases hj'
        · cases hj'
          exact ⟨ri, hri, hel⟩
      · cases hj'
    · cases hi'
  · cases hi'

/-- The kernel check `chainPairs_fixed`, read at a pair, with `hasElse` of the `otherwise` rule. -/
theorem chainPairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ chainPairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsRule ri = true ∧
      simpleRuleE rj = true ∧ hasElse ri = true := by
  rw [findRel?_utf8Env] at hrel
  have hmem := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 chainPairs_fixed _ hmem
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h
  have h' := h _ hij
  split at h'
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at h'
    have he := List.all_eq_true.1 elsePairs_fixed _ hmem
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at he
    have hin : (i, j) ∈ elsePairsOf rules := by
      rw [he.1]
      exact chainPairs_sub _ hij
    obtain ⟨ri', hri', hel⟩ := mem_elsePairsOf_inv hin
    rw [hri] at hri'
    cases hri'
    exact ⟨ri, rj, hri, hrj, h'.1, h'.2, hel⟩
  · cases h'

section Chain

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **A simple rule's firing goes to the erased side**, under any reading of `otherwise` (it has
no `otherwise` premise). -/
theorem fireFwd_simple {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {k : Nat}
    {nm : IL.Id} {qs : List Param} {opk : MixopS} {e : Exp} {prems : List Prem} {els els' : Prop}
    {D D' : Interp} {w : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some (.ruleD nm qs opk e prems))
    (hs : simpleRule (.ruleD nm qs opk e prems) = true)
    (hbody : RuleBodyB (utf8Env B) D els ps [] op (.ruleD nm qs opk e prems) w) :
    RuleBodyB (utf8Env B) D' els' ps [] op (.ruleD nm qs opk e prems) (eraseV w) := by
  have hrd : reach 0 "Step_read" = true := by decide
  have hsr : Script.stepReach.contains (0, "Step_read") = true := by decide
  have hD := NxFlow.flowSound B hB
  have hF := NxRule.rFacts hrd hrel hrk
  obtain ⟨e', halt, hop, ρ₀, σ, hps, hq, ⟨n, hn⟩, hpr⟩ := hbody
  obtain ⟨-, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
  subst hρ
  obtain ⟨hsE, hne⟩ := simpleRule_parts hB H hs
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
  refine ⟨e', halt, hop, VarEnv.empty, σ.map eraseP, hps, ?_, ⟨n, ?_⟩, fun pr hp => ?_⟩
  · rw [← Round8.NxDer.eraseScope_inst]
    exact Round8.NxTyp.typFwdN_utf8Env hsr hrel hrk hq
  · rw [← Round8.NxDer.eraseScope_inst, NxErase.erase_alt hD H hrd hrel hrk hq hCE halt hxe n, hn]
    rfl
  · have hspr := hsp pr hp
    split at hspr
    case h_3 => cases hspr
    case h_2 => exact absurd hp (hne _ _ _ _ _ rfl)
    rename_i c₀
    simp only [Bool.and_eq_true] at hspr
    cases hpr _ hp with
    | ifPr h =>
      rw [← Round8.NxDer.eraseScope_inst]
      exact .ifPr (NxClause.ifPr_fwd hD H hrd hrel hrk hq hCE hp hspr.1 h)

/-- **The backward firing at a chain pair.** -/
theorem pairReflect_chain {i j : Nat} (hij : (i, j) ∈ chainPairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj, hel⟩ := chainPairs_at hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨hji, hcov⟩ := chain_cover _ hij
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
  rcases hcov k hk with hne | had | hsi
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

/-- **`ElseBwdBLeft` from the 11 pairs of `leftPairs'`.** -/
theorem elseBwdBLeft_of_left' (hL : ElseBwdBLeft' (utf8Env B)) : ElseBwdBLeft (utf8Env B) := by
  intro p hp
  by_cases hc : p ∈ chainPairs
  · exact pairReflect_chain hB H hc
  · have : p ∈ leftPairs' := by revert hp hc; revert p; decide
    exact hL p this

end Chain

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
