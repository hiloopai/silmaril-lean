module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseExp.Reflect

/-!
# Round 9, RE: the four `Expand` pairs (unrefined)

* `fireFwdR`: a rule passing `simpleRuleR` fires on the erased side when it fires on the original
  one, given `PairReflectB` at its own pairs (`ElseBwd.fireFwd_elseRule` with export-free relation
  premises).
* `else_back`: the `otherwise` premise of an earlier rule `j` read backward, from a cover of the
  rules `k < j`: each is, against `i`, outside `elsePairs`, adjacency-clashing, or fires forward
  (`FwdAt`). This is the argument of `ElseBwd.pairReflect_chain` and `pairReflect_chain2`, stated
  once.
* `pairReflect_exp`, `pairReflect_expChain`, `pairReflect_expChain2`: `PairReflectB` along
  `eraseV` at `(101, 100)`, `(102, 100)`, `(102, 101)` and `(92, 91)`.
* `elseBwdBLeft''_of_left3`: `ElseBwd.ElseBwdBLeft''` (9 pairs) from `ElseBwdBLeft3` (5 pairs).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

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
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

/-! ## The kernel check, read at a pair -/

theorem expAll_sub : ∀ p ∈ expPairs ++ expChainPairs ++ expChain2Pairs, p ∈ elsePairs := by
  decide

/-- The kernel check `expPairs_fixed`, read at a pair. -/
theorem expPairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ expPairs ++ expChainPairs ++ expChain2Pairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsRule ri = true ∧
      simpleRuleR rj = true ∧ hasElse ri = true := by
  rw [findRel?_utf8Env] at hrel
  have hmem := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 expPairs_fixed _ hmem
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.1 _ hij
  split at h'
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at h'
    have he := List.all_eq_true.1 elsePairs_fixed _ hmem
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at he
    have hin : (i, j) ∈ elsePairsOf rules := by
      rw [he.1]
      exact expAll_sub _ hij
    obtain ⟨ri', hri', hel⟩ := mem_elsePairsOf_inv hin
    rw [hri] at hri'
    cases hri'
    exact ⟨ri, rj, hri, hrj, h'.1, h'.2, hel⟩
  · cases h'

/-- Rule 100 (`array.init_data-oob2`) has no `otherwise` premise. -/
theorem rule100_noElse {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules)) {nm : IL.Id}
    {qs : List Param} {o : MixopS} {e : Exp} {prems : List Prem}
    (hr : rules[100]? = some (.ruleD nm qs o e prems)) : Prem.elsePr ∉ prems := by
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 expPairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at h
  have h2 := h.2
  rw [hr] at h2
  intro hel
  have h3 : hasElse (.ruleD nm qs o e prems) = true := hasElse_of_mem hel
  simp [h3] at h2

/-- **Rule `k` of `Step_read` fires forward**: wherever it fires on the original side, it fires
at the erased value. -/
def FwdAt (B : Builtins) (ps : List Param) (op : MixopS) (rules : List Rule) (k : Nat) : Prop :=
  ∀ r, rules[k]? = some r → ∀ w,
    RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] k w) ps [] op r w →
    RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] k (eraseV w)) ps [] op r (eraseV w)

/-- **The `otherwise` premise of an earlier rule `j`, backward**, from a cover of the rules
`k < j`. -/
theorem else_back {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    {ri : Rule} {a b c' : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hel : hasElse ri = true) (hji : j < i)
    (hFi : Round8.NxElse.Fired (utf8Env B) "Step_read" [] i (.tuple [a, b]))
    (hcov : ∀ k, k < j →
      (i, k) ∉ elsePairs ∨ (i, k) ∈ adjPairs ∨ FwdAt B ps op rules k) (c : Value)
    (hO : otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [eraseV a, c'])) :
    otherwiseAtB (utf8Env B) "Step_read" [] j (.tuple [a, c]) := by
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
  rcases hcov k hk with hne | had | hfw
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
  · -- rule `k` would fire at the erased left-hand side
    exact hO k hk ps op t rules _ hrel hrk _ ⟨eraseV a, c', eraseV c₂, rfl, rfl⟩ (hfw _ hrk _ hbk)

theorem expChain_cover : ∀ k ∈ List.range 101,
    (102, k) ∉ elsePairs ∨ (102, k) ∈ adjPairs ∨ (102, k) ∈ simplePairs ∨ k = 100 := by
  decide +kernel

theorem expChain2_cover : ∀ k ∈ List.range 91,
    (92, k) ∉ elsePairs ∨ (92, k) ∈ adjPairs ∨ (92, k) ∈ simplePairs ∨ chainOk1 92 k = true := by
  decide +kernel

theorem expAll_lt : ∀ p ∈ expPairs ++ expChainPairs ++ expChain2Pairs, p.2 < p.1 := by decide

section Pairs

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **A rule passing `simpleRuleR` fires forward**, given `PairReflectB` at its own pairs when it
has an `otherwise` premise. -/
theorem fireFwdR {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {k : Nat}
    {nm : IL.Id} {qs : List Param} {opk : MixopS} {e : Exp} {prems : List Prem}
    {D : Interp} {w : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some (.ruleD nm qs opk e prems))
    (hsE : simpleRuleR (.ruleD nm qs opk e prems) = true)
    (hRk : Prem.elsePr ∈ prems → ∀ m, m < k → ∀ rm, rules[m]? = some rm →
      headsDiffer (.ruleD nm qs opk e prems) rm = false →
      PairReflectB (utf8Env B) eraseV "Step_read" [] [] k m)
    (hbody : RuleBodyB (utf8Env B) D (otherwiseAtB (utf8Env B) "Step_read" [] k w) ps [] op
      (.ruleD nm qs opk e prems) w) :
    RuleBodyB (utf8Env B) D (otherwiseAtB (utf8Env B) "Step_read" [] k (eraseV w)) ps [] op
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
  simp only [simpleRuleR, Bool.and_eq_true, List.all_eq_true] at hsE
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
    cases pr with
    | ifPr c₀ =>
      simp only [premR, Bool.and_eq_true] at hspr
      cases hpr _ hp with
      | ifPr h =>
        rw [← Round8.NxDer.eraseScope_inst]
        exact .ifPr (NxClause.ifPr_fwd hD H hrd hrel hrk hq hCE hp hspr.1 h)
    | elsePr =>
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
    | rulePr y args o c₀ =>
      obtain ⟨rfl, hxc, hnx⟩ := premR_rulePr hspr
      cases hpr _ hp with
      | rulePr hav hev hd =>
        obtain ⟨n₀, hn₀⟩ := hev
        rw [← Round8.NxDer.eraseScope_inst]
        exact .rulePr (evalArgs_nil hav)
          ⟨n₀, rulePr_self_fwd hD H hrd hrel hrk hq hCE hp hxc hnx hn₀⟩ hd
    | letPr _ _ => simp [premR] at hspr
    | iterPr _ _ => simp [premR] at hspr

/-- A simple rule fires forward. -/
theorem fwdAt_simple {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i k : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hs : (i, k) ∈ simplePairs) : FwdAt B ps op rules k := by
  intro r hrk w hbk
  obtain ⟨ri', rk', -, hrk', -, hsk⟩ := simplePairs_at hB H hrel hs
  rw [hrk] at hrk'
  cases hrk'
  obtain ⟨nm, qs, o, e, prems⟩ := r
  exact fireFwd_simple hB H hrel hrk hsk hbk

/-- A first-level chain rule whose own pairs are adjacency-clashing or simple fires forward. -/
theorem fwdAt_chain1 {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i k : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hok1 : chainOk1 i k = true) : FwdAt B ps op rules k := by
  intro r hrk w hbk
  obtain ⟨hch, hk2⟩ := chainOk1_spec hok1
  obtain ⟨ri', rk', -, hrk', -, hsk, -⟩ := chainPairs_at hrel hch
  rw [hrk] at hrk'
  cases hrk'
  obtain ⟨nm, qs, o, e, prems⟩ := r
  exact fireFwd_elseRule hB H hrel hrk hsk
    (fun hp m hm rm hrm hd => by
      have hkm := elsePairs_mem hrel hrk (hasElse_of_mem hp) hm hrm hd
      rcases hk2 _ (List.mem_filter.2 ⟨hkm, by simp⟩) with ha | hs
      · exact pairReflectB_adj ha
      · exact pairReflect_simple hB H hs) hbk

/-- Rule 100 (`array.init_data-oob2`) fires forward. -/
theorem fwdAt_100 {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules)) :
    FwdAt B ps op rules 100 := by
  intro r hrk w hbk
  obtain ⟨ri, rj, -, hrj, -, hsj, -⟩ := expPairs_at hrel (i := 101) (j := 100) (by decide)
  rw [hrk] at hrj
  cases hrj
  obtain ⟨nm, qs, o, e, prems⟩ := r
  exact fireFwdR hB H hrel hrk hsj (fun hel => absurd hel (rule100_noElse hrel hrk)) hbk

/-- **The backward firing at an `Expand` pair**, from a cover of the earlier rule's own earlier
rules when it has an `otherwise` premise. -/
theorem pairReflect_ofCover {i j : Nat} (hij : (i, j) ∈ expPairs ++ expChainPairs ++ expChain2Pairs)
    (hcov : ∀ ps op t rules, (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules) →
      ∀ nm qs o e prems, rules[j]? = some (.ruleD nm qs o e prems) → Prem.elsePr ∈ prems →
      ∀ k, k < j → (i, k) ∉ elsePairs ∨ (i, k) ∈ adjPairs ∨ FwdAt B ps op rules k) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj, hel⟩ := expPairs_at hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  exact reflect_coreR hB H hrel hri hr hli hsj hFi
    (fun hp c hO => else_back hrel hri hel (expAll_lt _ hij) hFi (hcov ps op t rules hrel nm qs opj e prems hr hp)
      c hO) hbody

/-- **The backward firing at `(101, 100)` and `(102, 100)`.** -/
theorem pairReflect_exp {i j : Nat} (hij : (i, j) ∈ expPairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  have hj : j = 100 := by
    simp only [expPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
    omega
  subst hj
  exact pairReflect_ofCover hB H (List.mem_append_left _ (List.mem_append_left _ hij))
    fun ps op t rules hrel nm qs o e prems hr hel => absurd hel (rule100_noElse hrel hr)

/-- **The backward firing at `(102, 101)`**: `array.init_data-num` against
`array.init_data-zero`. -/
theorem pairReflect_expChain : PairReflectB (utf8Env B) eraseV "Step_read" [] [] 102 101 :=
  pairReflect_ofCover hB H (by decide) fun ps op t rules hrel _ _ _ _ _ _ _ k hk => by
    rcases expChain_cover k (List.mem_range.2 hk) with h | h | h | rfl
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (fwdAt_simple hB H hrel h))
    · exact .inr (.inr (fwdAt_100 hB H hrel))

/-- **The backward firing at `(92, 91)`**: `array.copy-gt` against `array.copy-le`. -/
theorem pairReflect_expChain2 : PairReflectB (utf8Env B) eraseV "Step_read" [] [] 92 91 :=
  pairReflect_ofCover hB H (by decide) fun ps op t rules hrel _ _ _ _ _ _ _ k hk => by
    rcases expChain2_cover k (List.mem_range.2 hk) with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (fwdAt_simple hB H hrel h))
    · exact .inr (.inr (fwdAt_chain1 hB H hrel h))

/-- **`ElseBwdBLeft''` (9 pairs) from the 5 pairs of `leftPairs3`.** -/
theorem elseBwdBLeft''_of_left3 (hL : ElseBwdBLeft3 (utf8Env B)) :
    ElseBwdBLeft'' (utf8Env B) := by
  intro p hp
  by_cases h1 : p ∈ expPairs
  · exact pairReflect_exp hB H h1
  by_cases h2 : p = (102, 101)
  · subst h2; exact pairReflect_expChain hB H
  by_cases h3 : p = (92, 91)
  · subst h3; exact pairReflect_expChain2 hB H
  have : p ∈ leftPairs3 := by revert hp h1 h2 h3; revert p; decide
  exact hL p this

end Pairs

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
