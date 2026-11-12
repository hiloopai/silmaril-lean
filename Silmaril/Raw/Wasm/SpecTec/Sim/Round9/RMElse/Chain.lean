module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMElse.Simple

/-!
# Round 9, rm: `otherwise` chains along code erasure (unrefined)

At a chain pair `(i, j)` the earlier rule `j` is itself an `otherwise` rule. `reflect_coreC` reads
it backward given its own `otherwise` premise backward: no rule `k < j` fires at the original
left-hand side `a`, given that none fires at `eraseC a`. For every such `k`, the pair `(i, k)` is
outside `elsePairs` (the heads differ), in `adjPairs` (the adjacency clash), or rule `k` goes
forward along erasure (`fireFwd`):
* a `FiresC.relRead` rule by round 8's `FiresC.ruleBody_erase`;
* a `fwdElse` rule (`table.copy-zero`, `memory.copy-zero`, `array.copy-zero`) by `ruleBody_erase` with its own
  `otherwise` forward (`otherwise_fwd_at`), whose pairs are simple or with `throw_ref-instrs`.

* `pairReflectD_chain`: `PairReflectD` along `eraseC` at the 16 pairs of `chainPairsC` and
  `chain2PairsC`.
* `elseBwdDRest_of_left`: `ElseBwd.ElseBwdDRest` from the 4 pairs of `leftPairsC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps grC gdC)
open Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd (FiredD PairReflectD elsePairs adjPairs)

variable {B : Builtins}

/-- **A firing in a rule body is a typed firing.** -/
theorem firedD_of_body {D : Interp} {els : Prop} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {k : Nat} {nm : IL.Id} {qs : List Param} {opk : MixopS} {e : Exp}
    {prems : List Prem} {w : Value}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some (.ruleD nm qs opk e prems))
    (hbody : Sim.RuleBody (simEnv B) D els ps [] op (.ruleD nm qs opk e prems) w) :
    FiredD (simEnv B) "Step_read" [] k w := by
  obtain ⟨hop, ρ₀, σ, hb, hq, he, -⟩ := hbody
  subst hop
  exact ⟨ps, opk, t, rules, nm, qs, e, prems, ρ₀, σ, hrel, hrk, hb, hq, he⟩

/-- **The declarative `otherwise` of rule `k` goes along code erasure**, given the backward firing
at the pairs `(k, j)` of `elsePairs`. -/
theorem otherwise_fwd_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {k : Nat}
    {rk : Rule} {v : Value} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hk : rules[k]? = some rk) (hel : ElseBwd.hasElse rk = true)
    (hP : ∀ p ∈ elsePairs, p.1 = k → PairReflectD (simEnv B) eraseC "Step_read" [] [] p.1 p.2)
    (hF : FiredD (simEnv B) "Step_read" [] k v)
    (h : Sim.otherwiseAt (simEnv B) "Step_read" [] k v) :
    Sim.otherwiseAt (simEnv B) "Step_read" [] k (eraseC v) := by
  refine ElseBwd.otherwiseAt_map (fun _ _ _ => ElseBwd.eraseC_pair) ElseBwd.vHead_eraseC hF ?_ h
  intro j hj ps' op' t' rules' ri' rj hrel' hi' hrj hd
  rw [hrel] at hrel'
  cases hrel'
  rw [hk] at hi'
  cases hi'
  exact hP (k, j) (ElseBwd.elsePairs_mem_sim hrel hk hel hj hrj hd) rfl

/-- `elseRuleC` at a rule of `elseRead` of `simEnv B`. -/
theorem elseRuleC_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {k : Nat}
    {r : Rule} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some r) (hk : k ∈ elseRead) : elseRuleC r = true := by
  obtain ⟨r', hr', hel⟩ := elseRule_of hk
  rw [rulesOf_eq hrel, hrk, Option.some.injEq] at hr'
  exact hr' ▸ hel

/-- **A `relRead` or `fwdElse` rule's firing goes to the erased side.** -/
theorem fireFwd (H : Hyps QT grC gdC (simEnv B)) {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {k : Nat} {nm : IL.Id} {qs : List Param} {opk : MixopS} {e : Exp}
    {prems : List Prem} {w : Value}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some (.ruleD nm qs opk e prems)) (hk : k ∈ relRead ++ fwdElse)
    (hbody : Sim.RuleBody (simEnv B) (Sim.DDerives (simEnv B) Sim.noElse)
      (Sim.otherwiseAt (simEnv B) "Step_read" [] k w) ps [] op (.ruleD nm qs opk e prems) w) :
    Sim.RuleBody (simEnv B) (Sim.DDerives (simEnv B) Sim.noElse)
      (Sim.otherwiseAt (simEnv B) "Step_read" [] k (eraseC w)) ps [] op
      (.ruleD nm qs opk e prems) (eraseC w) := by
  have hF := firedD_of_body hrel hrk hbody
  have hb' := hbody
  obtain ⟨-, ρ₀, σ, hb, -⟩ := hb'
  obtain ⟨rfl, -⟩ := bindParams_nil hb
  have hq := quants_of_find hrel stepRead_reach (List.mem_of_getElem? hrk)
  rcases List.mem_append.1 hk with hr | hf
  · obtain ⟨r', hr', hrr⟩ := rel_of_relAt relRead_ok hr
    rw [rulesOf_eq hrel, hrk, Option.some.injEq] at hr'
    subst hr'
    have hparts := relRule_parts hrr
    refine ruleBody_erase H hparts.1 hq ?_ ?_ hbody
    · intro pr hpr y op avs w hy hd
      exact dderives_erase H hd (relPrem_rels (hparts.2 pr hpr) y hy)
    · intro pr hpr he
      rw [relPrem_else (hparts.2 pr hpr)] at he
      cases he
  · have hcov := fwdElse_cover k hf
    obtain ⟨hx, hhas, hps⟩ := elseRuleC_parts (elseRuleC_at hrel hrk hcov.1)
    have hP : ∀ p ∈ elsePairs, p.1 = k →
        PairReflectD (simEnv B) eraseC "Step_read" [] [] p.1 p.2 := by
      intro p hp hpk
      obtain ⟨i', j'⟩ := p
      rcases hcov.2 _ hp hpk with ha | hs
      · exact ElseBwd.pairReflectD_adj ha
      · exact pairReflectD_simple H hs
    refine ruleBody_erase H hx hq ?_ ?_ hbody
    · intro pr hpr y op avs w hy hd
      exact dderives_erase H hd (elsePremC_rels (hps pr hpr) y hy)
    · intro _ _ _ hO
      exact otherwise_fwd_at hrel hrk hhas hP hF hO

/-- The cover of a chain pair of either level. -/
theorem chain_coverC {i j : Nat} (hij : (i, j) ∈ chainPairsC ++ chain2PairsC) :
    (i, j) ∈ elsePairs ∧ ∀ k, k < j →
      (i, k) ∉ elsePairs ∨ (i, k) ∈ adjPairs ∨ k ∈ relRead ++ fwdElse := by
  rcases List.mem_append.1 hij with h | h
  · obtain ⟨hm, hc⟩ := chainC_cover _ h
    refine ⟨hm, fun k hk => ?_⟩
    rcases hc k hk with h₁ | h₂ | h₃
    · exact .inl h₁
    · exact .inr (.inl h₂)
    · exact .inr (.inr (List.mem_append_left _ h₃))
  · exact chain2C_cover _ h

/-- **The backward firing at a chain pair (RM).** -/
theorem pairReflectD_chain (H : Hyps QT grC gdC (simEnv B)) {i j : Nat}
    (hij : (i, j) ∈ chainPairsC ++ chain2PairsC) :
    PairReflectD (simEnv B) eraseC "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj⟩ := pairsOk_at chainPairsC_fixed hij
  rw [rulesOf_eq hrel] at hri hrj
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨hmem, hcov⟩ := chain_coverC hij
  obtain ⟨hji, hiel⟩ := elsePairs_lt _ hmem
  have hel : ElseBwd.hasElse ri = true := by
    have h := elseRuleC_at hrel hri hiel
    simp only [elseRuleC, Bool.and_eq_true] at h
    exact h.1.2
  refine reflect_coreC H hrel hri hr hli hsj hFi (fun _ c hO => ?_) hbody
  -- the `otherwise` premise of rule `j`, backward
  rw [Sim.otherwiseAt] at hO ⊢
  intro k hk ps' op' t' rules' rk hrel' hrk w hw hbk
  rw [hrel] at hrel'
  cases hrel'
  obtain ⟨a', b', c₂, hv, rfl⟩ := hw
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, -⟩ := hv
  obtain ⟨ps₁, op₁, t₁, rules₁, nmi, qsi, ei, premsi, ρ₀i, σi, hrel₁, hrulei, -, -, hevi⟩ := hFi
  rw [hrel] at hrel₁
  cases hrel₁
  rw [hrulei] at hri
  cases hri
  obtain ⟨nmk, qsk, opk, ek, premsk⟩ := rk
  rcases hcov k hk with hne | had | hfw
  · -- the heads of `i` and `k` differ
    cases hd : ElseBwd.headsDiffer (.ruleD nmi qsi op ei premsi) (.ruleD nmk qsk opk ek premsk) with
    | false => exact hne (ElseBwd.elsePairs_mem_sim hrel hrulei hel (by omega) hrk hd)
    | true =>
      obtain ⟨-, ρ₂, σ₂, -, -, hevk, -⟩ := hbk
      exact ElseBwd.heads_clash (ε := id) (fun _ => rfl) rfl hevi hevk
        (ElseBwd.headsDiffer_alt hd List.mem_cons_self List.mem_cons_self)
  · -- the adjacency clash
    obtain ⟨ri', rk', hri', hrk', hd⟩ := ElseBwd.adjPairs_at hrel had
    rw [hrulei] at hri'
    cases hri'
    rw [hrk] at hrk'
    cases hrk'
    obtain ⟨-, ρ₂, σ₂, -, -, hevk, -⟩ := hbk
    obtain ⟨hs, o₁, o₂, hh, ha, hn⟩ :=
      ElseBwd.adjDiffer_alt hd List.mem_cons_self List.mem_cons_self
    exact ElseBwd.fire_clash (ε := id) (fun v o u h => ⟨u, h⟩) (fun zv vs => by simp) hh ha hn
      hevi hevk
  · -- rule `k` would fire at the erased left-hand side
    have hf := fireFwd H hrel hrk hfw hbk
    exact hO k hk ps op t rules _ hrel hrk _ ⟨eraseC a, c', eraseC c₂, rfl, rfl⟩ hf

/-- **`ElseBwd.ElseBwdDRest` from the 4 pairs of `leftPairsC`.** -/
theorem elseBwdDRest_of_left (H : Hyps QT grC gdC (simEnv B)) (hL : ElseBwdDLeftC (simEnv B)) :
    ElseBwd.ElseBwdDRest (simEnv B) := by
  intro p hp ha
  obtain ⟨i, j⟩ := p
  rcases pairsC_cover _ hp ha with hs | hc | hc | hl
  · exact pairReflectD_simple H hs
  · exact pairReflectD_chain H (List.mem_append_left _ hc)
  · exact pairReflectD_chain H (List.mem_append_right _ hc)
  · exact hL _ hl

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
