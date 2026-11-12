module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs

/-!
# Round 9, rm: the kernel checks on the pairs

* `simplePairsC_fixed`: at every pair of `simplePairsC` the `otherwise` rule has a left-hand side
  `lhsRuleC` and the earlier rule is `simpleRuleC`;
* `pairsC_cover`, `chainC_cover`, `chain2C_cover`, `fwdElse_cover` (plain `decide` on the lists):
  the 68 pairs of `ElseBwdDRest` are simple, chain, second-level chain or left; the earlier rules
  of a chain pair are, against its `otherwise` rule, outside `elsePairs`, in `adjPairs`, in
  `FiresC.relRead` (or, one level deeper, in `fwdElse`); and the pairs of a `fwdElse` rule are
  simple or in `adjPairs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Round8.FiresC (rulesOf relRead elseRead)
open ElseBwd (elsePairs adjPairs)

set_option maxRecDepth 100000 in
theorem simplePairsC_fixed : pairsOk simpleRuleC (rulesOf "Step_read") simplePairsC = true := by
  decide +kernel

theorem pairsC_cover : ∀ p ∈ elsePairs, p ∉ adjPairs →
    p ∈ simplePairsC ∨ p ∈ chainPairsC ∨ p ∈ chain2PairsC ∨ p ∈ leftPairsC := by
  decide

theorem chainC_cover : ∀ p ∈ chainPairsC, p ∈ elsePairs ∧ ∀ k, k < p.2 →
    (p.1, k) ∉ elsePairs ∨ (p.1, k) ∈ adjPairs ∨ k ∈ relRead := by
  decide

theorem chain2C_cover : ∀ p ∈ chain2PairsC, p ∈ elsePairs ∧ ∀ k, k < p.2 →
    (p.1, k) ∉ elsePairs ∨ (p.1, k) ∈ adjPairs ∨ k ∈ relRead ++ fwdElse := by
  decide

theorem fwdElse_cover : ∀ k ∈ fwdElse, k ∈ elseRead ∧ ∀ p ∈ elsePairs, p.1 = k →
    p ∈ adjPairs ∨ p ∈ simplePairsC := by
  decide

theorem elsePairs_lt : ∀ p ∈ elsePairs, p.2 < p.1 ∧ p.1 ∈ elseRead := by
  decide

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
