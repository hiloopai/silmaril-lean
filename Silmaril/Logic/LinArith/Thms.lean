module

public import Silmaril.Proofs.Logic.LinArith.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Farkas certificates: results

Proofs in `Silmaril.Proofs.Logic.LinArith.Basic`, for every ordered field `K`
(`[Field K] [LinearOrder K] [IsStrictOrderedRing K]`, so `ℚ` and `ℝ`):

* **`WRows.IsCert.not_feasible`**: `rs.IsCert → ¬ Feasible K rs.system`;
* **`checkCert_sound`**: `checkCert S y = true → ¬ Feasible K S`, from `WRows.check_sound`
  (`check rs = true → IsCert rs`; variables outside the support have coefficient `0`,
  `comb_eq_zero_of_not_mem`);
* streaming: `Cmd.comb_row`, `Cmd.combB_row`, `Cmd.comb_entry`, `Cmd.combB_entry`,
  `load_append` (how one command changes the weighted sums of `load`).

Tests below: a two-row system `x ≤ 1, -x ≤ -2` with certificate `[1, 1]` is refuted over `ℚ`
and `ℝ`; a three-row system; bogus certificates (wrong combination, negative multiplier,
nonnegative bound sum, wrong length) are rejected.
-/

namespace Silmaril.Logic.LinArith

/-- `x₀ ≤ 1` and `x₀ ≥ 2`. -/
def sys₁ : System := [⟨[(0, 1)], 1⟩, ⟨[(0, -1)], -2⟩]

theorem sys₁_infeasible_rat : ¬ Feasible ℚ sys₁ := checkCert_sound (y := [1, 1]) (by decide)

theorem sys₁_infeasible_real : ¬ Feasible ℝ sys₁ := checkCert_sound (y := [1, 1]) (by decide)

/-- `x₀ + x₁ ≤ 2`, `x₀ ≥ 1`, `x₁ ≥ 2`: the sum of the three rows is `0 ≤ -1`. -/
def sys₂ : System := [⟨[(0, 1), (1, 1)], 2⟩, ⟨[(0, -1)], -1⟩, ⟨[(1, -1)], -2⟩]

theorem sys₂_infeasible : ¬ Feasible ℚ sys₂ := checkCert_sound (y := [1, 1, 1]) (by decide)

/-- Bogus certificates are rejected. -/
theorem bogus_rejected :
    checkCert sys₁ [1, 2] = false ∧ checkCert sys₁ [-1, -1] = false ∧
      checkCert [⟨[(0, 1)], 1⟩, ⟨[(0, -1)], 0⟩] [1, 1] = false ∧ checkCert sys₁ [1] = false ∧
      checkCert sys₂ [2, 1, 1] = false := by
  decide

end Silmaril.Logic.LinArith
