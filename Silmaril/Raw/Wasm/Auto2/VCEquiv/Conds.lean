module

public import Silmaril.Wasm.Auto2.VCEquiv.Defs
public import Silmaril.Wasm.Auto2.VCLib.Thms

/-!
# Equivalence through a shared contract: the conditions of the library's programs (unrefined)

The conditions of `Silmaril.Wasm.Auto2.VCLib.sumSpec` (invariant `acc + triBV n = triBV n₀`,
variant `n`, total correctness) on Binaryen's `-O3` of `sum` (`sumO3Func`) and on the
`do … while` form (`sumDoWhileFunc`, with `sumDoWhileSpec`: the invariant also says `n ≠ 0`),
computed by `vcgen4` and closed by the tactics of
`Silmaril.Proofs.Wasm.Auto2.VCLib.Conds` (`sum_vcs`).

New proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCLib

set_option maxRecDepth 100000 in
/-- The conditions of Binaryen's `-O3` of `$sum`. -/
theorem sumO3_vcs : AllValid sumFns (genFunc sumSpec sumO3Func libFuel) := by
  vcgen4 <;> simp only [sumFns]
  · simp
  · rintro ⟨rfl, rfl, h0, hi⟩
    rw [← hi, triBV_step' h0]
    bv_omega
  · rintro ⟨rfl, -, h0, -⟩
    bv_omega
  · rintro ⟨h0, hi⟩
    simp only [ne_eq, Decidable.not_not] at h0
    subst h0
    simpa [triBV_zero'] using hi

set_option maxRecDepth 100000 in
/-- The conditions of the `do … while` form of `$sum`. -/
theorem sumDoWhile_vcs : AllValid sumFns (genFunc sumDoWhileSpec sumDoWhileFunc libFuel) := by
  vcgen4 <;> simp only [sumFns]
  · intro h0
    simpa using h0
  · rintro ⟨h6, rfl, rfl, ⟨hi, h0⟩, -⟩
    refine ⟨?_, h6⟩
    rw [← hi, triBV_step' h0]
    bv_omega
  · rintro ⟨h6, rfl, -, ⟨-, h0⟩, -⟩
    bv_omega
  · rintro ⟨h6, rfl, rfl, ⟨hi, h0⟩, -⟩
    simp only [ne_eq, Decidable.not_not] at h6
    have h1 : v2 = 1 := by bv_omega
    subst h1
    rw [← hi]
    rfl
  · intro h0
    simp only [ne_eq, Decidable.not_not] at h0
    subst h0
    rfl

end Silmaril.Wasm.Auto2.VCEquiv
