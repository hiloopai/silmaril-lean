module

public import Silmaril.Wasm.Unified.Versions.Named.Defs
public import Silmaril.Wasm.Models.Syntax.Thms

/-!
# Version signatures inside 3.0: inclusions

* `nsig_sub30`: every named version signature is a sub-signature of `sig30`;
* `nsig_sub`: an inclusion of feature sets is an inclusion of signatures; the version lattice
  `nsub_10_20`, `nsub_20_30`, `nsub_10_lime1`, `nsub_lime1_30`;
* `tableGrow_nsep`: `table.grow` is in 2.0 and not in 1.0.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm.Models Silmaril.Wasm.Unified.Core30

theorem nsig_sub30 (S : FeatureSet) : FSig.Sub (nsig S) sig30 :=
  ⟨fun _ ⟨i, hi, _⟩ => ⟨i, hi⟩, fun _ _ => rfl⟩

theorem nsig_sub {S T : FeatureSet} (h : S ≤ T) : FSig.Sub (nsig S) (nsig T) :=
  ⟨fun _ ⟨i, hi, hs⟩ => ⟨i, hi, headB_mono h i hs⟩, fun _ _ => rfl⟩

theorem nsub_10_20 : FSig.Sub n10 n20 := nsig_sub v10_le_v20
theorem nsub_20_30 : FSig.Sub n20 (nsig v30) := nsig_sub v20_le_v30
theorem nsub_10_lime1 : FSig.Sub n10 nLime1 :=
  nsig_sub (leB_iff.mp (by decide) : v10 ≤ lime1)
theorem nsub_lime1_30 : FSig.Sub nLime1 (nsig v30) := nsig_sub lime1_le_v30

/-- The `table.grow` opcode of the 3.0 signature. -/
def nTableGrow : Opcode := .named "tableGrow" [32]

set_option linter.unusedTactic false in
/-- **`table.grow` separates 2.0 from 1.0.** -/
theorem tableGrow_nsep : nTableGrow ∈ n20.ops ∧ nTableGrow ∉ n10.ops := by
  refine ⟨⟨.tableGrow ⟨0⟩, rfl, by decide⟩, ?_⟩
  rintro ⟨i, hi, hs⟩
  cases i <;> simp_all [head, nTableGrow, Instr.headB]
  all_goals exact absurd hs.1 (by decide)

end Silmaril.Wasm.Unified.Versions
