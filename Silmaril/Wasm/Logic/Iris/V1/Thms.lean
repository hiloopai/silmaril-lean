module

public import Iris.ProofMode
public import Silmaril.Wasm.Logic.Iris.V1.Defs

/-!
# Wasm Logic proofs in the Iris proof mode

With the `BI HAssert` instance of `Silmaril.Wasm.Logic.Iris.V1.Defs`, the proof mode
(`iintro`, `iframe`, `isplit`, ...) and the generic `BI` lemma library act on
Wasm Logic's heap assertions directly. The unit laws of `HAssert.star` are
instances of the generic `emp_sep`/`sep_symm`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisV1

open _root_.Iris _root_.Iris.BI _root_.Iris.ProofMode Silmaril.Wasm.Execution
open Silmaril.Wasm.Logic.V1

/-- The left unit law, forward, in the proof mode. `HAssert.emp` is not affine, so
it is bound and left unused. -/
example (H : HAssert) : HAssert.emp ∗ H ⊢ H := by
  iintro ⟨_, HH⟩
  iframe

/-- The left unit law, backward. -/
example (H : HAssert) : H ⊢ HAssert.emp ∗ H := by
  iintro HH
  isplitr [HH]
  · iempintro
  · iassumption

/-- The right unit law, forward. -/
example (H : HAssert) : H ∗ HAssert.emp ⊢ H := by
  iintro ⟨HH, _⟩
  iframe
  iassumption

/-- The right unit law, backward. -/
example (H : HAssert) : H ⊢ H ∗ HAssert.emp := by
  iintro HH
  isplitl [HH]
  · iassumption
  · iempintro

/-- The left unit law of `HAssert.star` (`Silmaril.Wasm.Logic.V1.HAssert.emp_star`) is
the generic `BI.emp_sep`. -/
theorem star_emp_left (H : HAssert) : HAssert.star HAssert.emp H = H :=
  BI.equiv_iff.mpr BI.emp_sep

/-- The right unit law of `HAssert.star`, from `BI.emp_sep` and `BI.sep_symm`. -/
theorem star_emp_right (H : HAssert) : HAssert.star H HAssert.emp = H :=
  BI.equiv_iff.mpr ⟨BI.sep_symm.trans BI.emp_sep.mp, BI.emp_sep.mpr.trans BI.sep_symm⟩

/-- Separating conjunction is commutative for any two heap cells: free from `BI.sep_symm`, with
no appeal to `AHeap.Disj`/`AHeap.union_comm` at all. -/
theorem cell_star_comm (a a' : Term Nat) (v v' : Term Memory.Byte) :
    HAssert.cell a v ∗ HAssert.cell a' v' ⊢ HAssert.cell a' v' ∗ HAssert.cell a v := by
  iintro ⟨H1, H2⟩
  iframe

end Silmaril.Wasm.Logic.IrisV1
