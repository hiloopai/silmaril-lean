module

public import Silmaril.Wasm.Auto2.VCLib.Defs
public import Silmaril.Wasm.Auto2.VCGen.Thms
public import Silmaril.WasmSpec.SumTo.Thms
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# Contracts of the VC library: the conditions

The conditions of the library's specifications on the Wasm specification library's programs
(`Silmaril.WasmSpec.{SumTo,Max,Adder}.program`), computed by `vcgen4` and closed by the usual
tactics: `sum_vcs` (loop entry, exit, invariant step, variant step), `max_vcs`, `add_vcs`,
`div10_vcs` (`Silmaril.Wasm.Auto2.VCLib.div10MulhiFunc`, the Granlund–Montgomery identity).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen

theorem triBV_step' {i : BitVec 32} (hi : i ≠ 0) :
    Silmaril.WasmSpec.SumTo.triBV i = Silmaril.WasmSpec.SumTo.triBV (i - 1#32) + i :=
  Silmaril.WasmSpec.SumTo.triBV_step hi

theorem triBV_zero' : Silmaril.WasmSpec.SumTo.triBV (BitVec.ofNat 32 0) = 0 := rfl

set_option maxRecDepth 100000 in
/-- The conditions of `$sum` with the variant `n`. -/
theorem sum_vcs : AllValid sumFns (genFunc sumSpec Silmaril.WasmSpec.SumTo.sumFunc libFuel) := by
  vcgen4 <;> simp only [sumFns]
  · simp
  · rintro ⟨rfl, hi⟩
    simpa [triBV_zero'] using hi
  · rintro ⟨rfl, rfl, h0, hi⟩
    rw [← hi, triBV_step' h0]
    bv_omega
  · rintro ⟨rfl, -, h0, -⟩
    bv_omega

set_option maxRecDepth 100000 in
/-- The conditions of `$max`. -/
theorem max_vcs : AllValid {} (genFunc maxSpec Silmaril.WasmSpec.Max.maxFunc libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- The conditions of `$add`. -/
theorem add_vcs : AllValid {} (genFunc addSpec Silmaril.WasmSpec.Adder.addFunc libFuel) := by
  vcgen4
  all_goals (intros; simp_all)

/-- The Granlund–Montgomery identity in the form of the generator's condition (SSA names
substituted): the identity of `Silmaril.Wasm.Auto.Bridge.div10_bv64` up to
associativity and commutativity. -/
theorem div10_mulhi (x : BitVec 64) :
    (((x >>> 32) * 3435973836#64 + ((x &&& 4294967295#64) * 3435973836#64) >>> 32 +
        ((x >>> 32) * 3435973837#64) >>> 32 +
        (((x &&& 4294967295#64) * 3435973837#64) >>> 32 +
          (((x &&& 4294967295#64) * 3435973836#64) &&& 4294967295#64) +
          (((x >>> 32) * 3435973837#64) &&& 4294967295#64)) >>> 32) >>> 3) = x / 10#64 := by
  refine Eq.trans ?_ (Silmaril.Wasm.Auto.Bridge.div10_bv64 x)
  ac_rfl

set_option maxRecDepth 100000 in
/-- The condition of the multiply-high `div10` (one: the result). -/
theorem div10_vcs : AllValid {} (genFunc div10Spec div10MulhiFunc libFuel) := by
  vcgen4
  rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact div10_mulhi _

end Silmaril.Wasm.Auto2.VCLib
