module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Vec

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: `Equiv.instrV`

`Equiv.instrV`, the encoding of the scalar, control and index-only instructions, has no atom of
`HStep.hAtoms` except at `call_ref` (`CALL_REF`). The scalar operators are closed values, checked
by `atomsFreeB` and `decide`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.Wasm
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)

/-- **`Equiv.instrV` has no atom of `hAtoms` off `call_ref`.** -/
theorem nh_instrV (i : Instr) (hc : ∀ x, i ≠ .callRef x) : NH (instrV i) := by
  cases i
  case callRef x => exact absurd rfl (hc x)
  case intUnOp t op =>
    cases t <;> cases op <;> (try rename_i p; cases p) <;>
      exact atomsFreeB_sound _ _ (by decide)
  case intBinOp t op =>
    cases t <;> cases op <;> (try rename_i p; cases p) <;>
      exact atomsFreeB_sound _ _ (by decide)
  case intTestOp t op =>
    cases t <;> cases op <;> exact atomsFreeB_sound _ _ (by decide)
  case intRelOp t op =>
    cases t <;> cases op <;> (try rename_i p; cases p) <;>
      exact atomsFreeB_sound _ _ (by decide)
  case floatUnOp t op =>
    cases t <;> cases op <;> exact atomsFreeB_sound _ _ (by decide)
  case floatBinOp t op =>
    cases t <;> cases op <;> exact atomsFreeB_sound _ _ (by decide)
  case floatRelOp t op =>
    cases t <;> cases op <;> exact atomsFreeB_sound _ _ (by decide)
  case convert op =>
    cases op <;> (try rename_i a b c; cases a <;> cases b <;> cases c) <;>
      (try rename_i a; cases a) <;> exact atomsFreeB_sound _ _ (by decide)
  case select ts =>
    cases ts
    · exact atomsFreeB_sound _ _ (by decide)
    · exact trivial
  all_goals first
    | exact trivial
    | exact atomsFreeB_sound _ _ (by decide)
    | (refine nh_case_of ?_ (nh_idx _); decide)
    | (refine nh_case_of ?_ (nh_heapType _); decide)
    | (refine nh_case_of ?_ (nh_case_of ?_ (nh_idx _)) <;> decide)

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
