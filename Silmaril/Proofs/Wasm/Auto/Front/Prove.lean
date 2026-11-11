module

public import Silmaril.Proofs.Wasm.Auto.Front.Basic
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# The front end: soundness of the proving stage

A `proved` report of `checkRefinesBase` or `checkEquivBase` proves the equivalence (hence the
refinement) at **every** profile, given that the `identical` flag is only set for identical
modules: the identical stage by reflexivity, the function-level stage by
`Silmaril.Wasm.Auto.Bridge.modEquiv_of_fnCheck` and `modEquiv_of_discharged`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Front

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Front
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **A `proved` verdict of the proving stage is an equivalence**, every profile. -/
theorem modEquiv_of_proveStageBase {m₁ m₂ : Module} {j n : Nat}
    (h : (proveStageBase m₁ m₂ j n).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j := by
  unfold proveStageBase at h
  split at h
  · rename_i hc
    exact Bridge.modEquiv_of_fnCheck (Bridge.rel_refl R) hc
  · split at h
    · rename_i gs hgs
      split at h
      · rename_i hd
        exact Bridge.modEquiv_of_discharged (Bridge.rel_refl R) hgs hd
      · simp at h
    · simp at h

/-- **A `proved` report of `checkRefinesBase` proves the equivalence**, hence the refinement, at
every profile (`hid`: the `identical` flag is only set for identical modules). -/
theorem checkRefinesBase_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesBase R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j := by
  unfold checkRefinesBase at h
  split at h
  · rename_i hi
    obtain rfl := hid hi
    exact modEquiv_refl R P impl j
  dsimp only at h
  split at h
  · split at h
    · simp at h
    split at h
    · split at h
      · simp at h
      · simp at h
    · exact modEquiv_of_proveStageBase h R P
  · simp at h

/-- The refinement reading of `checkRefinesBase_proved`. -/
theorem checkRefinesBase_proved_refines {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesBase R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModRefines R.toProp P impl spec j :=
  (checkRefinesBase_proved hid h P).1

/-- **A `proved` report of `checkEquivBase` proves the equivalence**, every profile. -/
theorem checkEquivBase_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquivBase R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j := by
  unfold checkEquivBase at h
  dsimp only at h
  split at h
  · cases R with
    | eq =>
      dsimp only at h
      split at h
      · rename_i hr
        rw [h] at hr
        cases hr
      · rename_i hu _
        rw [h] at hu
        cases hu
    | trap =>
      rename_i hu
      rw [h] at hu
      cases hu
  · exact checkRefinesBase_proved hid h P

end Silmaril.Proofs.Wasm.Auto.Front