module

public import Silmaril.Wasm.Category.Session.Defs

@[expose] public section

/-!
# Export-session languages: results

* `lowerR_valid`, `liftR_valid`: lowering and lifting are valid compilations (realisations).
* `coreEndo_exportEquiv`: an exact arbitrary-profile Binaryen pass (`ArbitraryProfile.EquivPass`)
  conjugated to Core modules by the round trip is an `ExportEquiv Eq` transformation of Core
  modules, at the same arbitrary profile (no determinism assumption), and preserves the export
  observations exactly (`coreEndo_beh_eq`).
* `extraEndo_exportEquiv`, `extraCoreEndo_exportEquiv`: the same for Silmaril's every-profile
  Binaryen stages, on Binaryen IR and on Core modules.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Wasm Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-- Lowering is a valid compilation from Binaryen IR to Core. -/
theorem lowerR_valid (m : BModule) :
    Valid (lowerR P host).conv m (BModule.lower m) :=
  (lowerR P host).valid m

/-- Lifting is a valid compilation from Core to Binaryen IR. -/
theorem liftR_valid (m : Module) :
    Valid (liftR P host).conv m (BModule.lift m) :=
  (liftR P host).valid m

/-- **An exact arbitrary-profile Binaryen pass, conjugated to Core modules, is an export
equivalence of Core modules.** -/
theorem coreEndo_exportEquiv (pass : ArbitraryProfile.EquivPass P (closedHost (H := H)))
    (m : (coreValid P (closedHost (H := H))).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((coreEndo P closedHost (ArbitraryProfile.Compiler.ofEquivPass pass)).run m).val m.val := by
  have h := ArbitraryProfile.Compiler.ofEquivPass_exportEquiv pass
    ((liftValidR P (closedHost (H := H))).prog m)
  have e : (BModule.lift (m.val : Module)).lower = (m.val : Module) := lower_lift m.val
  rw [coreEndo_run]
  exact e ▸ h

/-- Export equivalence of Core modules preserves their export observations exactly. -/
theorem coreSession_beh_eq {a b : Module} (h : ExportEquiv (· = ·) P host a b) :
    (coreSession P host).beh a = (coreSession P host).beh b := by
  have h' : ExportEquiv (· = ·) P host (BModule.lift a).lower (BModule.lift b).lower := by
    rw [lower_lift, lower_lift]
    exact h
  have e := Exe.CompilerPass.exportEquiv_beh_eq h'
  rw [beh_lift, beh_lift] at e
  exact e

/-- The conjugated pass preserves the Core export observations exactly. -/
theorem coreEndo_beh_eq (pass : ArbitraryProfile.EquivPass P (closedHost (H := H)))
    (m : (coreValid P (closedHost (H := H))).Prog) :
    (coreSession P (closedHost (H := H))).beh
        ((coreEndo P closedHost (ArbitraryProfile.Compiler.ofEquivPass pass)).run m).val =
      (coreSession P (closedHost (H := H))).beh m.val :=
  coreSession_beh_eq P closedHost (coreEndo_exportEquiv P pass m)

/-- Silmaril's every-profile stages are export equivalences of Binaryen IR modules at an arbitrary
profile. -/
theorem extraEndo_exportEquiv (stages : List Silmaril.Wasm.Binaryen.Pipeline.ExtraStage)
    (h : ∀ s ∈ stages, s.anyProfile = true) (rounds : Nat)
    (m : (birValid P (closedHost (H := H))).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((extraEndo P stages h rounds).run m).val.lower m.val.lower :=
  ArbitraryProfile.Compiler.ofEquivPass_exportEquiv _ m

/-- **Silmaril's every-profile stages as Core optimizations**: conjugated by the round trip, they
are export equivalences of Core modules at an arbitrary profile. -/
theorem extraCoreEndo_exportEquiv (stages : List Silmaril.Wasm.Binaryen.Pipeline.ExtraStage)
    (h : ∀ s ∈ stages, s.anyProfile = true) (rounds : Nat)
    (m : (coreValid P (closedHost (H := H))).Prog) :
    ExportEquiv (· = ·) P (closedHost (H := H))
      ((coreEndo P closedHost (extraEndo P stages h rounds)).run m).val m.val :=
  coreEndo_exportEquiv P _ m

end Silmaril.Wasm.Category
