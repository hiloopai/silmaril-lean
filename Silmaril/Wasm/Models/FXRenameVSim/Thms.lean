module

public import Silmaril.Proofs.Wasm.Models.FXRenameVSim.Beh

/-!
# Exception renaming for `StepFX'`: `Task.exnRenameBisimFX'` proved

`Task.exnRenameBisimFX'` (`Silmaril.Wasm.Models.FXRenameV`, frozen in ws1 and proved there only on
Core code) asks that host-free `StepFX'` behaviours without FX functions commute with the
renaming `rnIdx n` of exception addresses, over an `ExnRen n` target store and a `KRn n`
renamed continuation store. This module proves it:

* **`stepV_rn`** (forward): every step of `c` is matched by one step of each renamed
  configuration `⟨t, K₂, rnFrame n c.frame, rnL n c.code⟩`, to a renamed configuration of the
  successor (the Core rule by the Core renaming `step_rn`; each FX rule by one lemma);
* **`stepV_rn_back`** (backward): every step of a renamed configuration is the renamed image of
  a step of `c`. Contexts of suspension are read back from renamed code (`rnL_eq_plug_iff`),
  so both splits of `suspend_nondet` are matched;
* **`behavioursV_rn_eq`**, **`exnRenameBisimFX'_holds`**.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- **The forward renaming simulation for `StepFX'`, one step.** -/
theorem stepV_rn {H : Type} {P : Profile} {n : Nat} {c c' : ConfigFX H}
    (hs : StepFX' P noHost noFX c c') {t : Store H} {K₂ : List (Option ContFX)}
    (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    ∃ t' K₂', StepFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n c.code⟩
        ⟨t', K₂', rnFrame n c'.frame, rnL n c'.code⟩ ∧ ExnRen n c'.store t' ∧
      KRn n c'.conts K₂' :=
  Silmaril.Proofs.Wasm.Models.FXRenameVSim.stepV_rn hs h hK

/-- **The backward renaming simulation for `StepFX'`, one step.** -/
theorem stepV_rn_back {H : Type} {P : Profile} {n : Nat} {c : ConfigFX H} {t : Store H}
    {K₂ : List (Option ContFX)} (h : ExnRen n c.store t) (hK : KRn n c.conts K₂)
    {d : ConfigFX H} (hs : StepFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n c.code⟩ d) :
    ∃ (c' : ConfigFX H) (t' : Store H) (K₂' : List (Option ContFX)),
      StepFX' P noHost noFX c c' ∧ d = ⟨t', K₂', rnFrame n c'.frame, rnL n c'.code⟩ ∧
      ExnRen n c'.store t' ∧ KRn n c'.conts K₂' :=
  Silmaril.Proofs.Wasm.Models.FXRenameVSim.stepV_rn_back hs h hK rfl rfl

/-- **The renaming simulation on `StepFX'` behaviours.** -/
theorem behavioursV_rn_eq {H : Type} {P : Profile} {n : Nat} {c : ConfigFX H} {t : Store H}
    {K₂ : List (Option ContFX)} (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    behavioursFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n c.code⟩ =
      rnBeh n '' behavioursFX' P noHost noFX c :=
  Silmaril.Proofs.Wasm.Models.FXRenameVSim.behavioursV_rn_eq h hK

/-- **`Task.exnRenameBisimFX'` holds.** -/
theorem exnRenameBisimFX'_holds : Task.exnRenameBisimFX' :=
  Silmaril.Proofs.Wasm.Models.FXRenameVSim.exnRenameBisimFX'_holds

/--
info: 'Silmaril.Wasm.Models.FXRenameVSim.exnRenameBisimFX'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exnRenameBisimFX'_holds

end Silmaril.Wasm.Models.FXRenameVSim
