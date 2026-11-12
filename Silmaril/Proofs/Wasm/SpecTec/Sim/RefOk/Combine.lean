module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefOk.Assembly
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms

/-!
# Track refok, combined with track configok

Track configok (`origin/spectec-sim3-configok`, merged here) discharges `Residue.result`,
`Residue.funcinst`, `Extra.mem`, `Extra.inst` and `BwdOpen.exnFields` in every `simEnv B`, and
refutes `Prims.TypeTyping` (hence `Residue`) and `Aggregates.AggTypes` (hence `Extra`) as
stated. Together with this track's `instReftype` and `grow`:

* `residueRest_of_core`, `extraRest_of_agg`: of `Residue` only `ResidueCore` (`types`,
  `valtypes`, `refOk`) is left, and of `Extra` only `agg`;
* `wholeStepBounded_of_core`: `Integrate.Task.wholeStepBounded` from `ResidueCore`, `AggTypes`,
  `BwdOpen.remaining` and the forward direction outside the fragment;
* `not_residueCore`, `not_aggTypes'`: both remaining typing bundles are refuted as stated, so the
  premise of `wholeStepBounded_of_core` is (formally) unsatisfiable; the bundles need restating
  (to the encodings' range, e.g. type indices below `2 ^ 32`) before the target can follow.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- `ResidueRest` from `ResidueCore`, with configok's `result` and `funcinst`. -/
theorem residueRest_of_core {B : Builtins} {hn : H → String} (R : ResidueCore (simEnv B)) :
    ResidueRest (simEnv B) hn where
  types := R.types
  valtypes := R.valtypes
  result r _ := ConfigOk.typedV_result r
  funcinst := ConfigOk.funcinst_of_store hn
  refOk := R.refOk

/-- `ExtraRest` from `AggTypes`, with configok's `MemTyping` and `InstTyping`. -/
theorem extraRest_of_agg {B : Builtins} (A : Aggregates.AggTypes (simEnv B)) :
    ExtraRest (simEnv B) where
  mem := ConfigOk.memTyping_simEnv B
  inst := ConfigOk.instTyping_simEnv B
  agg := A

/-- `BwdOpen` from the open backward rules, with configok's `exnFields`. -/
theorem bwdOpen_of_remaining {B : Builtins} {hn : H → String} {P : Profile}
    {host : HostSemantics H} (R : Integrate.RemainingW (simEnv B) hn P host) :
    Integrate.BwdOpen B hn P host where
  exnFields := ConfigOk.exnFields_simEnv B hn
  remaining := R

/-- **`Task.wholeStepBounded`, reduced to what tracks refok and configok leave open.** -/
theorem wholeStepBounded_of_core
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Prims.HostRespects hn host ∧
        ResidueCore (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        Aggregates.AggTypes (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        Integrate.RemainingW (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn
          (Profile.spec nd r) host ∧
        (∀ c c' : Config H, ¬ Integrate.Covered c → Integrate.StoreOk c.store →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧
            SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c)
              (configV hn d'))) :
    Integrate.Task.wholeStepBounded :=
  wholeStepBounded_of_refok fun H hn hinj host hfin nd r =>
    let ⟨hr, R, A, Rw, hrest⟩ := h H hn hinj host hfin nd r
    ⟨hr, residueRest_of_core R, extraRest_of_agg A, bwdOpen_of_remaining Rw, hrest⟩

/-- `ResidueCore` is uninhabited, in every `simEnv B` (`types` is refuted by its proof). -/
theorem not_residueCore (B : Builtins) : ¬ ResidueCore (simEnv B) :=
  fun R => ConfigOk.not_typeTyping B R.types

/-- `AggTypes` is uninhabited, in every `simEnv B`. -/
theorem not_aggTypes' (B : Builtins) : ¬ Aggregates.AggTypes (simEnv B) :=
  ConfigOk.not_aggTypes B

end Silmaril.Wasm.SpecTec.Sim.RefOk
