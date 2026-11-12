module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read2.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms

/-!
# SpecTec ↔ Core 3.0, round 5, pass-3 integration: assembly

`Open4` gives pass 2's `Open2`, using the four leaves pass 3 proved; the restated target and
the run corollaries follow. `not_open4` and `not_open4_spec` record that `Open4` is
unsatisfiable.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int3

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round4 (SSteps)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`Round5.Int2.Open2` from `Open4`**, at an injective encoding. -/
theorem open2_of_open4 (hinj : Function.Injective hn) (O : Open4 hn P host) :
    Int2.Open2 hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := FwdRef2.hostRespectsT_all _ hinj host
  vector := SimdTy.vectorFwd_of_ops O.vecOps
  vecOps := O.vecOps
  vtestop := Simd.pureOpenVtestop
  read := Read2.readRest

/-- `Open2` gives `Open4`: the new leaves ask no more. -/
theorem open4_of_open2 (O : Int2.Open2 hn P host) : Open4 hn P host where
  simd := O.simd
  refOk := O.refOk
  vecOps := O.vecOps

/-- **`Open4` never holds**: its `simd` leaf is false for every builtins. -/
theorem not_open4 : ¬ Open4 hn P host := fun O => SimdTy.not_simdTyping _ O.simd

/-- **`Open4` never holds under the spec NaN profile**, independently of `simd`: its `vecOps`
leaf fails at `convert`. -/
theorem not_open4_spec (nd : Bool) (r : RelaxedChoice) : ¬ Open4 hn (Profile.spec nd r) host :=
  fun O => Simd.not_vecAgreeOps_spec rfl O.vecOps

/-- **`Round5.Task.wholeStepValidOk` from the leaves still open after pass 3**, at every
injective encoding, finite `HostOk` host and `Profile.spec nd r`. Vacuous: see `not_open4`. -/
theorem wholeStepValidOk_of_open4
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open4 hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Int2.wholeStepValidOk_of_open2 fun H hn hinj host hfin hok nd r =>
    open2_of_open4 hinj (h H hn hinj host hfin hok nd r)

/-- **The composable one-step simulations (`Int2.MultiOk2`) from `Open4`.** -/
theorem multiOk2_of_open4
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open4 hn (Profile.spec nd r) host) :
    Int2.MultiOk2 :=
  Int2.multiOk2_of_open2 fun H hn hinj host hfin hok nd r =>
    open2_of_open4 hinj (h H hn hinj host hfin hok nd r)

/-- **The run corollaries of the restated target, from `Open4`**: pass 2's
`Round5.Int2.runs_of_open2` with the four pass-3 leaves discharged. -/
theorem runs_of_open4 {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : Open4 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      Multi.BoundedReachNE (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (Multi.SuccTyped (BI (Profile.spec nd r) hn host) hn →
      Int2.WitnessBnd (BI (Profile.spec nd r) hn host) hn →
      ∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      Multi.BoundedReachNE (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  Int2.runs_of_open2 hf hh (open2_of_open4 hinj O)

end Silmaril.Wasm.SpecTec.Sim.Round5.Int3
