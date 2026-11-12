module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef2.Typed
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Thms

/-!
# Round 5, pass 3, track fwdref: `HostRespectsT` holds for every host

* `storeInjT_simEnv`: `StoreInjT (simEnv B) hn` holds for every injective `hn`
  (`storeV_inj_typed`).
* `hostRespectsT_all`: so `HostRespectsT (simEnv B) hn host` holds for every host
  (`FwdRef.hostRespectsT_of_storeInj`).
* `open2_of_open3`, `wholeStepValidOk_of_open3`, `multiOk2_of_open3`, `runs_of_open3`: the
  pass-2 results with `Open2.hostRespects` discharged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round4 (SSteps)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`StoreInjT` holds**: `storeV hn` is injective on stores with typed images, for every
injective `hn` and every `B`. -/
theorem storeInjT_simEnv (B : Builtins) (hinj : Function.Injective hn) :
    FwdRef.StoreInjT (simEnv B) hn :=
  fun _ _ hs h => storeV_inj_typed hinj hs h

/-- **`HostRespectsT` holds for every host**, at an injective `hn`. -/
theorem hostRespectsT_all (B : Builtins) (hinj : Function.Injective hn) (host : HostSemantics H) :
    FwdRef.HostRespectsT (simEnv B) hn host :=
  FwdRef.hostRespectsT_of_storeInj hinj (storeInjT_simEnv B hinj)

/-- `Open3` gives pass 2's `Open2`, at an injective `hn`. -/
theorem open2_of_open3 (hinj : Function.Injective hn) (O : Open3 hn P host) :
    Int2.Open2 hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := hostRespectsT_all _ hinj host
  vector := O.vector
  vecOps := O.vecOps
  vtestop := O.vtestop
  read := O.read

/-- `Open2` gives `Open3` (it is a sub-structure). -/
theorem open3_of_open2 (O : Int2.Open2 hn P host) : Open3 hn P host :=
  ⟨O.simd, O.refOk, O.vector, O.vecOps, O.vtestop, O.read⟩

/-- **`Round5.Task.wholeStepValidOk` from the leaves still open after pass 3, track fwdref.** -/
theorem wholeStepValidOk_of_open3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open3 hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Int2.wholeStepValidOk_of_open2 fun H hn hinj host hf hok nd r =>
    open2_of_open3 hinj (h H hn hinj host hf hok nd r)

/-- **`Int2.MultiOk2` from `Open3`.** -/
theorem multiOk2_of_open3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open3 hn (Profile.spec nd r) host) :
    Int2.MultiOk2 :=
  Int2.multiOk2_of_open2 fun H hn hinj host hf hok nd r =>
    open2_of_open3 hinj (h H hn hinj host hf hok nd r)

/-- **The run corollaries from `Open3`**: `Int2.runs_of_open2` with `hostRespects`
discharged. -/
theorem runs_of_open3 {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : Open3 hn (Profile.spec nd r) host) :
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
  Int2.runs_of_open2 hf hh (open2_of_open3 hinj O)

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2
