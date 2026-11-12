module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: REI without `HostExportParam` (round 5, pass 2)

`Round7.Task.wholeStepValidREI` (proved, `Round7.EraseDer.wholeStepValidREI_holds`) asks the host
to be export-parametric (`HostExportParam`): invariant under *every* export-only rewriting of
*every* store. The proof uses this hypothesis in two places only.

* On the SpecTec side, through `Round7.Swap.host_mods_sub`: a finite, export-parametric host
  returns only module instances of the store it was called in. This is what keeps the outcomes
  of `$hostcall` in the swap set.
* On the Core side, through `Round7.step_mapConfig`, which needs `HostModMap host μ` at every
  store, although a step calls the host only at the store of its source.

This header states the two weaker hypotheses that replace it.

* `HostModsSub host`: every module instance of a returned store is one of the calling store.
  It is the conclusion of `host_mods_sub`, so it follows from `HostFinite` and `HostExportParam`
  (`Round7.HostMods.hostModsSub_of_param`). It does not ask anything about export lists.
* `HostModMapAt host μ s`: `HostModMap host μ` at the one store `s`.

`StepValidREM` is `Round7.Task.wholeStepValidREI` with `HostModsSub` in place of
`HostExportParam`. It is a plain definition, not a frozen task: it is proved in
`Round7.HostMods.Thms` (`stepValidREM_holds`), and it implies `Round7.Task.wholeStepValidREI`
(`wholeStepValidREI_of_REM`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-- **The host invents no module instance**: every module of a store it returns is a module of
the store it was called in. -/
def HostModsSub (host : HostSemantics H) : Prop :=
  ∀ (h : H) (s s' : Store H) (vs : List Val) (r : Result),
    host h s vs (.returned s' r) → ∀ fi ∈ s'.funcs, fi.module ∈ s.funcs.map FuncInst.module

/-- **`HostModMap host μ` at one store**: an outcome of a call in `s` is rewritten by `μ` to an
outcome of the same call in `mapStore μ s`. -/
def HostModMapAt (host : HostSemantics H) (μ : ModuleInst → ModuleInst) (s : Store H) : Prop :=
  ∀ (h : H) (vs : List Val) (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
    host h s vs o → host h (mapStore μ s) vs (mapOutcome μ o)

/-- **`Round7.Task.wholeStepValidREI` with `HostModsSub` in place of `HostExportParam`**. Proved
(`Round7.HostMods.stepValidREM_holds`). -/
def StepValidREM : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      HostModsSub host → ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c → StripInj c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧ backendE.step B (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelE c → StripInj c → backendE.step B (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
