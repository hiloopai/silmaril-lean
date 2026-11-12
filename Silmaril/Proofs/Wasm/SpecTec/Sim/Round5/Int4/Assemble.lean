module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int4.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi4.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Thms

/-!
# Round 5, pass-4 integration: the backward relation on `FloatMissel`-free runs

`Target.bwdRelSel_of_partsSel`, `bwdRelSel_of_open5`, `multiSel_of_open5` and
`runsSel_of_open5` with `Multi.succTyped` and `Multi.witnessBnd` plugged in, so
that the backward relation needs only `PartsSel` (whose `pos` field is `Target.posTypingSel`):

* `bwdRelSel_of_partsSel`, `bwdRelSel_of_open5`;
* `multiSel3_of_multiSel`, `multiSel3_of_open5`;
* `runsSel_of_open5`: both run directions with no further hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int4

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel SSteps)
open Round4Int (BI)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (ConfigEq)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The backward relation on `FloatMissel`-free sources, from `PartsSel` alone.** -/
theorem bwdRelSel_of_partsSel (Pa : Target.PartsSel hn P host) (hh : HostOk host) :
    Target.BwdRelSel (BI P hn host) hn P host :=
  Target.bwdRelSel_of_partsSel Pa hh (Multi.succTyped _ hn) (Multi.witnessBnd _ hn)

/-- **The backward relation, from `Target.Open5` alone** (vacuous: `Target.not_open5_spec`). -/
theorem bwdRelSel_of_open5 (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (hh : HostOk host) (O : Target.Open5 hn P host) : Target.BwdRelSel (BI P hn host) hn P host :=
  Target.bwdRelSel_of_open5 hinj hf hPs hPf hh O (Multi.succTyped _ hn) (Multi.witnessBnd _ hn)

/-- `Target.MultiSel` gives `MultiSel3`. -/
theorem multiSel3_of_multiSel (h : Target.MultiSel) : MultiSel3 :=
  fun H hn hinj host hf hh nd r =>
    have ⟨B, hF, hB⟩ := h H hn hinj host hf hh nd r
    ⟨B, hF, hB (Multi.succTyped B hn) (Multi.witnessBnd B hn)⟩

/-- **`MultiSel3` from the leaves `Target.Open5`** (vacuous: `Target.not_open5_spec`). -/
theorem multiSel3_of_open5
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Target.Open5 hn (Profile.spec nd r) host) :
    MultiSel3 :=
  multiSel3_of_multiSel (Target.multiSel_of_open5 h)

/-- **The run corollaries on `FloatMissel`-free runs, from `Target.Open5`**, both directions
with no further hypothesis (vacuous: `Target.not_open5_spec`). -/
theorem runsSel_of_open5 {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : Target.Open5 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      Target.BoundedReachSel (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      Target.BoundedReachSel (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  have h := Target.runsSel_of_open5 hinj hf hh O
  ⟨h.1, h.2 (Multi.succTyped _ hn) (Multi.witnessBnd _ hn)⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Int4
