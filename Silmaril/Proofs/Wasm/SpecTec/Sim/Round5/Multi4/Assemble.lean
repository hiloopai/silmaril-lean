module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi4.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi4.WitnessBnd

/-!
# Round 5, track multi (pass 4): the backward multi-step relation without extra hypotheses

With `succTyped` and `witnessBnd` proved for every `B`, pass 2's backward relation needs only
what the one-step backward direction needs:

* `bwdRel_of_partsOkS`: `Multi.BwdRel` from `PartsOkS` and a `HostOk` host;
* `bwdRel_of_open2`, `runs_of_open2`, `runs_of_open4`: pass 2's and pass 3's corollaries
  without `SuccTyped` and `WitnessBnd`;
* `multiOk3_of_multiOk2`, `multiOk3_of_multiOk`, `multiOk3_of_open4`.

`Int3.Open4` is refuted (`Round5.Int3.not_open4`), and so is `PartsOkS`'s field `pos`
(`Round5.SimdTy.not_posTypingNE`). So these corollaries are still vacuous. They show only that
`SuccTyped` and `WitnessBnd` no longer stand between the leaves and the run corollaries.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel SSteps)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The backward relation, from `PartsOkS`**, for a `HostOk` host. -/
theorem bwdRel_of_partsOkS (Pa : Round5.Read.PartsOkS hn P host) (hh : HostOk host) :
    BwdRel (BI P hn host) hn P host :=
  Int2.bwdRel_of_partsOkS Pa hh (succTyped _ hn) (witnessBnd _ hn)

/-- **The backward relation, from `Open2`**, for a finite `HostOk` host in a profile where
growth may both succeed and fail. -/
theorem bwdRel_of_open2 (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (hh : HostOk host) (O : Int2.Open2 hn P host) :
    BwdRel (BI P hn host) hn P host :=
  Int2.bwdRel_of_open2 hf hPs hPf hh O (succTyped _ hn) (witnessBnd _ hn)

/-- `MultiOk2` without its backward hypotheses. -/
theorem multiOk3_of_multiOk2 (h : Int2.MultiOk2) : MultiOk3 := fun H hn hinj host hf hh nd r =>
  have ⟨B, hF, hB⟩ := h H hn hinj host hf hh nd r
  ⟨B, hF, hB (succTyped B hn) (witnessBnd B hn)⟩

/-- `MultiOk` without its backward hypothesis. -/
theorem multiOk3_of_multiOk (h : MultiOk) : MultiOk3 := fun H hn hinj host hf hh nd r =>
  have ⟨B, hF, hB⟩ := h H hn hinj host hf hh nd r
  ⟨B, hF, hB (succTyped B hn)⟩

/-- `MultiOk3` from pass 3's leaves (vacuous: `Int3.not_open4`). -/
theorem multiOk3_of_open4
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Int3.Open4 hn (Profile.spec nd r) host) :
    MultiOk3 :=
  multiOk3_of_multiOk2 (Int3.multiOk2_of_open4 h)

/-- **The run corollaries from `Open2`**, both directions without further hypotheses, at one
finite `HostOk` host and `Profile.spec nd r`, with `B := Prims.builtins`. -/
theorem runs_of_open2 {nd : Bool} {r : RelaxedChoice} (hf : HostFinite host) (hh : HostOk host)
    (O : Int2.Open2 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachNE (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachNE (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  have R := Int2.runs_of_open2 hf hh O
  ⟨R.1, R.2 (succTyped _ hn) (witnessBnd _ hn)⟩

/-- **The run corollaries from `Open4`**, both directions without further hypotheses (vacuous:
`Int3.not_open4`). -/
theorem runs_of_open4 {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : Int3.Open4 hn (Profile.spec nd r) host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachNE (Profile.spec nd r) host c₀ → Steps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachNE (Profile.spec nd r) host c₀ →
      SSteps (simEnv (BI (Profile.spec nd r) hn host)) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  runs_of_open2 hf hh (Int3.open2_of_open4 hinj O)

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
