module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Thms

/-!
# Round 7, `BD`: `Round7.Task.wholeStepValidRM` reduced at `BD` (definitions)

Round 7 reduced the frozen target `Round7.MemSimd.Task.wholeStepValidRM` to `MemSimd.OpenRMRest`
(and then to `VInv.OpenRMRestMS`), stated at the builtins `BM = withVBytes (Prims.builtins …)`.
`BM` answers no `$hostcall` made from a store with memory SIMD code (`MSPres.bm_hostcall_none`),
so `OpenRMRest.forward` asks, at a Core host call from such a store, for a SpecTec step that the
host-call rules of `simEnv BM` cannot make. Round 5 defined `HostD.BD`, whose `$hostcall` is keyed
on `storeVD` images, and proved the host-call rules at `BD` in both directions
(`HostRulesD.fwd_callRefHostD`, `HostRulesD.hostStepsD`).

This topic restates the reduction at `BD`:

* `RestMSH hn P host`: `VInv.RestMS` (the per-rule backward obligations at round 6's `BI` on the
  `NoCastVM` configurations outside `VInv.NoMSDom`) **without the host-call rules** `Step` 8 and
  9 (`HAgree.BackwardUpToDRestSH`). At `BD` those two rules are `hostStepsD`.
* `OpenRMRestD hn P host`: `VInv.OpenRMRestMS` with `forward`, `castsFwd` and `castsBwd` read at
  `BD` and `restMS` weakened to `RestMSH`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMD

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (NoCastVM BoundedSelM configVD)
open Round7.HostD (BD)
open Round6.Target (CastRedex)

variable {H : Type}

/-- **`VInv.RestMS` without the host-call rules**: the per-rule backward obligations at round 6's
builtins, off memory SIMD and off `Step` 8 and 9, at the `NoCastVM` configurations outside
`NoMSDom`. -/
def RestMSH (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  HAgree.BackwardUpToDRestSH (fun c => NoCastVM c ∧ ¬ VInv.NoMSDom P host c)
    (simEnv (Prims.builtins P hn host)) hn P host

/-- **`VInv.OpenRMRestMS` at `BD`**: the forward half away from cast redexes and the cast leaf at
`BD`, and the per-rule backward obligations of `RestMSH`. -/
structure OpenRMRestD (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- The declarative forward half at `configVD` and `BD`, away from cast redexes, up to Core's
  choice of successor. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations at `BI` off memory SIMD and off the host calls, outside
  `NoMSDom`. -/
  restMSH : RestMSH hn P host
  /-- The cast leaf at `BD`, forward. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- The cast leaf at `BD`, backward. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round7.RMD
