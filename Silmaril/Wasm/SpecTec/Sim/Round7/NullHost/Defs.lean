module

public import Silmaril.Wasm.SpecTec.Sim.Round7.RMD.Thms

/-!
# Round 7, memory SIMD: `RestMSH` without its successor half (definitions)

`RMD.RestMSH hn P host` asks for the per-rule backward obligations at round 6's builtins, off
memory SIMD and off the host calls `Step` 8 and 9, at the `NoCastVM` configurations outside
`VInv.NoMSDom`. A configuration is outside `NoMSDom` when it holds memory SIMD code itself, or
when a Core successor does. Round 7 removed the second case only for a host that adds no memory
SIMD code (`MSPres.HostKeepsMS`, `MSPres.restMS_iff_restMSC`); `BMHost.msAddHost` is a finite,
`HostOk` host that adds some.

The definitions below drop the second case for every host.

* `nullHost`: the host with no outcome. Its Core steps are the host-free ones
  (silmaril's `Step.of_noHost`), and round 6's primitives at it agree with those at any host off
  `$hostcall` (`NullHost.agreeOff_host`).
* `RestMSHC hn P host`: `RestMSH` at the `NoCastVM` configurations that hold memory SIMD code
  (in the code or in a store function body), at any depth.
* `OpenRMRestDC`: `RMD.OpenRMRestD` with `restMSH` replaced by `RestMSHC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NullHost

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (NoCastVM BoundedSelM configVD)
open Round7.HostD (BD)
open Round6.Target (CastRedex)

variable {H : Type}

/-- **The host with no outcome.** -/
def nullHost : HostSemantics H := fun _ _ _ _ => False

/-- **`RestMSH` at the configurations that hold memory SIMD code**: the per-rule backward
obligations at round 6's builtins, off memory SIMD and off `Step` 8 and 9, at the `NoCastVM`
configurations with memory SIMD code in the code or in a store function body. -/
def RestMSHC (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  HAgree.BackwardUpToDRestSH (fun c => NoCastVM c ∧ ¬ Round6.MemSimd.NoMemSimd c)
    (simEnv (Prims.builtins P hn host)) hn P host

/-- **`RMD.OpenRMRestD` with `RestMSHC` for `RestMSH`.** -/
structure OpenRMRestDC (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMD.OpenRMRestD.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations at configurations holding memory SIMD code. -/
  restMSHC : RestMSHC hn P host
  /-- As `RMD.OpenRMRestD.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMD.OpenRMRestD.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round7.NullHost
