module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HPair.Thms

/-!
# Round 7, memory SIMD: `RestMSHC` with a proved slice removed (definitions)

* `pureVal`: the 42 `Step_pure` rules whose backward leaves read only the fired value
  (`BwdPureStep.pureDone`, `Integrate.floatDone`, `Round5.BwdStep.pureVecDone`).
* `RestMSHCR hn P host`: `NullHost.RestMSHC` with the `Step_pure` obligation asked only for rules
  outside `pureVal` or at configurations whose code (not only the store) holds memory SIMD code.
  The `Step_read` and `Step` obligations are unchanged.
* `OpenRMRestDPR`: `HPair.OpenRMRestDP` with `RestMSHCR` for `RestMSHC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSRest

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS NoMemSimd)
open Round6.Target (CastRedex)
open Round7.MemSimd (NoCastVM BoundedSelM configVD adminsToVD TypedD BwdUpToD msReadRules
  stepMSRules)
open Round7.HostD (BD)

variable {H : Type}

/-- The `Step_pure` rules whose backward leaves read only the fired value. -/
def pureVal : List Nat :=
  BwdPureStep.pureDone ++ Integrate.floatDone ++ Round5.BwdStep.pureVecDone

/-- The configurations of `RestMSHC`: `NoCastVM` and holding memory SIMD code. -/
def VMS (c : Config H) : Prop := NoCastVM c ∧ ¬ NoMemSimd c

/-- **`NullHost.RestMSHC` without the value-level `Step_pure` rules at memory-SIMD-free code.** -/
structure RestMSHCR (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `Step_pure`, for rules outside `pureVal` or code holding memory SIMD instructions. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    (i ∉ pureVal ∨ ¬ AdminsMS is) → VMS ⟨s, f, is⟩ →
    TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, as in `RestMSHC`. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), VMS c →
    TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step`, as in `RestMSHC`. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 8 → i ≠ 9 → ∀ (c : Config H) (w : Value),
    VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w]) →
    BwdUpToD hn P host c w

/-- **`HPair.OpenRMRestDP` with `RestMSHCR` for `RestMSHC`.** -/
structure OpenRMRestDPR (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `HPair.OpenRMRestDP.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code →
    ¬ HPair.EasyP hn P host c → Step P host c c' → ¬ HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations left. -/
  restMSHC : RestMSHCR hn P host
  /-- As `HPair.OpenRMRestDP.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → ¬ HPair.EasyP hn P host c →
    Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `HPair.OpenRMRestDP.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code → ¬ HPair.EasyP hn P host c →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round7.MSRest
