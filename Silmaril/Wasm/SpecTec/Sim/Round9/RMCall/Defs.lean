module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 9, rm: `Step` rule 7 at `configVD` (definitions)

Round 8's `FiresC.RestMSHCF` keeps `Step` rule 7 (`call_ref-func`) in its `step` field at every
configuration: its firing at `configVD` reads the callee's `CODE`, so it has no image at round 8's
named host store. Round 9 proves rule 7 directly at `configVD`
(`Round9.RMCall.bwd_callRefFuncD`), so the obligations below leave it out.

* `RestMSHCG`: `FiresC.RestMSHCF` with the `step` field asked only for `i ≠ 7`, hence only at code
  holding a memory SIMD instruction.
* `OpenRMRestDPG`: `FiresC.OpenRMRestDPF` with `RestMSHCG` for `RestMSHCF`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMCall

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (configVD adminsToVD TypedD BwdUpToD msReadRules stepMSRules BoundedSelM)

variable {H : Type}

/-- **`FiresC.RestMSHCF` without `Step` rule 7.** -/
structure RestMSHCG (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `FiresC.RestMSHCF.pure`. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ¬ AdminsMS is → Round7.MSRest.VMS ⟨s, f, is⟩ →
    TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- As `FiresC.RestMSHCF.read`. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), ¬ AdminsMS c.code →
    Round7.MSRest.VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- `FiresC.RestMSHCF.step` without rule 7: only at code holding a memory SIMD
  instruction. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 7 → i ≠ 8 → i ≠ 9 →
    ∀ (c : Config H) (w : Value), ¬ AdminsMS c.code → Round7.MSRest.VMS c →
    TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w]) →
    BwdUpToD hn P host c w
  /-- As `FiresC.RestMSHCF.firesRead`. -/
  firesRead : ∀ i ∈ Round8.FiresC.elseRead,
    Round8.RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i

/-- **`FiresC.OpenRMRestDPF` with `RestMSHCG` for `RestMSHCF`.** -/
structure OpenRMRestDPG (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `FiresC.OpenRMRestDPF.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule obligations left. -/
  restMSHC : RestMSHCG hn P host
  /-- As `FiresC.OpenRMRestDPF.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `FiresC.OpenRMRestDPF.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round9.RMCall
