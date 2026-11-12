module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.Defs

/-!
# Round 9, rm: `Step_pure` at memory SIMD code (definitions)

Round 9's `RMAtom.RestMSHCH` asks for the `Step_pure` obligation at code holding a memory SIMD
instruction only at the 15 rules that are not flat (`RMAtom.structPure`). Round 9 proves them at
`adminsToVD` (`Round9.RMPure.pure_struct`), so the obligations below drop the field.

* `RestMSHCI`: `RMAtom.RestMSHCH` without `pure`.
* `OpenRMRestDPI`: `RMAtom.OpenRMRestDPH` with `RestMSHCI` for `RestMSHCH`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMPure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (configVD adminsToVD TypedD BoundedSelM)

variable {H : Type}

/-- **`RMAtom.RestMSHCH` without its `Step_pure` field.** -/
structure RestMSHCI (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMAtom.RestMSHCH.read`: the 16 `Step_read` rules of `RMAtom.structRead`. -/
  read : ∀ i ∈ RMAtom.structRead, ∀ (c : Config H) (w : Value), ¬ AdminsMS c.code →
    Round7.MSRest.VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- As `RMAtom.RestMSHCH.firesRead`. -/
  firesRead : ∀ i ∈ Round8.FiresC.elseRead,
    Round8.RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i

/-- **`RMAtom.OpenRMRestDPH` with `RestMSHCI` for `RestMSHCH`.** -/
structure OpenRMRestDPI (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMAtom.OpenRMRestDPH.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule obligations left. -/
  restMSHC : RestMSHCI hn P host
  /-- As `RMAtom.OpenRMRestDPH.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMAtom.OpenRMRestDPH.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
