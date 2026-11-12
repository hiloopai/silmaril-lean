module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMPure.Defs

/-!
# Round 9, rm: the structured `Step_read` rules at memory SIMD code (definitions)

`RMPure.RestMSHCI` asks for the `Step_read` obligation at code holding a memory SIMD instruction
at the 16 rules of `RMAtom.structRead`. Round 9 proves fifteen of them at `configVD`
(`Round9.RMRead.read_struct`) and shows that the last, `throw_ref-handler-next` (21), fires only at
memory-SIMD-free code (`adminsMS_of_handlerNext`). So the obligations below keep only round 8's
`firesRead` (the 28 `otherwise` rules under code erasure).

* `RestMSHCJ`: `RMPure.RestMSHCI` without `read`.
* `OpenRMRestDPJ`: `RMPure.OpenRMRestDPI` with `RestMSHCJ` for `RestMSHCI`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (configVD adminsToVD TypedD BoundedSelM)

variable {H : Type}

/-- **`RMPure.RestMSHCI` without its `Step_read` field**: only round 8's `firesRead` is left. -/
structure RestMSHCJ (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMPure.RestMSHCI.firesRead`. -/
  firesRead : ∀ i ∈ Round8.FiresC.elseRead,
    Round8.RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i

/-- **`RMPure.OpenRMRestDPI` with `RestMSHCJ` for `RestMSHCI`.** -/
structure OpenRMRestDPJ (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMPure.OpenRMRestDPI.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule obligations left. -/
  restMSHC : RestMSHCJ hn P host
  /-- As `RMPure.OpenRMRestDPI.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMPure.OpenRMRestDPI.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
