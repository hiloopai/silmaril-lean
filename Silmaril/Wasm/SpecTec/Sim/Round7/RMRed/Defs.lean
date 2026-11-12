module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.Thms

/-!
# Round 7, `BD`: the reduction of `Task.wholeStepValidRM` with the proved pieces removed
(definitions)

`NullHost.OpenRMRestDC` has four fields. Three of them are now proved on part of their domain:

* `forward` at sources with no memory SIMD code, no successor with memory SIMD code and no
  `CALL_REF` in the image (`HStep.forwardD_noMS`), and for every `call_ref` step on a reference
  (null, Wasm function, host function) under any evaluation context, at every source
  (`HCtx.forwardD_callCtx`);
* `castsFwd` and `castsBwd` at the same sources as `forwardD_noMS` (`HCasts.castsFwdD_noMS`,
  `castsBwdD_noMS`).

This header states what remains.

* `Easy hn P host c`: `c` has no memory SIMD code, nor does any Core successor, and its `configV`
  image has no memory SIMD atom and no `CALL_REF` (`VInv.NoAtoms HStep.hAtoms`).
* `OpenRMRestDR hn P host`: `OpenRMRestDC` with `forward` restricted to sources that are not
  `Easy` and steps that are not `HCtx.CallCtxStep`, and `castsFwd`/`castsBwd` restricted to
  sources that are not `Easy`. `restMSHC` is unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMRed

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (NoMemSimd)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM configVD)
open Round7.HostD (BD)

variable {H : Type}

/-- **The sources the proved pieces cover**: no memory SIMD code in `c` or in any Core successor,
and no memory SIMD atom or `CALL_REF` in `c`'s image. -/
def Easy (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  NoMemSimd c ∧ (∀ c₁, Step P host c c₁ → NoMemSimd c₁) ∧
    VInv.NoAtoms HStep.hAtoms (configV hn c)

/-- **`NullHost.OpenRMRestDC` with the proved parts removed.** -/
structure OpenRMRestDR (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `forward`, at sources that are not `Easy`, for steps that are not `call_ref` steps on a
  reference under contexts. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → ¬ Easy hn P host c →
    Step P host c c' → ¬ HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations at configurations holding memory SIMD code. -/
  restMSHC : NullHost.RestMSHC hn P host
  /-- `castsFwd`, at sources that are not `Easy`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → ¬ Easy hn P host c →
    Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- `castsBwd`, at sources that are not `Easy`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code → ¬ Easy hn P host c →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round7.RMRed
