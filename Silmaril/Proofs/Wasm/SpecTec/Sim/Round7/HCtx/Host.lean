module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HCtx.Lift
public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Thms

/-!
# Round 7, `BD`: host calls under labels, frames and handlers, forward at `configVD`

* `fwdD_hostLeaf`: Core's two host-call steps are `FwdPD` steps at `simEnv (BD …)` when every
  function type of the source store is bounded (`HostRulesD.fwd_callRefHostD`,
  `fwd_callRefHostDivD`).
* `fwdD_hostCtx`: **a host call at any depth of evaluation context is a SpecTec step between the
  `configVD` images at `BD`**, for every store, memory SIMD code included (`fwdD_ctxStep`).
* `step_of_hostCtx`: such a step is a Core step.
* `forwardD_hostCtx`: the same in the shape of `RMD.OpenRMRestD.forward` (and of
  `NullHost.OpenRMRestDC.forward`): from a valid `BoundedSelM` source whose successors are
  `BoundedSelM`, for a finite `HostOk` host and an injective encoding. The successor is the
  step's own target, so the conclusion holds with `c'' := c'` and `d' := c'`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCtx

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (tyBnd)
open Round7.MemSimd (configVD TypedD BoundedSelM)
open Round7.HostD (BD)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **Core's host-call leaves, forward at `configVD` and `BD`**, at a store whose function types
are bounded. -/
theorem fwdD_hostLeaf (hinj : Function.Injective hn) (hf : HostFinite host) {s₀ : Store H}
    (hb : ∀ fi ∈ s₀.funcs, tyBnd fi.type = true) :
    ∀ c c' : Config H, HostLeaf P host c c' → c.store = s₀ →
      FwdPD (simEnv (BD P hn host)) hn c c'
  | _, _, .ret hc hfa hex hlen hcode hhost, hs => fun h₁ h₂ => by
      subst hs
      exact HostRulesD.fwd_callRefHostD hinj hf hc hfa hex hlen hcode hhost
        (hb _ (List.mem_of_getElem? hfa)) h₁ h₂
  | _, _, .div hc hfa hex hlen hcode hhost, hs => fun h₁ _ => by
      subst hs
      exact HostRulesD.fwd_callRefHostDivD hinj hf hc hfa hex hlen hcode hhost
        (hb _ (List.mem_of_getElem? hfa)) h₁

/-- **A host call under any evaluation context, forward at `configVD` and `BD`.** -/
theorem fwdD_hostCtx (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (hb : ∀ fi ∈ c.store.funcs, tyBnd fi.type = true) (h : HostCtxStep P host c c') :
    FwdPD (simEnv (BD P hn host)) hn c c' :=
  fwdD_ctxStep _ (fwdD_hostLeaf hinj hf hb) h rfl

/-- A host-call leaf is a Core step. -/
theorem step_of_hostLeaf : ∀ {c c' : Config H}, HostLeaf P host c c' → Step P host c c'
  | _, _, .ret hc hfa hex hlen hcode hhost => .callRefHost hc hfa hex hlen hcode hhost
  | _, _, .div hc hfa hex hlen hcode hhost => .callRefHostDiv hc hfa hex hlen hcode hhost

/-- **A host call under any evaluation context is a Core step.** -/
theorem step_of_hostCtx {c c' : Config H} (h : HostCtxStep P host c c') : Step P host c c' :=
  step_of_ctxStep (fun _ _ => step_of_hostLeaf) h

/-- **`forward` at `BD` for host calls under any evaluation context**, in the shape of
`RMD.OpenRMRestD.forward`. -/
theorem forwardD_hostCtx (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : BoundedSelM c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁)
    (h : HostCtxStep P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d') := by
  have hs := step_of_hostCtx h
  have hT := Round7.MemSimd.typedD_of_configOk_selM (BD P hn host) hn hc hb
  have hT' := Round7.MemSimd.typedD_of_configOk_selM (BD P hn host) hn
    (Step.preservation hh hc hs).1 (hsucc _ hs)
  refine ⟨c', hs, fun _ => rfl, c', Bwd.ConfigEq.refl c', ?_⟩
  exact fwdD_hostCtx hinj hf (fun fi hfi => (hb.1.1.storeBnd.funcs fi hfi).1) h hT hT'

end Silmaril.Wasm.SpecTec.Sim.Round7.HCtx
