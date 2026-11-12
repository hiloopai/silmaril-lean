module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HCtx.Call

/-!
# Round 7, `BD`: context lifting at `configVD`, and host calls under contexts (round 6, pass 3,
proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.HCtx`; see `docs/projects/spectec/README.md`. Definitions (`FwdPD`, `CtxStep`, `HostLeaf`, `HostCtxStep`) are in
`Round7/HCtx/Defs.lean`.

* `fwdD_ctxtInstrs`, `fwdD_ctxtLabel`, `fwdD_ctxtHandler`, `fwdD_ctxtFrame`: the four context
  liftings at `configVD`, in every `simEnv B`.
* `fwdD_ctxStep`: `FwdPD` is closed under `CtxStep`; `step_of_ctxStep`: a `CtxStep` of Core steps
  is a Core step.
* `fwdD_hostCtx`: **a Core host call under any labels, handlers, frames and value/instruction
  context is a SpecTec step between `configVD` images at `BD`**, for every store (memory SIMD
  code included), given bounded function types.
* `forwardD_hostCtx`: the same in the shape of `RMD.OpenRMRestD.forward`.
* `fwdD_callRefNull`, `fwdD_callRefFunc`: `call_ref` on a null reference and into a Wasm function
  (`Step` rules 6 and 7) at `configVD` and `BD`, for every store.
* `fwdD_callCtx`, `forwardD_callCtx`: **every `call_ref` step on a reference (null, Wasm function,
  host function returning or diverging), under any evaluation context, is a SpecTec step between
  `configVD` images at `BD`**, at every source, memory SIMD code included.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCtx

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.fwdD_ctxStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdD_ctxStep

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.fwdD_hostCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdD_hostCtx

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.forwardD_hostCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forwardD_hostCtx

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.fwdD_callRefFunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdD_callRefFunc

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCtx.forwardD_callCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forwardD_callCtx

end Silmaril.Wasm.SpecTec.Sim.Round7.HCtx
