module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HStep.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HStep.Forward

/-!
# Round 7, `BD`: the whole step across `$hostcall`, and `forward` at `BD` off memory SIMD and
`CALL_REF` (round 6, pass 2, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.HStep`; see `docs/projects/spectec/README.md`. Definitions (`ctxPremOkH`, `stepCtxOkH`, `StepInvH`, `hAtoms`) are in
`Round7/HStep/Defs.lean`.

* `step_ctxOkH`, `ctx_lhsOkH` (kernel): the context rules' premises are `HAgree.RG`, rules 8 and 9
  end in `CALL_REF` and rule 23 in `VSTORE`; the context rules' left-hand sides are in
  `VInv.LFrag hAtoms`.
* `stepInvH_h`: `LhsNoAtoms hAtoms` (no memory SIMD atom and no `CALL_REF` in the left-hand side)
  is a `StepInvH`: rules 43, 23, 8 and 9 are silent at its values and it passes through rules 1–5.
* `sstep_agree` (unrefined, `Raw/…/Round7/HStep/Step.lean`): **under a `StepInvH`, the whole step
  moves between builtins that agree off `$vbytes_` and `$hostcall`**. `sstep_iff_h`,
  `sstep_bd_bm_iff`, `sstep_bd_bi_iff`: at `LhsNoAtoms hAtoms` values, `BD`, `BM` and round 6's
  `BI` read the whole step alike.
* `forwardD_noMS`: `RMD.OpenRMRestD.forward` at memory-SIMD-free sources whose image has no
  `CALL_REF`, when no Core successor has memory SIMD code, for a `HostOk` host.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HStep

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HStep.stepInvH_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepInvH_h

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HStep.sstep_iff_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_iff_h

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HStep.sstep_bd_bm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_bd_bm_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HStep.forwardD_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forwardD_noMS

end Silmaril.Wasm.SpecTec.Sim.Round7.HStep
