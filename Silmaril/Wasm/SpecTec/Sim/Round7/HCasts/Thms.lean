module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HCasts.Casts

/-!
# Round 7, `BD`: the backend whole step across `$hostcall`, and the cast leaf at `BD` off memory
SIMD and `CALL_REF` (round 6, pass 3, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.HCasts`; see `docs/projects/spectec/README.md`. The definition (`StepInvBH`) is in `Round7/HCasts/Defs.lean`.

* `stepInvBH_h`: `LhsNoAtoms hAtoms` is a `StepInvBH` (rules 43, 23, 8 and 9 silent under the
  backend reading, and it passes through the context rules).
* `sstepB_agree`, `sstepB_iff_h` (unrefined, `Raw/…/Round7/HCasts/StepB.lean`): **under a
  `StepInvBH`, the backend whole step moves between builtins that agree off `$vbytes_` and
  `$hostcall`**. `sstepB_bd_bi_iff`, `sstepB_bd_bm_iff`: at `NoAtoms hAtoms` sources, `BD`, `BM`
  and `BI` read it alike.
* `castsFwdD_noMS`, `castsBwdD_noMS`: `RMD.OpenRMRestD.castsFwd`/`castsBwd` at memory-SIMD-free
  sources whose image has no `CALL_REF`, when no Core successor has memory SIMD code.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCasts

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.stepInvBH_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepInvBH_h

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.sstepB_iff_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepB_iff_h

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.castsFwdD_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms castsFwdD_noMS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.castsBwdD_noMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms castsBwdD_noMS

end Silmaril.Wasm.SpecTec.Sim.Round7.HCasts
