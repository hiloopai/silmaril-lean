module

public import Silmaril.Wasm.SpecTec.Sim.Round7.RMD.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.RMD.Assemble

/-!
# Round 7, `BD`: `Round7.Task.wholeStepValidRM` reduced at `BD`

Round 7 reduced the frozen target to `MemSimd.OpenRMRest` / `VInv.OpenRMRestMS` at
`BM = withVBytes (Prims.builtins …)`, whose `$hostcall` answers no call made from a store with
memory SIMD code. This topic restates the reduction at `HostD.BD` (`$hostcall` keyed on `storeVD`
images) and discharges at `BD` everything that was discharged at `BM`:

* **The memory SIMD rules at `BD`** (`readMSD_bd`, `stepMSD_bd`): the ten loads (`Step_read`
  42–51) and four stores (`Step` 22–25), at every configuration. Rules other than 43 and 23 move
  from `BM` by `HAgree.fires_read_iff`/`fires_step_iff`; rules 43 and 23 use round 7's
  builtins-generic leaves with `$vbytes_` answered by `BD` (`vBytes_bd`).
* **The backward dispatch at `BD`** (`backward_upToD_restSD`).
* **The rest of the backward half at `BD`** (`restD_of_restMSH`): the host calls `Step` 8 and 9
  are round 5's `HostRulesD.hostStepsD`; every other rule moves from round 6's `BI`
  (`HAgree.backwardUpToDRestSH_agree`), where `VInv.backwardUpToDRestS_noMSDom` covers
  `NoMSDom` and `RestMSH` the rest.
* **`wholeStepValidRM_of_restD`**: the frozen target from `OpenRMRestD` (forward half and cast
  leaf at `BD`, and `RestMSH`). `RestMSH` follows from round 7's `RestMS` and, for a host that adds
  no memory SIMD code, from `RestMSC` (`restMSH_of_restMS`, `restMSH_of_restMSC`).

Still open: `OpenRMRestD.forward`, `castsFwd`, `castsBwd` and `restMSH`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.RMD.readMSD_bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readMSD_bd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.RMD.stepMSD_bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepMSD_bd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.RMD.restD_of_restMSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restD_of_restMSH

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.RMD.wholeStepValidRM_of_restD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restD

end Silmaril.Wasm.SpecTec.Sim.Round7.RMD
