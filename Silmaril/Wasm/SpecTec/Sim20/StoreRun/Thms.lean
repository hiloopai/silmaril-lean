module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreRunInv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreRunExample
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreRunLift

/-!
# A storing V1 program through the composite route: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreRun`; see `docs/projects/spectec/README.md`, "fwd20
".

* `StoreRunInv`: V2's `Step`, inverted on `i32.const 0; i32.const 0; i32.store; nop` over one empty
  memory: its only step is to `trap; nop` (`step_memStoreCfg2_inv`).
* `StoreRunExample`: so the step-shape clause of `GoodStore20T` holds there, every reachable
  configuration is in `GoodT20`, and **`composite10T20_memStore`** exhibits one instance of
  `StoreAgree.composite10T20` on the V1 program with the same code, with no hypothesis.
* `StoreRunLift`: `Step/pure`, `Step/read`, `ctxt-label` and `ctxt-frame` lift steps in
  `simEnv20T` (`sstepT_pure`, `sstepT_read`, `sstepT_ctxtLabel`, `sstepT_ctxtFrame`), and every
  `Step_read` or `Step_pure` firing of the 2.0 script at a state and codes typed in `simEnv20T` is
  a step of `simEnv20T` (`sstepB20T_of_firesRead20`, `sstepB20T_of_firesPure20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreRun

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.step_memStoreCfg2_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_memStoreCfg2_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.runGood_memStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runGood_memStore

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.composite10T20_memStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composite10T20_memStore

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.sstepT_ctxtLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepT_ctxtLabel

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.sstepT_ctxtFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepT_ctxtFrame

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.sstepB20T_of_firesRead20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepB20T_of_firesRead20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreRun.sstepB20T_of_firesPure20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepB20T_of_firesPure20

end Silmaril.Wasm.SpecTec.Sim20.StoreRun
