module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnGen
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnRead
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnLoad
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnStore
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnCall
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnBase
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnRun
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnBulk

/-!
# Stores inside the store's functions: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreFn`; see `docs/projects/spectec/README.md`, "fwd20
".

* `StoreFnGen`: **`firesT_of_parts`**, `firesT_read_of20`, `firesT_step_of20`: a relation-free
  rule fires in `simEnv20T` from quantifiers typed there and its conclusion and premises
  evaluated in `simEnv20` (moved by `RelFree` and `StoreAgree`); `quantsOkT_z` types the
  quantifiers from the state in `simEnv20T` and the rest in `simEnv20`.
* `StoreFnRead`, `StoreFnLoad`, `StoreFnStore`, `StoreFnCall`: every state-reading rule of the
  covered fragment fired in `simEnv20T` from a state typed only there: `local.get`/`set`,
  `global.get`/`set`, `ref.func`, `call`, `call_addr`, `table.size`, `memory.size`, both
  `table.get` rules, the four loads, the six scalar stores, both `call_indirect` rules (the
  `otherwise` of `call_indirect-trap` proved in `simEnv20T` directly, `otherwise4T`).
* `StoreFnTyp`: `eraseS`, `StoreOkD`, and **`typedT_state_of_erased`**: a state whose erasure is
  typed in `simEnv20`, over a `StoreOkD` store, is typed in `simEnv20T`.
* `StoreFnBase`: `BaseF`, **`cover20F`**, **`okF_step`**.
* `StoreFnNest`: `TypF` and **`fwd_nestF`**, with subject reduction through the erased state.
* `StoreFnRun`: **`Good20F`**, **`fwd_good20F`**, **`good20F_steps`**, `runT_good20F`,
  `typed20T_of_good20F`, **`good20F_of_good20D`**, `good20F_invoke`, and a witness beyond
  `simEnv20` (`good20F_beyond_simEnv20`).
* `StoreFnBulk`: `memory.fill` forward at the rule level, from a state typed in `simEnv20T`:
  `firesT_memFillTrap`, `firesT_memFillZero`, `firesT_memFillSucc` (whose successor holds an
  `i32.store8`), with both `otherwise` premises proved in `simEnv20T` (`otherwise38T`,
  `otherwise39T`); `-succ` asks for `i + 1 < 2 ^ 32` (V2 wraps, the script does not).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_of_parts

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_read_of20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_read_of20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_step_of20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_step_of20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.quantsOkT_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quantsOkT_z

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_localGet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_localGet

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_globalSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_globalSet

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_loadPackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_loadPackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_storeNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_storeNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_storePackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_storePackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.typedT_state_of_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_state_of_erased

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_callAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_callAddr

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.otherwise4T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms otherwise4T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_callIndirectTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_callIndirectTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.cover20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cover20F

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.okF_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms okF_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.fwd_nestF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_nestF

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.fwd_good20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_good20F

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.good20F_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20F_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.runT_good20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runT_good20F

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.typed20T_of_good20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed20T_of_good20F

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.good20F_of_good20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20F_of_good20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.good20F_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20F_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.good20F_beyond_simEnv20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20F_beyond_simEnv20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_memFillTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_memFillTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_memFillZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_memFillZero

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.firesT_memFillSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_memFillSucc

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFn.otherwise39T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms otherwise39T

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
