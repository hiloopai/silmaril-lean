module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.StoreAgree.Eval
public import Silmaril.Raw.Wasm.SpecTec.Sim20.StoreAgree.Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeDerive
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeStore
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeCtx
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeRoute

/-!
# `simEnv20S` against `simEnv20T`: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreAgree`; see `docs/projects/spectec/README.md`, "fwd20
".

* `Raw/…/StoreAgree/Eval`: two environments with the same definitions, relations and primitives
  whose matchers agree evaluate alike at every fuel (`sameMonoAt`, `evalExp_eq`, …).
* `Raw/…/StoreAgree/Typ`: if the type tables differ only by repairing variant cases that no
  payload inhabits (`TypRepair`), typing grows (`hasTyp_repair`).
* `StoreAgreeEnv`: `simEnv20S B` and `simEnv20T B` are such a pair (`envSame20T`,
  `typRepair20T`; the original `STORE` cases are dead, `deadCase_store`).
* `StoreAgreeDerive`: plain rule firings and the original `Step` rules `k ≥ 4` move to
  `simEnv20T` (`sstepB20T_of_fires20`); whole derivations move under `ElseAgree20T`
  (`sstepB20T_of_sstepB20S`), frozen as the open target `Task.elseAgree20T`.
* `StoreAgreeStore`, `StoreAgreeCtx`: every valid scalar store is a typed `admininstr` of
  `simEnv20T` (`typedV_intStore20T`, `typedV_floatStore20T`), and a top-level store under a value
  prefix and a suffix is a step of `simEnv20T (storeB P)` (`fwdT_storeCtx`).
* `StoreAgreeRoute`: the composite route at `simEnv20T` (`composite10T20`), its forward condition
  on stores under a context (`fwd20T_goodStore20T`, unconditional) and on
  `Good20C ∨ GoodStore20T` under `ElseAgree20T` (`fwd20T_goodT20`), with a configuration whose
  store below the top of the code steps in `simEnv20T` (`sstepT_memStore`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.evalExp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.evalExp_eq

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.hasTyp_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.hasTyp_repair

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.envSame20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.envSame20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.typRepair20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.typRepair20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.deadCase_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.deadCase_store

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.stepPlain20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.stepPlain20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.sstepB20T_of_fires20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.sstepB20T_of_fires20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.sstepB20T_of_sstepB20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.sstepB20T_of_sstepB20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.typedV_intStore20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.typedV_intStore20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.typedV_floatStore20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.typedV_floatStore20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwdT_storeCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwdT_storeCtx

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.composite10T20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.composite10T20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwd20T_of_fwd20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwd20T_of_fwd20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwd20T_goodStore20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwd20T_goodStore20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwd20T_goodT20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.fwd20T_goodT20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.storeCtxOk20_memStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.storeCtxOk20_memStore

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreAgree.sstepT_memStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreAgree.sstepT_memStore
