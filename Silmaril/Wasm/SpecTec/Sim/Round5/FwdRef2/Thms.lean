module

public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef2.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass 3, track fwdref: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2`; see `docs/projects/spectec/README.md`.

* `instrToV_inj`: `instrToV` is injective at images satisfying a `GoodV` predicate, through the
  decoder `recon` (`recon_instrToV`). `goodV_typed` shows that the IL typing of `instr` is such a
  predicate, which gives `instrToV_inj_typed` and `instrsToV_inj_typed`.
* `storeV_inj_typed`, `storeInjT_simEnv`: `storeV hn` is injective on stores with typed images
  (`StoreInjT`), for an injective `hn`.
* `hostRespectsT_all`: so `FwdRef.HostRespectsT` holds for every host, and pass 2's leaf
  `Open2.hostRespects` is discharged.
* `open2_of_open3`, `wholeStepValidOk_of_open3`, `multiOk2_of_open3`, `runs_of_open3`: the
  restated target and its run corollaries from `Open3`, which is `Open2` without
  `hostRespects`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.instrToV_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef2.instrToV_inj

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.storeV_inj_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef2.storeV_inj_typed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.hostRespectsT_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef2.hostRespectsT_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.wholeStepValidOk_of_open3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef2.wholeStepValidOk_of_open3

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.multiOk2_of_open3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef2.multiOk2_of_open3

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.runs_of_open3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef2.runs_of_open3
