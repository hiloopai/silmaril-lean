module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Instantiation
public import Silmaril.Raw.Wasm.Versions.Lime1.ToV2.Execution
public import Silmaril.Raw.Wasm.Versions.Lime1.ToV2.Validation

/-!
# Wasm versions: the copied 2.0 → Core 3.0 simulation

The public header of the copies under `Silmaril/Raw/Wasm/Versions/**`: the forward simulation of
Wasm 2.0 execution and instantiation by Core 3.0, and of Wasm 1.0 and Lime1 by 2.0
(an earlier development,
`Silmaril/Wasm/V2/ToCore/{Runtime,Sim/*,Execution,Instantiation}`,
`Silmaril/Wasm/Lime1/{ToV2,ToCore}/*` and their missing prerequisites), with source namespaces kept:

* `Silmaril.Wasm.V2.Execution.Step.toCore`: one 2.0 step is simulated by one or more Core steps
  along `Sim`, at every profile;
* `Steps.toCore`, `Diverges.toCore`, `Sim.result`: finite runs, divergence and results;
* `Instantiate.toCore`, `InstantiateDiverges.toCore`: instantiation (under
  `InstantiationBounds`);
* `Silmaril.Wasm.Lime1.Execution.{Step,Steps,Diverges}.toV2`: Lime1 execution is simulated by
  2.0 execution at `v2Profile = Profile.spec` (`Lime1/ToV2/Execution.lean`), and
  `Silmaril.Wasm.V1.Execution.{Step,Steps,Diverges}.toV2` compose it with the lock-step
  1.0 → Lime1 simulation (`Lime1/Execution/FromV1.lean`); `Instantiation.toV2` for both;
* `Silmaril.Wasm.V1.Validation.ModuleValid.toV2`: a valid 1.0 module whose segment offsets read
  imported globals is a valid 2.0 module (`Lime1/ToV2/Validation.lean`);
* `Silmaril.Wasm.Lime1.Execution.{Step,Steps,Diverges}.toCore`: Lime1 execution is simulated by
  Core 3.0 (`Lime1/ToCore/*`, a prerequisite of the 2.0 bridge).

`Silmaril.Wasm.Models.V2Core.Thms`.
-/
