module

public import Silmaril.Wasm.Wit.Project.IR.Defs
public import Silmaril.Proofs.Wasm.Wit.ProjectIR

/-!
# The world of an IR component: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.ProjectIR`:

* `world_flatten`: composing the nested component instances of a component into
  one flat component keeps its world;
* `world_specialise`: composing providers into the imports keeps the exports and
  replaces the imports by the providers' imports;
* `world_fuseComponent`, `world_fuseLinked`, `world_deadInstances`,
  `world_optimizeComponent`: the optimiser keeps the world;
* `world_deadExports_imports`: dead export elimination keeps the imports (it
  replaces unobserved exports, so their names and types change).
-/
