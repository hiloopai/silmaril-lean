module

public import Silmaril.Wasm.Spec.Graph.Defs
public import Silmaril.Proofs.Wasm.Spec.Graph.Basic

@[expose] public section

/-!
# The logic graph of the specification institutions: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Graph.Basic`.

* `SEdge.modelExpansive`: the edges marked `Expansive` are model-expansive comorphisms (logic
  maps by `LogicMap.coHom_modelExpansive`, wrapping and synchronous-to-asynchronous by
  `pushCoHom_modelExpansive`); `env_not_modelExpansive`: the environment edge is not (a program
  with a proper environment is not the chaotic reading of a program).
* `specGraphE_pathModelExpansive`: every path of `specGraphE P C` is model-expansive, hence
  **`specGraphE_entails_lift_path_iff`**: consequence in the Grothendieck institution
  `(specGraphE P C).flatInst` is borrowed along every path (silmaril's
  `LogicGraph.entails_lift_path_iff`).
* `ncToMax`, `ncToMax_modelExpansive`: litmus, the path `neverCall → act → ltlMax` over
  `wasmSem P`.
* `Inst.CoHom.lift_modelExpansive`, `liftGraph_pathModelExpansive`; **`fullGraph₃_pathModelExpansive`**:
  every path of the Wasm graph joined with the specification graph is model-expansive.

Not covered: cross edges between `fullGraph₂` and the specification graph (different interface
categories and models), harness reduction (a corridor at fixed interfaces, not a comorphism),
`wasmSem`/`wasmDivSem` (no semantics map: the divergence semantics has more traces), and the
non-expansive edges `jointWrap`, `jointIR` (only `env` is shown non-expansive).
-/
