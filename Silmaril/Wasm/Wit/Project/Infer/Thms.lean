module

public import Silmaril.Wasm.Wit.Project.Infer.Defs
public import Silmaril.Proofs.Wasm.Wit.ProjectInfer

/-!
# The projection with type inference: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.ProjectInfer`:

* `projectI_of_projectX`, `projectI_of_project`: wherever `projectX` (or `project`) is
  defined, `projectI` is defined and equal. The proof is a simulation (`Ref`): the
  inferred descriptor tables refine those of `projectX` (`Le`), and every export
  `projectX` types gets the same type;
* `projectI_norm : projectI (norm c) = projectI c` and `projectI_read_print`: the
  inference does not see the WAT normal form (export tables are keyed by plain names,
  `tinfoOf_norm`);
* `projectX_composeExample`, `projectI_composeExample`: a WAC-style composition
  (instantiate an imported component with an imported instance, alias an instance
  export of the created instance and a function export of that, export both without
  ascription) has no `projectX` and has the expected world under `projectI`.

## Open

* inference through nested components (`Section.component`): their type would be
  their own projection, which needs a type index in the world;
* descriptors that refer to local types of an instance or component type other than
  outer aliases (inline type definitions, as `wit-component` writes them): lifting
  them needs new type definitions in the world, so the index-preserving replay leaves
  them unknown;
* `stripCode` invariance of `projectI` is not stated (as for `projectX`, it needs the
  function and component exports to be ascribed; the inferred types of aliases do not
  depend on code).
-/
