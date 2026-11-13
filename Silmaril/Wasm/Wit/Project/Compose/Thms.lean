module

public import Silmaril.Wasm.Wit.Project.Compose.Defs
public import Silmaril.Proofs.Wasm.Wit.ProjectCompose

/-!
# The projection and composition: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.ProjectCompose`. Let `projState c = some s` (the
projection with inference of `c` succeeded, its world is `s.x.base.decls`).

* `projState_extend`: extending `c` continues the projection from `s` (the
  look-ahead for resource exports found its exports in `c` and keeps them,
  `resExport_append_of_some`), so the projection is compositional in the items
  appended;
* `projectI_instantiateC`: instantiating a component keeps the world (the created
  instance is internal);
* `projectI_aliasC_func`: aliasing a function keeps the world;
* `projectI_aliasC_created`: aliasing an instance export of a created instance keeps
  the world; `projectI_aliasC_world`: aliasing one of an imported or exported instance
  `i` (world index `j`) appends `(alias export j n (instance))`;
* `projectI_exportC`: exporting a function, instance or component appends
  `(export n d)` with its ascribed or inferred descriptor `d`;
* `composeExample_ops`: the composition `composeExample` is `composeBase` extended by
  these operations (same projection, `projectI_composeExample`).

## Open

* type exports and exports of resources (hoisting) are not covered by
  `projectI_exportC`; values (`(value (eq i))`) are not projected at all;
* the operations act on one component; composing two components into a new one
  (nesting both, as `wac` does) needs the projection of nested components
  (`Section.component`), which inference does not provide yet.
-/
