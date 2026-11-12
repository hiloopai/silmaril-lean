module

public import Silmaril.Wasm.Wit.Project.Ext.Defs
public import Silmaril.Proofs.Wasm.Wit.ProjectExt

/-!
# The extended projection: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.ProjectExt`:

* `projectX_of_project : project c = some w → projectX c = some w` (conservative);
* `project_resComponent`, `projectX_resComponent`: a component defining and exporting
  a resource and its constructor without ascriptions has no `project` but has a
  `projectX`, the expected world (strictly larger domain).

## Open

* `projectX` is not proved invariant under `Wat.norm` (`project_norm`'s analogue) nor
  under `stripCode`; the look-ahead and the descriptor tables make the replay depend
  on more than the type and instance index spaces;
* exports of aliased functions, instances created by instantiation and nested
  components still need type inference (they give `none`);
* validity of the projected component type is not proved.
-/
