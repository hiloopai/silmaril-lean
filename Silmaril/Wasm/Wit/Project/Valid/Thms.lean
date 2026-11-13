module

public import Silmaril.Wasm.Wit.Project.Valid.Defs
public import Silmaril.Proofs.Wasm.Wit.ProjectValid

/-!
# Validity of projected worlds: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.ProjectValid`:

* `projectX_wellScoped : wellScopedC c → projectX c = some w → wellScoped w` and
  `project_wellScoped`: the projection of a well-scoped component is a well-scoped
  component type. The invariant (`Inv`) says that the type index spaces of the
  component and of the world stay aligned (`wc.t = k.t = tCount`), that every instance
  the replay maps is an instance of the world, and that the descriptor tables and the
  hoisted resources only use bound types;
* `wellScopedC_resComponent`: an example.

## Open

* validity beyond index scoping (type equality and subtyping of ascriptions and
  `canon lift` types, name uniqueness and kebab case, resource rules, the inner
  scopes of nested types) is not checked: Silmaril has no full validator for the
  component binary AST;
* `projectI` (inference) is not covered: the descriptors it lifts from instance and
  component types are not checked to have the sort of the alias that reads them.
-/
