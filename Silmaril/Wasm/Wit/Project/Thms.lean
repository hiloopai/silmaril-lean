module

public import Silmaril.Wasm.Wit.Project.Defs
public import Silmaril.Proofs.Wasm.Wit.Project

/-!
# The projection of a component to its world: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.Project`:

* `project_norm : project (norm c) = project c` and
  `project_read_print : (read (print c)).bind project = project c`: the
  projection is well defined on component WAT (it does not see section grouping
  or the spelling of attribute-free names);
* `project_stripCode : project (stripCode c) = project c`: code (core modules
  and instances, `canon`, `start`, nested components, custom sections) does not
  change the world; `project_not_injective`: the projection is many-to-one;
* `project_worldPackage`, `worldOf_project_worldPackage`: the binary package of
  a world (wit-component's layout) projects to the package's type, from which
  `worldOf` reads the world back in normal form
  (`worldOf_project_worldPackage_of_norm`: exactly, for normal worlds);
  `project_worldPackage_inj`: two worlds have the same package projection exactly
  when their normal forms agree;
* `packageItems_project_itemsPackage`: the binary package of several named items
  (wit-component's layout: item `k` is the type `2 k`, exported as `2 k + 1`;
  interfaces as instance types, worlds as wrapped component types), followed by
  custom sections, projects to declarations from which `packageItems` reads the
  items back in normal form;
* `normDefType_idem`, `normComponentDecls_idem`: the normal form is idempotent.

## Open

* the projection is partial: resource definitions, exports without type
  ascription (other than type exports), `(value (eq i))` bounds, outer aliases
  leaving the component and aliases of exports of created instances give `none`
  (type inference and resource renumbering are not done);
* validity: no theorem says that `project c` is a valid component type when `c`
  is a valid component (Silmaril has no validator for the binary AST);
* the relation with the IR's world (`Silmaril.Wasm.Wit.Project.IR`) through
  `Binary.lower` is not stated.
-/
