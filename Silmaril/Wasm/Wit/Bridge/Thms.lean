module

public import Silmaril.Wasm.Wit.Bridge.Defs
public import Silmaril.Proofs.Wasm.Wit.Bridge

/-!
# The binary encoder and the projection: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.Bridge`:

* `allItemSections_eq : allItemSections items k = itemSecs k (asDefTypes items)`:
  wit-component's item layout (`Binary.encodeItems`) is the layout the
  projection reads (`Project.itemSecs`);
* `packageSections_itemsPackage`: the sections of a package's binary are
  `itemsPackage (asDefTypes items) cs` with `cs` custom sections;
* `project_encodePackage : encodePackage deps P = .ok b →` the bytes parse to a
  component `c` with `(project c).bind (packageItems 0)` the encoded items in
  WAT normal form;
* `world_project_encodePackage : P.Valid deps → encodePackage deps P = .ok b →`
  for every world `(n, w)` of `P`, the projection has an item `(n, d)` with
  `wrappedWorld d = some ds`, where `encodeWorld _ w = .ok ds` and
  `decWorld ds = .ok w.normalize`: **the WIT-encoded component of a world
  projects back to that world** (as the component type the encoder writes for
  it, which decodes to the world's normal form);
* `normComponentDecls_of_decWorld` (`Bridge/Plain`): what the world decoder
  reads is in WAT normal form, so the projection's normalisation is the
  identity on encoded worlds.
-/
