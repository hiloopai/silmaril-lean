module

public import Silmaril.Wasm.Component.Wat.Ids.Defs
public import Silmaril.Proofs.Wasm.Component.Wat.Ids

/-!
# Component WAT: symbolic identifiers, verified extension

Proofs in `Silmaril.Proofs.Wasm.Component.Wat.Ids`:

* `resolve_noIds`: on a component S-expression without identifiers, `resolve` is the
  identity;
* `readIds_of_noIds`: on such text `readIds` is `read`, so every property of `read`
  (for instance `Wat.read_print`) carries over: `readIds (print c) = some (norm c)`
  because the printer writes no identifiers.

That `resolve` assigns the right indices to identifiers is tested
(`tests/wat/Ids.lean`), not proved.
-/
