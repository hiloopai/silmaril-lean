module

public import Silmaril.Wasm.Resource.Extern.Defs
public import Silmaril.Proofs.Wasm.Resource.Extern.Basic

@[expose] public section

/-!
# Handle protocols for `externref` handles: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Extern.Basic`: `uClientSpec_oTotal`,
`uProviderSpec_oTotal` (environment moves never break the sentences) and **`untyped_accepts`**
(a protocol invariant of `U.lts P` gives acceptance of every play of `U.strategy P`, every
profile).
-/
