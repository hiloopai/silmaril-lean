module

public import Silmaril.Wasm.Resource.Table.Defs
public import Silmaril.Proofs.Wasm.Resource.Table.Basic

@[expose] public section

/-!
# Handle tables of the component reference machine: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Table.Basic`.

* `add?_fresh`: `Table.add?` (`resource.new`) returns an index that held nothing, and changes only
  it; `remove?_live`: `Table.remove?` (`resource.drop`) succeeds only on a valid index and empties
  only it. Both keep the invariant `FreeOK`.
* **`table_steps_run`**, **`table_steps_accepts`**: every successful history of a handle table
  (`Table.Steps Table.empty evs t'`), read as handle events by `tableEv`, is accepted by
  `handleProto ℕ r` for **both** roles: fresh allocation (provider) and no use or drop of a dropped
  handle (client).
-/
