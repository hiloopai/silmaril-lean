module

public import Silmaril.Proofs.Wasm.Examples.Common.Exec
public import Silmaril.Proofs.Wasm.Examples.Common.Session

@[expose] public section

/-!
# Verified Wasm examples: shared results

Proofs in `Silmaril.Proofs.Wasm.Examples.Common.{Exec,Session}`, at every profile and for every
host relation:

* **`Wp.exec`** (and `Wp.exec_eq`, `Wp.exec1`): symbolic execution of straight-line code
  (`Silmaril.Wasm.Logic.Core.exec`: integer arithmetic, locals, globals, integer loads and stores)
  in the every-run logic, either reading (`HWP`/`TWP`): every instruction `exec` evaluates is a
  profile-free family head step, so the evaluated result is the **only** continuation;
* `FSpecValid.of_body_hwp`: a function specification from an every-run proof of the body
  that returns or traps (`bodyPost`);
* `FSpecValid.result_post`: a Core run of `$invoke` ending in a result satisfies the
  postcondition at that result's outcome;
* **`session_allGood`**: if every export call of a scalar instance meets
  `callSpec I R next Good` under the session's host, every closed-world session
  (`Silmaril.Wasm.Spec.Multi.Session`) from a store representing `a` is `AllGood`;
  `allGood_append`: the call after a prefix `l₁` is `Good` in the state `after next a l₁`.
-/
