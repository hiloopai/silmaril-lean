module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Component.Sound

@[expose] public section

/-!
# The Farkas checker as a component: results

Proofs in `Silmaril.Proofs.Wasm.Examples.Farkas.Component.{Inst,Sound}`, every silmaril profile and
every component choice profile:

* the fragment conditions: `farkasS_good`, `farkasS_floatFree`, `farkasS_arity`,
  `farkasS_inst` (the module's instance is `farkasI`: `farkasNum_isInst`, and every instance is
  `farkasI`: `isInst_eq`), and the reference validator accepts `farkasS.toRef`
  (`farkasS_valid`, kernel evaluation of `check?`);
* **`farkasS_sound`**: in every behaviour of the reference machine that instantiates
  `farkasS.toRef`, calls its exports `calls` (well typed) in order, each resolving, and then
  calls `check`, if `check` returns `1` then `WRows.IsCert (cloaded calls)`: the rows loaded by
  `calls` since their last `check` carry a valid Farkas certificate;
* **`farkasS_infeasible`**: hence their system has no solution over any ordered field.

The proof transfers the Core-level session invariant (`farkas_spec`, `Rep`) through
`seq_refToSpec`: each returned call is a host-free Core run from the current store
(`retAt_rep`, `seqSpec_rep`), and the last call is an outcome of `specAt` (`specAt_check`).
-/
