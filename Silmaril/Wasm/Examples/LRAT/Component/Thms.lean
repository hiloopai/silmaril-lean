module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Component.Sound

@[expose] public section

/-!
# The LRAT checker as a component: results

Proofs in `Silmaril.Proofs.Wasm.Examples.LRAT.Component.{Inst,Sound}`, every silmaril profile and
every component choice profile:

* the fragment conditions: `lratC_good`, `lratC_floatFree`, `lratC_arity`, `lratC_inst` (the
  module's instance is `lratI`: `lratNum_isInst`, and every instance is `lratI`: `isInst_eq`),
  and the reference validator accepts `lratC.toRef` (`lratC_valid`, kernel evaluation of
  `check?`);
* **`lratC_sound`**: in every behaviour of the reference machine that instantiates
  `lratC.toRef`, calls its exports `calls` (well typed) in order, each resolving, and then calls
  `is-unsat`, if `is-unsat` returns `true` then `(Dimacs.cnf (cstream calls)).Unsat`: the DIMACS
  formula sent by the `add-lit`/`end-clause` calls among `calls` is unsatisfiable.

The proof transfers the Core-level session invariant (`lrat_spec`, `Rep`, `CallOk`) through
`seq_refToSpec`: each returned call is a host-free Core run from the current store on the
lowered arguments (`retAt_rep`, `seqSpec_rep`), and the last call is an outcome of `specAt`
whose `bool` lift is `true` only for a nonzero core answer (`specAt_unsat`).

The component exports `rat-begin: func(j: u32)` and `rat-end: func()` as well, so RAT steps are
available at the component level; `lratC_sound` covers every call sequence.

Not covered: component-level completeness (a reference-machine behaviour in which `is-unsat`
returns `true` after a valid proof) needs the converse direction of `seq_refToSpec`, which the
reference soundness development does not provide. A list-based interface (`load-cnf: func(list<s32>)`) needs the linear-memory
canonical ABI (`realloc`, pointer/length pairs), which the reference soundness development does
not model yet.
-/
