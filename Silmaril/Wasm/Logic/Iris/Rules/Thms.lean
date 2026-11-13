module

public import Silmaril.Wasm.Logic.Iris.Rules.Defs
public import Silmaril.Proofs.Wasm.Logic.Iris.Control

/-!
# The Iris logic of Wasm Core 3.0: rules

Weakest-precondition rules for `IExpr P host` (`Silmaril.Wasm.Logic.Iris.Language.Defs`),
for **every profile** `P` and **every host relation** `host`. Every rule is in
continuation style: the instruction sits under values `vs` and before the rest of
the code `rest`, and the premise asks, a later, for the weakest precondition of
the code it steps to. Proofs are in `Silmaril/Proofs/Wasm/Logic/Iris`.

* lifting (`Lifting.lean`): `wp_run` (the lifting lemma of the language),
  `wp_exit` (an exit, also a trap or an exception still bubbling out of a
  sequence), `wp_head` (an inert plain instruction, through silmaril-lean's
  `Det.Head`, after `Silmaril.Wasm.Logic.Hoare.Safe.head`); with owned cells
  (`Base.lean`): `wp_head_cells`, `wp_head_read`, `wp_head_change`;
* outcomes (`Control.lean`): `wp_vals`, `wp_trap`, `wp_throwing`, `wp_br`,
  `wp_return`, `wp_tail` (the postcondition is indexed by the outcome);
* locals and globals (`Variable.lean`): `wp_localGet`, `wp_localSet`,
  `wp_globalGet`, `wp_globalSet`;
* linear memory (`Memory.lean`, `Grow.lean`): `wp_intLoad`, `wp_intStore`
  (full-width `i32`/`i64`, any address type, so memory64 and multiple memories),
  `wp_memoryGrow` (both outcomes, in every profile);
* tables (`Table.lean`): `wp_tableGet`, `wp_tableSet`;
* GC (`Aggregate.lean`): `wp_structNew`, `wp_structGet`, `wp_structGet_null`,
  `wp_structSet`, `wp_arrayNewFixed`, `wp_arrayGet`, `wp_arraySet`, `wp_arrayLen`;
* arithmetic and exceptions (`Control.lean`): `wp_intBinOp`, `wp_intBinOp_trap`,
  `wp_throw`.

Every instruction rule is proved from silmaril-lean's head-step inversions
(`Silmaril/Proofs/Wasm/Logic/Iris/Head.lean` for globals, memory, tables and
arrays; `Silmaril.Wasm.Logic.Hoare`'s `head_*` for locals, structures,
`memory.grow`, `throw` and integer operators), so it covers every run.
-/
