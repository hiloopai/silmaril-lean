module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Tests
public import Silmaril.Proofs.Wasm.Examples.LRAT.Accept

@[expose] public section

/-!
# The streaming LRAT checker: results

Proofs in `Silmaril.Proofs.Wasm.Examples.LRAT.*`. Every silmaril profile, every environment, every
host relation; no determinism assumption.

* the module checks RUP and RAT steps (`rat_begin`, `rat_end`); the invariant `Good` says that
  the clause database of the memory (`dbOf`) is satisfiable whenever the formula is (`sat`; in
  the input phase every model of the formula is one of the database), not that its clauses are
  implied;
* **`lrat_session_unsat`**: in every closed-world Core 3.0 session
  (`Silmaril.Wasm.Spec.Multi.Session`) of export calls on the instantiated checker `lratI`
  (`Silmaril.Wasm.Verify.instOf lratModule`), in any order and with any arguments, if a call of
  `unsat` answers a nonzero value, the CNF formula of the DIMACS stream sent before it
  (`streamOf`, by `add_lit`/`end_clause`) is unsatisfiable (`Silmaril.Logic.SAT.CNF.Unsat`);
* `lrat_spec`: every export meets its call specification (`Silmaril.Wasm.Examples.Common.callSpec`)
  for the representation `Rep xs s` ("the store's view satisfies `Good xs`", the invariant of
  `Silmaril.Wasm.Examples.LRAT.Defs`); `lrat_init`: the instantiated store represents the empty
  stream;
* the bodies, every run (`HWP`): `addLit_hwp` (also `end_clause`), `stepBegin_hwp`,
  `stepLit_hwp`, `stepHint_hwp` (the scan loop, `w_while` with `ScanInv`), `stepEnd_hwp`,
  `delete_hwp`, `unsat_hwp`, `ratBegin_hwp` (two `asg_loop`s), `ratEnd_hwp` (`outer_loop`
  around `scan_loop`); the invariant steps `Good.append`, …, `Good.hintConfl`, `Good.hintUnit`,
  `Good.closeGroup`, `Good.ratGroup`, `Good.ratCommit` (`GoodInput`, `GoodHint`, `GoodRat`);
* tests: `satTwo_never_unsat` (proved for every session), and `#guard` runs of the verified
  interpreter accepting three refutations (one with RAT steps) and rejecting bogus proofs
  (`Tests`).
* an accepted refutation, kernel-checked (`Accept`): **`unitPair_accepted`**
  (`wasmCheck unitPair unitPairProof = true`: the verified interpreter's run of the session of
  the unsatisfiable `[[1], [-1]]` and its one-step RUP refutation answers `1` to `unsat`) and
  **`unitPair_session`** (at every profile admitting the interpreter's deterministic steps and
  against every environment, a Core 3.0 `Session` of `lratI` with exactly these calls whose
  `unsat` answers `1`), by kernel evaluation through `Silmaril.Wasm.Verify.Kernel`
  (`runInvokeF_eq`) and `session_of_runCalls`.
-/
