module

public import Silmaril.Logic.SAT.LRAT.Defs
public import Silmaril.Proofs.Logic.SAT.LRAT.Basic
public import Silmaril.Proofs.Logic.SAT.LRAT.Rat
public import Silmaril.Proofs.Logic.SAT.LRAT.Examples

@[expose] public section

/-!
# A reference LRAT checker: results

Proofs in `Silmaril.Proofs.Logic.SAT.LRAT.{Basic,Rat,Examples}`:

* **`check_sound`**: `check F proof = true → F.Unsat`, for RUP and RAT steps, from
  **`run_unsat`**: a successful run refutes the clauses of its starting database (`clauses`;
  `clauses_init`: those of `init 1 F` are `F`);
* **`ratOk_sat`**: a valid RAT step keeps the database satisfiable, from the semantic RAT lemma
  **`CNF.sat_cons_of_rat`** (a model falsifying the new clause is repaired by making the pivot
  true, `Assignment.flip`); `Step.sat_apply`: every valid step keeps the database satisfiable,
  so `F.Sat → (clauses db).Sat` holds along a run (`sat_init`). RAT clauses are not implied by
  `F`, and the converse `(clauses db).Sat → F.Sat` fails after deletions;
* **`addOk_implies`**: a valid RUP addition is implied by `F` when every database clause is
  (`Implied F db`), from **`rup_sound`**: successful propagation contradicts every assignment
  satisfying `F` and agreeing with the starting partial assignment (`Agrees`: every assumed
  literal is nonzero and true); `Lit.eval_neg` (negation flips a nonzero literal);
* `run_sound`: a run from a database implied by `F` refutes `F` (`implied_init`,
  `Implied.delete`, `Implied.cons` remain for RUP-only reasoning).

Examples: `fourClauses_unsat` (all four clauses over two variables) and `php32_unsat`
(pigeonhole PHP(3, 2), with a deletion step) by `decide` and `check_sound`; the satisfiable
`satTwo` (`satTwo_sat`) and `zeroUnit` (`zeroUnit_sat`, the literal `0`) with bogus proofs
rejected (`satTwo_bogus_rejected`, `zeroUnit_rejected`); `fourClausesRat_check` (a refutation
through two RAT steps, the first of which no hint list justifies by RUP, `fresh_not_rup`) and
`rat_bogus_rejected`.

Not covered: completeness (every RUP/RAT-derivable refutation has an accepted proof); a relation
to Lean core's `Std.Tactic.BVDecide.LRAT.check`.
-/
