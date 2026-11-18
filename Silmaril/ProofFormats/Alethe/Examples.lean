module

public import Silmaril.ProofFormats.Alethe.Thms
public meta import Silmaril.ProofFormats.Alethe.Thms

/-!
# Alethe refutations from cvc5, checked

The fixtures in `tests/alethe/cvc5-1.4.2/` are SMT-LIB problems and the Alethe proofs that the
official cvc5 1.4.2 release printed for them (`receipt.json`: the archive and executable SHA-256,
the exact arguments, and every file's hash; `scripts/alethe/check-fixtures.sh` verifies the hashes
and, given the executable, regenerates the proofs). The checks below read them at build time:

* **accepted**: `p1` (`or_pos` and resolution), `p2` (`or`), `p3` (`and` with an index), `p5`
  (`and`, `or`, `or_pos` and four-way resolution, with `:named` sharing), each returning the
  problem's assertions, which `checkRefutation_sound` then refutes;
* **refused**: `p4`, whose proof uses the theory rule `not_symm`; `p2-no-pivots`, the same problem
  printed without `--proof-alethe-res-pivots`;
* **mutations** of the real files, each refused with its reason: a step's conclusion changed, an
  assertion changed in the problem, a premise that names a later step, the final step removed, a
  `define-fun` in the problem, and an `anchor` command.
-/

public section

namespace Silmaril.ProofFormats.Alethe.Examples

open Silmaril.ProofFormats.Alethe

meta def dir : String := "tests/alethe/cvc5-1.4.2/"

meta def expect (what : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"Alethe regression: {what}")

meta def check (problem proof : String) : Except AletheError (List Silmaril.Logic.Smt.SE) :=
  checkRefutation problem.toUTF8.toList proof.toUTF8.toList

/-- The error, if any. -/
meta def err (r : Except AletheError (List Silmaril.Logic.Smt.SE)) : Option AletheError :=
  match r with
  | .error e => some e
  | .ok _ => none

#eval do
  let file (n : String) := IO.FS.readFile (dir ++ n)
  -- accepted, refuting exactly the problem's assertions
  for (p, n) in [("p1", 3), ("p2", 4), ("p3", 2), ("p5", 5)] do
    match check (← file s!"{p}.smt2") (← file s!"{p}.alethe") with
    | .ok φs => expect s!"{p}: {φs.length} assertions" (φs.length == n)
    | .error e => throw (IO.userError s!"Alethe regression: {p} refused: {repr e}")
  -- refused real proofs
  expect "p4 uses not_symm"
    (err (check (← file "p4.smt2") (← file "p4.alethe")) == some (AletheError.unsupportedRule "t0" "not_symm"))
  expect "p2 without pivots"
    (match err (check (← file "p2.smt2") (← file "p2-no-pivots.alethe")) with
      | some (.badArgs "t2" _) => true
      | _ => false)
  -- mutations of real files
  let p5 ← file "p5.alethe"
  let p5smt ← file "p5.smt2"
  expect "a changed conclusion"
    (err (check p5smt (p5.replace "(step t3 (cl @p_2)" "(step t3 (cl s)")) == some AletheError.rejected)
  expect "a changed assertion"
    (err (check (p5smt.replace "(assert (or (not q) s))" "(assert (or (not q) p))") p5) ==
      some (AletheError.notAnAssertion "a2"))
  expect "a later premise"
    (err (check p5smt (p5.replace ":premises (t1 t2)" ":premises (t1 t9)")) ==
      some (AletheError.unknownPremise "t3" "t9"))
  expect "no final step"
    (err (check p5smt (p5.replace "(step t9 (cl) :rule resolution :premises (a0 t8) :args (@p_1 true))" "")) ==
      some AletheError.notRefutation)
  expect "define-fun"
    (match err (check (p5smt.replace "(check-sat)" "(define-fun z () Bool p)\n(check-sat)") p5) with
      | some (.problem _) => true
      | _ => false)
  expect "anchor"
    (match err (check p5smt (p5.replace "(step t9 " "(anchor :step t10)\n(step t9 ")) with
      | some (.command _ _) => true
      | _ => false)

end Silmaril.ProofFormats.Alethe.Examples
