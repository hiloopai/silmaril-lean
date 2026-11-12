module

public import Silmaril.Cli.Getopt.Stream.Defs
import Silmaril.Proofs.Cli.Getopt.Stream

/-!
# getopt as a stream of results: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Cli.Getopt.Stream`):

* **Going on after errors**: **`parseAll_ok`** (without a usage error the loop reads what
  `parse` reads: the same options in order, operands and `--`), **`parseAll_error`** (when
  `parse` stops at an error, that error is the loop's first diagnostic), hence
  `parseAll_errors_nil` (the loop reports no diagnostic exactly when `parse` succeeds) and
  `parseAll_opts` (then a program that skips `?` sees the options of `parse`);
* **Operands in order**: **`parseInOrder_permute`**: the results of the in-order reading, split
  into options and operands, are the GNU permuting reading.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-- **Without a usage error the loop reads what `parse` reads.** -/
theorem parseAll_ok {t : Table} {ord : Order} {argv : List String} {p : Parsed}
    (h : parse t ord argv = .ok p) : parseAll t ord argv = Report.ofParsed p :=
  Proofs.Cli.Getopt.parseAll_ok h

/-- **The first diagnostic of the loop is the error `parse` stops at.** -/
theorem parseAll_error {t : Table} {ord : Order} {argv : List String} {e : Error}
    (h : parse t ord argv = .error e) : (parseAll t ord argv).errors.head? = some e :=
  Proofs.Cli.Getopt.parseAll_error h

/-- The loop reports no diagnostic exactly when `parse` succeeds. -/
theorem parseAll_errors_nil {t : Table} {ord : Order} {argv : List String} :
    (parseAll t ord argv).errors = [] ↔ ∃ p, parse t ord argv = .ok p := by
  cases h : parse t ord argv with
  | ok p =>
    simp only [parseAll_ok h, Except.ok.injEq, exists_eq', iff_true]
    exact Proofs.Cli.Getopt.ofOpts_error p.opts
  | error e =>
    have he := parseAll_error h
    constructor
    · intro hn; rw [hn] at he; cases he
    · rintro ⟨_, hp⟩; cases hp

/-- Without a usage error, a program that skips `?` sees the options `parse` reads. -/
theorem parseAll_opts {t : Table} {ord : Order} {argv : List String} {p : Parsed}
    (h : parse t ord argv = .ok p) : (parseAll t ord argv).opts = p.opts := by
  rw [parseAll_ok h]
  exact Proofs.Cli.Getopt.ofOpts_opt p.opts

/-- **The in-order reading, its interleaving forgotten, is the GNU permuting reading.** -/
theorem parseInOrder_permute (t : Table) (argv : List String) :
    (parseInOrder t argv).map splitInOrder =
      (parse t .permute argv).map fun p => (p.opts, p.operands) :=
  Proofs.Cli.Getopt.parseInOrder_permute argv

end Silmaril.Cli.Getopt
