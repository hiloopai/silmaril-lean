module

public import Silmaril.Cli.Clap.Defs
public import Silmaril.Proofs.Cli.Clap.Lex

/-!
# The clap dialect: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Cli.Clap.Lex`, namespace `Silmaril.Cli.Clap`):

* **`read_agrees`**: for every tool whose help and version options are flags (`HelpFlags`,
  decidable) and every argument vector the clap pre-pass passes (`pre … = none`), the clap
  reading agrees with the args front end: `(t.read env argv).Agrees (interpret t.grammar env
  argv)` (the same run, help or version, usage errors on both sides; a value the checks
  leave undecided runs in the args front end). This covers clap's own spellings: clusters
  `-vx`, attached values `-ofile` and `-o=file`, optional values `--validate[=V]` with their
  missing value, exact tokens `-O2`. The proof goes token by token: `readOpt_step`
  (one option token) and `readCluster_cluster` (a cluster, letter by letter) show that where
  the pre-pass goes on, the args parser reads the same token, consumes the same next token and
  reads only options that are neither the help nor the version flag (`scans_quiet`, by
  induction on the grammar `Scans`);
* **`pre_render`**, **`read_render`**: the pre-pass passes the args normal form of a valid
  `Plain` invocation of a well-formed grammar, so `t.read env (render t.grammar fs) =
  t.readInv env fs`;
* `read_run_scan`, **`read_run_valid`**: what the reading runs is what `scan` (sound and
  complete for the grammar: `scanAux_eq_ok_iff`) read from the argument vector itself, hence a
  `Valid` invocation; **`read_run_render`**: its normal form reads back to the same outcome.

Where the pre-pass stops early the two front ends may differ, by design: clap answers help
before reading the rest (`-h --bogus`), refuses a value that looks like an option
(`-o --stats`) and has no `--no-x` negations.

The exit codes (`Outcome.exit`) are simp lemmas below. The derived clap view
(`Tool.surface`) and the comparison with its reference reading (`compare`) are checked by
evaluation on example tools (`Silmaril.Cli.Clap.Examples`), not proved.
-/

@[expose] public section

namespace Silmaril.Cli.Clap

open Silmaril.Cli

@[simp] theorem Outcome.exit_run (t : Tool) (fs : Invocation) (m : Matches) :
    (Outcome.run fs m).exit t = none := rfl
@[simp] theorem Outcome.exit_undecided (t : Tool) (fs : Invocation) (m : Matches) (w : String) :
    (Outcome.undecided fs m w).exit t = none := rfl
@[simp] theorem Outcome.exit_help (t : Tool) (p : List String) :
    (Outcome.help p).exit t = some 0 := rfl
@[simp] theorem Outcome.exit_version (t : Tool) : Outcome.version.exit t = some 0 := rfl
@[simp] theorem Outcome.exit_needCommand (t : Tool) (p : List String) :
    (Outcome.needCommand p).exit t = some t.usageExit := rfl
@[simp] theorem Outcome.exit_error (t : Tool) (msg : String) :
    (Outcome.error msg).exit t = some t.usageExit := rfl

/-- Help found by the pre-pass is the reading's outcome. -/
theorem read_early {t : Tool} {env : String → Option String} {argv : List String} {p : List String}
    (h : pre t t.grammar [t.grammar.name] argv = some (.help p)) :
    t.read env argv = .help p := by
  simp only [Tool.read, h]

end Silmaril.Cli.Clap
