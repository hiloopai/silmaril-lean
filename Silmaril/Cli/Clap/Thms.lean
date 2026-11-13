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

/-! ## The reading depends on the grammar and `helpSub` only

The presentation (`present`, `after`, `long`, `choices`, `usageExit`) does not change what a
command line reads to: two tools with the same grammar and the same `helpSub` read every
argument vector alike (`Tool.read_congr`). A tool that differs from another only in how it
prints its outcomes (`{ t with present := p }`) therefore inherits its reading. -/

theorem step_congr {t u : Tool} (hs : t.helpSub = u.helpSub) (c : Command)
    (path : List String) (tok : String) (rest : List String) :
    step t c path tok rest = step u c path tok rest := by
  simp only [step, hs]

/-- The pre-pass depends on the tool only through `helpSub`. -/
theorem pre_congr {t u : Tool} (hs : t.helpSub = u.helpSub) (n : Nat) :
    ∀ (c : Command) (path argv : List String), argv.length ≤ n →
      pre t c path argv = pre u c path argv := by
  induction n with
  | zero => intro c path argv h; cases argv <;> simp_all [pre]
  | succ n ih =>
    intro c path argv h; cases argv with
    | nil => rfl
    | cons tok rest =>
      have hl : rest.length ≤ n := by simpa using h
      rw [pre, pre, step_congr hs]
      split
      · rfl
      · rfl
      · exact ih c path rest hl
      · exact ih _ _ rest hl
      · split
        · rfl
        · split
          · rfl
          · exact ih c path _ (by simp only [List.length_cons] at hl; omega)

/-- **The reading depends on the grammar and `helpSub` only.** -/
theorem Tool.read_congr {t u : Tool} (hg : t.grammar = u.grammar) (hs : t.helpSub = u.helpSub)
    (env : String → Option String) (argv : List String) : t.read env argv = u.read env argv := by
  have hr : ∀ fs, t.readInv env fs = u.readInv env fs := by
    intro fs; unfold Tool.readInv Tool.message nameOf; simp only [hg]
  unfold Tool.read
  rw [pre_congr hs argv.length t.grammar [t.grammar.name] argv (Nat.le_refl _), hg]
  simp only [hr]

/-- A tool with its own presentation reads as the tool it was built from. -/
theorem Tool.read_present (t : Tool) (p : Option (List String → Outcome → String))
    (env : String → Option String) (argv : List String) :
    ({ t with present := p } : Tool).read env argv = t.read env argv :=
  Tool.read_congr (t := { t with present := p }) (u := t) rfl rfl env argv

end Silmaril.Cli.Clap
