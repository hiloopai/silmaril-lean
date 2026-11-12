module

public import Silmaril.Cli.Getopt.Clap.Defs
public import Silmaril.Cli.Getopt.Thms
public import Silmaril.Cli.Clap.Thms
import Silmaril.Proofs.Cli.Getopt.Clap

/-!
# The getopt and clap dialects of one grammar (header)

One args grammar can be read with C's conventions (`Silmaril.Cli.Getopt.Tool`) and with Rust
clap's (`Silmaril.Cli.Clap.Tool`). Each dialect has a pre-pass that finds where it may read a
command line differently from the args front end `interpret`, and agrees with `interpret`
where its pre-pass passes (`Getopt.read_agrees`, `Clap.read_agrees`). So where both pre-passes
pass, the two dialects agree with each other.

PROVED (standard axioms; proof in `Silmaril.Proofs.Cli.Getopt.Clap`):

* **`read_clap`**: for a grammar both dialects can express (`Fits`; `Clap.HelpFlags`: help and
  version are flags) and an argument vector both pre-passes pass, in every environment, the
  clap reading agrees with the getopt reading (`Clap.Outcome.Agrees`: the same run, help or
  version, or usage errors on both sides); `Tool.read_clap` for the clap tool of a getopt tool
  (`Tool.clap`).

Where a pre-pass stops the dialects may differ; `Silmaril.Cli.Getopt.Clap.Examples` shows each
difference on one grammar: POSIX order, abbreviated long names, arguments that start with `-`,
an attached `=`, and help before a usage error.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-- **The clap and getopt readings agree** where both pre-passes pass. -/
theorem read_clap (tg : Tool) (tc : Clap.Tool) (hg : tc.grammar = tg.grammar)
    (env : String → Option String) (argv : List String) (hf : Fits tg.grammar)
    (hh : Clap.HelpFlags tg.grammar) (hpg : tg.pre env argv = none)
    (hpc : Clap.pre tc tc.grammar [tc.grammar.name] argv = none) :
    (tc.read env argv).Agrees (tg.read env argv) := by
  have h1 := Clap.read_agrees tc env (hg ▸ hh) hpc
  rw [hg] at h1
  exact Proofs.Cli.Getopt.agrees_clap h1 (read_agrees tg env argv hf hpg)

/-- The clap tool of a getopt tool agrees with it where both pre-passes pass. -/
theorem Tool.read_clap (t : Tool) (env : String → Option String) (argv : List String)
    (hf : Fits t.grammar) (hh : Clap.HelpFlags t.grammar) (hpg : t.pre env argv = none)
    (hpc : Clap.pre t.clap t.grammar [t.grammar.name] argv = none) :
    (t.clap.read env argv).Agrees (t.read env argv) :=
  Getopt.read_clap t t.clap rfl env argv hf hh hpg hpc

end Silmaril.Cli.Getopt
