module

public import Silmaril.Cli.Info.Thms
public import Silmaril.Cli.Guide.Thms
public import Silmaril.Cli.Spec.Asyncify.Thms
public import Silmaril.Cli.Spec.WasmOpt.Thms
public meta import Silmaril.Cli.Info.Defs
public meta import Silmaril.Cli.Guide.Defs
public meta import Silmaril.Cli.Spec.Asyncify.Defs

/-!
# Standard problems `--help` and `--version`: examples

* `greet` (`Silmaril.Cli.Guide`, args dialect, `withHelp` and `withVersion`): its spec and its
  Lean program meet `cli.help.either`, help over operands, `cli.version.short` and `cli.version.pinned "1.0.0"`; they do not meet
  `cli.help.wins`: `greet --help --bogus` is a usage error (`greetProg_not_wins`). A variant
  whose text must contain `Usage: greet` is met given that the text fits, which is checked by
  evaluation (`greet_usage_of`, `GreetUsageFits`).
* `wasm-asyncify` (`Silmaril.Cli.Spec.Asyncify`, clap dialect, `helpEverywhere`): help wins
  after every subcommand.
* `wasm-opt` (`Silmaril.Cli.Spec.WasmOpt`, clap dialect, help in its information options):
  `cli.help.wins`, by evaluating the trigger conditions.
* A program that prints a usage text and exits 1 (`badHelp`) fails `cli.help.basic` and meets
  `cli.help.loose`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Info.Examples

open Silmaril.Cli Silmaril.Cli.Io Silmaril.Cli.Info Silmaril.Cli.Guide

/-! ## `greet`: the args dialect -/

theorem greet_helpOpt : helpOpt ∈ greetCmd.opts :=
  helpOpt_mem_withVersion (helpOpt_mem_withHelp _) _

/-- `greet --help`, `greet -h`, and after them help or a usage error. -/
theorem greet_either (S : Matches → Spec) : greetCmd.spec S ≤ HelpVariant.either.sen :=
  greetCmd.spec_le_help greetCmd_wf greet_helpOpt rfl rfl rfl rfl
    (rootOnly rfl greetCmd (fun h => by cases h)) S

/-- `greet` has no subcommands, so help wins over operands: `greet --help ada`. -/
def greetOperands : HelpVariant := { short := true, extra := .winsOperands }

theorem greet_operands (S : Matches → Spec) : greetCmd.spec S ≤ greetOperands.sen :=
  greetCmd.spec_le_help greetCmd_wf greet_helpOpt rfl rfl rfl rfl
    (rootOnly rfl greetCmd (fun _ => rfl)) S

/-- A variant whose help text must name the program and show a usage line. -/
def greetUsage : HelpVariant := { reply := { mentions := ["Usage: greet"] } }

/-- The help text fits (checked by evaluation: the kernel does not reduce the UTF-8 encoding of
a computed help text). -/
abbrev GreetUsageFits : Prop := greetUsage.Fits [] (greetCmd.helpBytes [])

#guard greetCmd.helpTriggers greetUsage
#guard decide GreetUsageFits

/-- With the text condition evaluated above, `greet` meets the variant. -/
theorem greet_usage_of (h : GreetUsageFits) (S : Matches → Spec) :
    greetCmd.spec S ≤ greetUsage.sen :=
  spec_help (by decide +kernel) (fun p hp => by
    simp only [greetUsage, HelpVariant.roots, List.mem_singleton] at hp
    subst hp; exact h) S

/-- `greet --version` and `greet -V` print `greet 1.0.0`. -/
theorem greet_version (S : Matches → Spec) :
    greetCmd.spec S ≤ (VersionVariant.pinned "1.0.0").sen :=
  greetCmd.spec_le_version greetCmd_wf (versionOpt_mem_withVersion _ _) rfl
    (by simp [VersionVariant.pinned]) (by simp [VersionVariant.pinned]) S

theorem greet_versionShort (S : Matches → Spec) :
    greetCmd.spec S ≤ VersionVariant.basicShort.sen :=
  greetCmd.spec_le_version greetCmd_wf (versionOpt_mem_withVersion _ _) rfl
    (by simp [VersionVariant.basicShort]) (by simp [VersionVariant.basicShort]) S

/-- **The Lean program meets the standard problems for free**: it is `Prog.ofCommandCore` on
the grammar, whatever its core does. -/
theorem greetProg_help : greetProg.Sat HelpVariant.either.sen :=
  Prog.ofCommand_sat_help (by decide +kernel)
    (fun p _ => HelpVariant.fits_line rfl rfl p _) _

theorem greetProg_version : greetProg.Sat (VersionVariant.pinned "1.0.0").sen :=
  ((Prog.sat_ofCommandCore_iff greetCmd _ fun _ => ⊤).mpr fun _ _ _ => trivial).mono (greet_version _)

/-- As a model of the institution. -/
theorem greetProg_model : greetProg.model.Sat HelpVariant.either.sen :=
  (Prog.model_sat_iff _ _).mpr greetProg_help

-- the args dialect reads the whole command line before it answers help
#guard (greetProg.obs { args := ["--help", "--bogus"] }).exit == 2
#guard (greetProg.obs { args := ["--help", "ada"] }).exit == 0
#guard !greetCmd.helpTriggers HelpVariant.wins

/-- **`greet` does not meet `cli.help.wins`**: `greet --help --bogus` is a usage error. -/
theorem greetProg_not_wins : ¬ greetProg.Sat HelpVariant.wins.sen := by
  intro h
  have hx : (greetProg.obs { args := ["--help", "--bogus"] }).exit = 2 := by decide +kernel
  have hs := ((h { args := ["--help", "--bogus"] }).1 [] List.mem_cons_self).2.2 "--help"
    (by simp [HelpVariant.tokens, HelpVariant.wins]) ["--bogus"] (by simp) rfl
  have h0 : (greetProg.obs { args := ["--help", "--bogus"] }).exit = 0 := hs.1.1
  rw [hx] at h0
  exact absurd h0 (by decide)

/-! ## `wasm-asyncify`: the clap dialect, help on every command -/

/-- `--help` and `-h` at the root and after every subcommand; help wins over what follows. -/
def asyncifyHelp : HelpVariant :=
  { short := true, extra := .wins,
    paths := [["asyncify"], ["run-src"], ["run-tgt"], ["example"], ["examples"]] }

theorem asyncify_help (S : Matches → Spec) :
    Spec.Asyncify.tool.spec S ≤ asyncifyHelp.sen :=
  Clap.Tool.spec_le_help rfl Spec.Asyncify.tool_wf rfl rfl (by decide) (fun h => by cases h)
    (by decide +kernel) S

#guard Clap.helpTriggers Spec.Asyncify.tool asyncifyHelp
-- clap has no `help` subcommand here
#guard !Clap.helpTriggers Spec.Asyncify.tool { word := true }

/-! ## `wasm-opt`: the clap dialect, help among the information options -/

theorem wasmOpt_wins (S : Matches → Spec) : Spec.WasmOpt.tool.spec S ≤ HelpVariant.wins.sen :=
  Clap.spec_help rfl (by decide +kernel) (fun p _ => HelpVariant.fits_line rfl rfl p _) S

/-! ## A program that answers help with exit 1 -/

/-- Prints a usage text and exits 1, whatever it is given. -/
def badHelp : Prog ExitCode := .out .stdout (utf8 "usage: bad [OPTIONS]\n") (.exit 1)

theorem badHelp_obs (i : Input) :
    badHelp.obs i = { stdout := utf8 "usage: bad [OPTIONS]\n", exit := 1, fs := i.fs } := rfl

/-- **It fails `cli.help.basic`**: the exit code of `bad --help` is 1. -/
theorem badHelp_not_basic : ¬ badHelp.Sat HelpVariant.basic.sen := by
  intro h
  have hs := ((h { args := ["--help"] }).1 [] List.mem_cons_self).1 "--help"
    (by simp [HelpVariant.tokens, HelpVariant.basic]) rfl
  have h0 : (badHelp.obs { args := ["--help"] }).exit = 0 := hs.1.1
  rw [badHelp_obs] at h0
  exact absurd h0 (by decide)

/-- **It meets `cli.help.loose`** (any exit code). -/
theorem badHelp_loose : badHelp.Sat HelpVariant.loose.sen := by
  intro i
  rw [badHelp_obs]
  have hne : utf8 "usage: bad [OPTIONS]\n" ≠ [] := by decide +kernel
  have hs : ∀ p, HelpVariant.loose.Shows p
      { stdout := utf8 "usage: bad [OPTIONS]\n", stderr := [], exit := 1 } := fun p =>
    ⟨⟨trivial, trivial, fun _ => by simpa [HelpVariant.loose, Dest.text] using hne,
      fun m hm => by simp [HelpVariant.loose] at hm⟩, fun q hq => by simp [HelpVariant.loose] at hq⟩
  exact ⟨fun p _ => ⟨fun _ _ _ => hs p, fun hw => by simp [HelpVariant.loose] at hw,
    fun _ _ _ _ _ => trivial⟩, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## The registry ids -/

#guard (HelpVariant.named.map (·.1)) ==
  ["cli.help.basic", "cli.help.short", "cli.help.loose", "cli.help.wins", "cli.help.either"]
#guard (VersionVariant.named.map (·.1)) == ["cli.version.basic", "cli.version.short"]

end Silmaril.Cli.Info.Examples
