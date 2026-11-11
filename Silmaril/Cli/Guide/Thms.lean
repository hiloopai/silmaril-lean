module

public import Silmaril.Cli.Guide.Defs
public import Silmaril.Cli.Args.Thms
public import Silmaril.Cli.Io.Command.Thms
public meta import Silmaril.Cli.Guide.Defs

/-!
# The CLI spec API on one page: theorems and evaluated examples

The compiled examples of the guide at the top of `docs/projects/cli.md`.

PROVED (standard axioms), namespace `Silmaril.Cli.Guide`:

* `greetCmd_wf`: the grammar is well formed (`decide`);
* `greet_sat`: the program built from the pure core meets the spec derived from the grammar;
* `greetCheck_sound`: the harness check is sound for the spec;
* `greet_quiet`, `greet_quiet_scan`: adding a flag is a grammar morphism, so every old command
  line parses the same.

Evaluated (`#guard`): parses, environment and defaults, help, usage errors, exit codes, the
normal form and the help text.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Guide

open Silmaril.Cli Silmaril.Cli.Io

/-! ## The grammar and its derived front end -/

theorem greetCmd_wf : greetCmd.WF := by decide

#guard match interpret greetCmd (fun _ => none) ["-s", "ada"] with
  | .run m => m.flag "shout" && m.str? "greeting" == some "hello" && m.strs "name" == ["ada"]
  | _ => false
-- the environment comes after the command line and before the default
#guard match interpret greetCmd (fun v => if v == "GREETING" then some "hi" else none) ["ada"] with
  | .run m => m.str? "greeting" == some "hi"
  | _ => false
#guard interpret greetCmd (fun _ => none) ["--help"] == .help ["greet"]
#guard (interpret greetCmd (fun _ => none) ["--help"]).exitCode? == some 0
#guard (interpret greetCmd (fun _ => none) ["--bogus", "ada"]).exitCode? == some 2
#guard (interpret greetCmd (fun _ => none) ["ada"]).exitCode? == none
-- the normal form: first long names, values as separate tokens
#guard normalize greetCmd ["-s", "--greeting=hey", "ada"] ==
  .ok ["--shout", "--greeting", "hey", "ada"]

-- the help text is a function of the grammar, so it cannot drift from it
#guard greetCmd.help ["greet"] == "\n".intercalate [
  "Greet someone",
  "",
  "Usage: greet [OPTIONS] <NAME>",
  "",
  "Arguments:",
  "  <NAME>  Who to greet",
  "",
  "Options:",
  "  -s, --shout         Print in capitals",
  "  --greeting <VALUE>  The greeting [default: hello] [env: GREETING]",
  "  -h, --help          Print help",
  "  -V, --version       Print version",
  "",
  "Exit status:",
  "  0  success",
  "  2  usage error"]

/-! ## The program meets the spec -/

theorem greet_sat : greetProg.Sat greetSpec :=
  (Prog.sat_ofCommandCore_iff _ _ _).2 fun i _ _ => by
    rw [Result.obs_nil _ _ _ _ _ rfl]
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, rfl⟩

/-! ## The check is sound -/

theorem greetCheck_sound : greetCheck.Sound greetSpec :=
  Command.check_sound _ fun m i s h => by
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hx, ho⟩, he⟩, hf⟩ := h
    have hfs : s.fs i = i.fs := by
      funext q
      simp [Snap.fs, hf]
    exact ⟨{ stdout := greetLine m, fs := i.fs }, ⟨ho.symm, he.symm, hx.symm, hfs.symm⟩,
      rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

/-! ## Growing the CLI -/

theorem greet_quiet : greetCmd ⊑ greetCmd.addOpt quiet := extends_addOpt _ (by decide)

theorem greet_quiet_scan {argv : List String} {fs : Invocation} (h : scan greetCmd argv = .ok fs) :
    scan (greetCmd.addOpt quiet) argv = .ok fs :=
  scan_extends greet_quiet h

end Silmaril.Cli.Guide

end
