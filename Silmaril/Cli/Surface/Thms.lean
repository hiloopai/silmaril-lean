module

public import Silmaril.Cli.Surface.Defs

/-!
# CLI surfaces: first laws

Small laws of the reference reading `Command.parse` and of the exit codes. The derived
parser of `Silmaril.Cli.Args` carries the full soundness and completeness theorems; these are
the facts pinned surfaces of real tools use.
-/

@[expose] public section

namespace Silmaril.Cli.Surface

@[simp] theorem Outcome.exit_run (inv : Invocation) : (Outcome.run inv).exit = none := rfl
@[simp] theorem Outcome.exit_help (p : List String) : (Outcome.help p).exit = some 0 := rfl
@[simp] theorem Outcome.exit_version (p : List String) : (Outcome.version p).exit = some 0 := rfl
@[simp] theorem Outcome.exit_error (m : String) : (Outcome.error m).exit = some 2 := rfl
@[simp] theorem Outcome.exit_needCommand (p : List String) :
    (Outcome.needCommand p).exit = some 2 := rfl

@[simp] theorem Tool.exitOf_run (t : Tool) (inv : Invocation) : t.exitOf (.run inv) = none := rfl
@[simp] theorem Tool.exitOf_error (t : Tool) (m : String) :
    t.exitOf (.error m) = some t.usageExit := rfl

/-- A tool with clap's convention fixes the same exit codes as `Outcome.exit`. -/
theorem Tool.exitOf_eq_exit (t : Tool) (h : t.usageExit = 2) (o : Outcome) :
    t.exitOf o = o.exit := by
  cases o <;> simp [Tool.exitOf, Outcome.exit, h]

/-- After `--`, every token is a positional argument: the reading of the rest is the final
checks on the state with those tokens appended. -/
theorem Parse.go_dd (ts : List String) (st : Parse.St) (h : st.dd = true) :
    Parse.go ts st = Parse.finish { st with args := ts.reverse ++ st.args } := by
  induction ts generalizing st with
  | nil => simp [Parse.go]
  | cons t ts ih =>
    rw [Parse.go]
    simp only [h, ↓reduceIte]
    rw [ih _ rfl]
    simp

/-- The reading of `-- ARGS…` on a command: `ARGS` are its positionals. -/
theorem Command.parse_dd (c : Command) (args : List String) :
    c.parse ("--" :: args) =
      Parse.finish { cmd := c, path := [c.name], args := args.reverse, dd := true } := by
  have hne : ("--" == "--") = true := by decide
  simp only [Command.parse, Parse.go, hne, Bool.false_eq_true, ↓reduceIte]
  rw [Parse.go_dd _ _ rfl]
  simp

end Silmaril.Cli.Surface
