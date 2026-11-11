module

public import Silmaril.Cli.Surface.Defs
public import Silmaril.Cli.Io.Check.Defs

/-!
# The front ends of pinned tools as behaviour specifications

The command line of a real tool can be pinned as a surface (`Silmaril.Cli.Surface`), with a
reference reading `Command.parse` of an argument vector. This module reads a surface as a **behaviour
specification** of the tool's front end, so the test harness can check the binaries against it:

`Tool.spec t body`: on an argument vector the reading runs (`.run inv`), `body inv`; otherwise
the front end alone, with no file changed:

* help (`-h`, `--help`, `help SUB`): exit `0`, nothing on stderr, and stdout shows the derived
  usage line of the command (`usageOf`) modulo whitespace (clap's long `--help` text differs
  from the `-h` layout the surface derives, but both carry the usage line; the full `-h` text
  is compared separately, against `Command.help`);
* version: exit `0`, nothing on stderr, something on stdout;
* a missing subcommand: the tool's usage exit code, nothing on stdout, and stderr shows the
  usage line;
* a usage error: the tool's usage exit code, nothing on stdout, a message on stderr.

`Tool.frontSpec t := Tool.spec t fun _ => ⊤` says nothing about runs. `Tool.check t body` is
the harness check, sound (`Silmaril.Cli.Io.Surface.Thms.Tool.check_sound`).

What the reading leaves out (value types, requires/conflicts rules) is a run here, so a tool
that rejects such a vector with a usage error still meets `frontSpec`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Surface

open Silmaril.Cli Silmaril.Cli.Io

/-- The whitespace-separated words of a text. -/
def words (s : String) : List String :=
  ((s.toList.map fun c => if c.isWhitespace then ' ' else c).splitOn ' ').filterMap fun w =>
    if w.isEmpty then none else some (String.ofList w)

/-- The words of the text the bytes `b` show (none when `b` is not UTF-8). -/
def bytesWords (b : Bytes) : List String :=
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => words s
  | none => []

/-- The derived usage line of the command at `path` (program name first). -/
def Tool.usageOf (t : Tool) (path : List String) : String :=
  match t.root.find? (path.drop 1) with
  | some c => c.usage path
  | none => ""

/-- The bytes `b` show the usage line of the command at `path`. -/
def Tool.ShowsUsage (t : Tool) (path : List String) (b : Bytes) : Prop :=
  words (t.usageOf path) <:+: bytesWords b

/-- **What the front end prints and exits with** on an outcome that does not run (files
aside). -/
def Tool.FrontOut (t : Tool) (res : Outcome) (o : Obs) : Prop :=
  match res with
  | .run _ => True
  | .help path => o.exit = 0 ∧ o.stderr = [] ∧ t.ShowsUsage path o.stdout
  | .version _ => o.exit = 0 ∧ o.stderr = [] ∧ o.stdout ≠ []
  | .needCommand path => o.exit = t.usageExit.toUInt8 ∧ o.stdout = [] ∧ t.ShowsUsage path o.stderr
  | .error _ => o.exit = t.usageExit.toUInt8 ∧ o.stdout = [] ∧ o.stderr ≠ []

instance (t : Tool) (res : Outcome) (o : Obs) : Decidable (t.FrontOut res o) := by
  unfold Tool.FrontOut Tool.ShowsUsage
  split <;> infer_instance

/-- **The behaviour of a tool with the surface `t`**: the front end, then `body inv` on the
invocations the reading runs. -/
def Tool.spec (t : Tool) (body : Invocation → Spec) : Spec := fun i o =>
  match t.root.parse i.args with
  | .run inv => body inv i o
  | res => t.FrontOut res o ∧ o.fs = i.fs

/-- **The front end only**: anything on runs. -/
def Tool.frontSpec (t : Tool) : Spec := t.spec fun _ => ⊤

/-- What a snapshot shows, files aside. -/
def snapObs (s : Snap) (i : Input) : Obs :=
  { stdout := s.stdout, stderr := s.stderr, exit := s.exit, fs := i.fs }

/-- **The harness check of `Tool.spec t body`.** -/
def Tool.check (t : Tool) (body : Invocation → Check) : Check := fun i s =>
  match t.root.parse i.args with
  | .run inv => body inv i s
  | res => decide (t.FrontOut res (snapObs s i)) && s.files.isEmpty

/-- The check of the front end only. -/
def Tool.frontCheck (t : Tool) : Check := t.check fun _ _ _ => true

end Silmaril.Cli.Surface

end
