module

public import Silmaril.Cli.Clap.Defs
public import Silmaril.Cli.Front.Defs
public import Silmaril.Cli.Io.Check.Defs

/-!
# Programs behind a clap front end, and their specification

`Silmaril.Cli.Front` reads the args front end (`interpret`) as a behaviour specification,
`Command.spec`, and runs programs behind it with `Command.main`. This module does the same for
the **clap dialect** (`Silmaril.Cli.Clap`: `Tool.read`, the reading the pinned tools are specified
with), so that a real tool can parse its arguments with the very reading its specification
uses:

* `Tool.text t argv out`: what the front end prints on an outcome that does not run, derived
  from the grammar: the `-h` help of the command (`Surface.Command.help`, clap's layout) on
  stdout; the version line on stdout; a group without a subcommand: its help on stderr; a usage
  error: `error: MSG`, a blank line, the usage line of the command the error is located at
  (`Tool.errorPath`), and, when the grammar has a help flag, `For more information, try
  '--help'.`, on stderr;
* **`Tool.main t run argv`** (`IO`; `Tool.mainWith` for any `Host`): read the declared
  environment variables, `Tool.read`, print the text and exit with the outcome's code (0, or
  the tool's `usageExit`), else call `run` on the matches (also on `.undecided` outcomes: the
  program checks the values the grammar leaves to it);
* **`Tool.spec t S`**: the specification of such a program, as `Command.spec` for the args
  dialect: on matches `m`, `S m` (on an undecided outcome, `S m` or a loose usage error);
  otherwise exactly the text above with its exit code, nothing else touched.
  `Silmaril.Cli.Clap.Main.Thms`: `Tool.main` read in the behaviour model refines it
  (`Tool.main_refines`), and `Tool.frontCheck`, the harness check of `Tool.spec t ⊤`, is sound
  (`Tool.frontCheck_sound`).

`wasm-asyncify` and the component tools run behind `Tool.main` with their pinned grammars
(`Silmaril.Cli.Spec.*`), and `wasm-opt` prints its derived help through `Tool.text`;
see docs/projects/wasm-binaryen-tooling.md.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

/-! ## Help on every command -/

/-- clap's `-h, --help` of one command (not inherited: every command lists its own). -/
def helpFlag : Opt := { id := "help", short := ["h"], help := "Print help" }

mutual
/-- `c` with clap's help flag on every command, after the command's own options. -/
def Command.helpEverywhere : Command → Command
  | ⟨n, al, ab, os, ps, subs, req, ex, v, ck, rl⟩ =>
    ⟨n, al, ab, os ++ [helpFlag], ps, Command.helpEverywhereAll subs, req, ex, v, ck, rl⟩
/-- `helpEverywhere` of a list. -/
def Command.helpEverywhereAll : List Command → List Command
  | [] => []
  | s :: ss => s.helpEverywhere :: Command.helpEverywhereAll ss
end

end Silmaril.Cli

namespace Silmaril.Cli.Clap

open Silmaril.Cli

/-! ## The program -/

/-- The subcommand path the words of `argv` name (options skipped), from `c` at `path`: where
the pre-pass stopped early, the command its message is about. -/
def wordsPath : Command → List String → List String → List String
  | _, path, [] => path
  | c, path, w :: rest =>
    if w == "--" then path else
    if optionLike w then wordsPath c path rest else
    match findSub c.subs w with
    | some s => wordsPath (c.child s) (path ++ [s.name]) rest
    | none => path

/-- The command path (program name first) an outcome of the reading is located at: the frames
of the parsed invocation, the path of a located parse error, else (the pre-pass stopped) the
subcommands the words name. -/
def Tool.errorPath (t : Tool) (argv : List String) : List String :=
  match pre t t.grammar [t.grammar.name] argv with
  | none =>
    match scan t.grammar argv with
    | .ok fs => fs.map (·.cmd)
    | .error (p, _) => t.grammar.name :: p
  | some _ => wordsPath t.grammar [t.grammar.name] argv

/-- A text without its final newlines (the host's `putLine` adds one). -/
def chomp (s : String) : String := String.ofList (s.toList.reverse.dropWhile (· == '\n')).reverse

/-- The derived `-h` help of the command at `path` (program name first). -/
def Tool.helpText (t : Tool) (path : List String) : String :=
  match t.surface.root.find? (path.drop 1) with
  | some c => chomp (c.help path)
  | none => ""

/-- The derived usage line of the command at `path` (program name first). -/
def Tool.usageText (t : Tool) (path : List String) : String :=
  match t.surface.root.find? (path.drop 1) with
  | some c => c.usage path
  | none => ""

/-- Whether the grammar's root has the help flag. -/
def Tool.hasHelp (t : Tool) : Bool := t.grammar.opts.any isHelpOpt

/-- The text of a usage error on `argv`. -/
def Tool.errorText (t : Tool) (argv : List String) (msg : String) : String :=
  "error: " ++ msg ++ "\n\n" ++ t.usageText (t.errorPath argv) ++
    (if t.hasHelp then "\n\nFor more information, try '--help'." else "")

/-- **What the front end prints** on an outcome of the reading of `argv` (nothing when the
program runs). -/
def Tool.text (t : Tool) (argv : List String) : Outcome → Option (Channel × String)
  | .run _ _ | .undecided _ _ _ => none
  | .help p => some (.stdout, t.helpText p)
  | .version => some (.stdout, t.grammar.name ++ " " ++ t.grammar.version.getD "")
  | .needCommand p => some (.stderr, t.helpText p)
  | .error msg => some (.stderr, t.errorText argv msg)

/-- What the program does with an outcome: run with the matches, or print the text and exit
with the outcome's code. -/
def Tool.finish {m : Type → Type} [Monad m] (h : Host m) (t : Tool) (argv : List String)
    (run : Matches → m UInt32) : Outcome → m UInt32
  | .run _ mt => run mt
  | .undecided _ mt _ => run mt
  | out => h.emit (t.text argv out) >>= fun _ => pure ((out.exit t).getD 0).toUInt32

/-- **A program behind the clap front end**, for any host: read the declared environment
variables, `Tool.read` the arguments, print help, version or usage errors, else call `run`. -/
def Tool.mainWith {m : Type → Type} [Monad m] (h : Host m) (t : Tool)
    (run : Matches → m UInt32) (argv : List String) : m UInt32 :=
  h.getEnvs t.grammar.envVars >>= fun env => t.finish h argv run (t.read env argv)

/-- Run a program behind the clap front end in `IO`. -/
def Tool.main (t : Tool) (run : Matches → IO UInt32) (argv : List String) : IO UInt32 :=
  t.mainWith Host.io run argv

/-- **Only the help of the clap front end**: on a command line the reading answers with help,
print the derived help (exit 0); hand every other command line to `other`, which reads it
itself (a tool adopting the grammar step by step, as `wasm-opt` does). -/
def Tool.helpOr {m : Type → Type} [Monad m] (t : Tool) (h : Host m) (other : List String → m UInt32)
    (argv : List String) : m UInt32 :=
  h.getEnvs t.grammar.envVars >>= fun env =>
    match t.read env argv with
    | .help p => h.emit (t.text argv (.help p)) >>= fun _ => pure 0
    | _ => other argv

/-! ## The specification -/

/-- What the clap front end decides on an invocation. -/
def Tool.outcome (t : Tool) (i : Input) : Outcome := t.read (t.grammar.envOf i) i.args

/-- The observation of a non-running outcome: its text with a newline, its exit code, nothing
else. -/
def Tool.frontObs (t : Tool) (i : Input) (out : Outcome) : Obs :=
  { Beh.lineObs i (t.text i.args out) with exit := ((out.exit t).getD 0).toUInt32.toUInt8 }

/-- **The specification of a program behind the clap front end** (`Command.spec` for the clap
dialect): on matches `m`, `S m`; on an undecided outcome, `S m` or a loose usage error;
otherwise exactly `frontObs`. -/
def Tool.spec (t : Tool) (S : Matches → Spec) : Spec := fun i o =>
  match t.outcome i with
  | .run _ m => S m i o
  | .undecided _ m _ => S m i o ∨ Spec.usageError i o
  | out => o = t.frontObs i out

/-- **The front end alone**: anything on the outcomes that run. -/
def Tool.frontSpec (t : Tool) : Spec := t.spec fun _ => ⊤

/-- `Tool.main` read in the behaviour model. -/
def Tool.modelMain (t : Tool) (run : Matches → Beh UInt32) : Beh UInt32 :=
  Beh.withArgs (t.mainWith Beh.host run)

/-- Whether an outcome runs the program. -/
def Outcome.runs : Outcome → Bool
  | .run _ _ | .undecided _ _ _ => true
  | _ => false

/-- **The harness check of `Tool.frontSpec`**: on a non-running outcome, exactly the derived
text on the right channel, nothing on the other, the outcome's exit code and no file changed. -/
def Tool.frontCheck (t : Tool) : Io.Check := fun i s =>
  let out := t.outcome i
  if out.runs then true else
    let o := t.frontObs i out
    s.stdout == o.stdout && s.stderr == o.stderr && s.exit == o.exit && s.files.isEmpty

end Silmaril.Cli.Clap
