import Silmaril.Cli.Spec.WasmTools.Defs
import Silmaril.Cli.Spec.WasmOpt.Defs
import Silmaril.Cli.Spec.Asyncify.Defs
import Silmaril.Cli.Spec.WasmVerify.Defs
import Silmaril.Cli.Spec.Jco.Defs
import Silmaril.Cli.Spec.Wac.Defs
import Silmaril.Cli.Clap.Help.Defs
import Silmaril.Cli.Clap.Main.Defs

/-!
# `cli-spec`: print what a pinned CLI specification says

Test driver of `docs/projects/wasm-binaryen-tooling.md` (section "apply"). Its own command line is an args
grammar (`CliSpec.grammar`) read in the clap dialect, so its help is derived too.

```
cli-spec tools                    the pinned tools
cli-spec paths TOOL               every command path of TOOL, one per line
cli-spec show TOOL [PATH]...      the derived `-h` help of a command path
cli-spec text TOOL [-l] [-w N] [PATH]...
                                  the derived help of a command path in clap's exact layout
                                  (`Clap.Help`; `-l`: the long help of `--help`; `-w`: the
                                  width, as COLUMNS sets it)
cli-spec run TOOL [ARGV]...       what the front end prints on ARGV (`Clap.Tool.text`: help,
                                  version, usage errors) on the channel it uses, and its exit code;
                                  `run` (exit 0, nothing printed) when ARGV runs the program
cli-spec rows TOOL [PATH]...      the positionals and options of a command path: id, then the
                                  left column of its help row (tab-separated)
cli-spec parse TOOL [ARGV]...     the reading of ARGV (`Clap.Tool.read`) and its exit class
cli-spec corpus TOOL              argument vectors derived from the grammar, one per line
                                  (tab-separated), each after the exit class the reading gives:
                                  0, the usage exit, run, or run|N (a value left to the program)
cli-spec compare TOOL             the corpus vectors on which the reading and the reference
                                  reading of the clap view differ, with the verdict
cli-spec errors TOOL              the corpus vectors the reading refuses, each after the first
                                  line of its message (tab-separated)
```

The corpus (`Surface.Command.corpus` of the derived clap view) exercises every command path:
help, unknown options, too many positionals, `--`, and for every option a valid use, a missing
value, an unexpected value and a repetition. `tools/cli-spec/tests/wasm-tools-surface.sh` runs
it against the pinned binary, `tools/cli-spec/tests/pinned-tools.sh` against the Lean tools.
-/

open Silmaril.Cli

namespace CliSpec

def tools : List (String × Clap.Tool) :=
  [("wasm-tools", Silmaril.Cli.Spec.WasmTools.tool),
   ("wasm-opt", Silmaril.Cli.Spec.WasmOpt.tool),
   ("wasm-asyncify", Silmaril.Cli.Spec.Asyncify.tool),
   ("wasm-verify", Silmaril.Cli.Spec.WasmVerify.tool),
   ("wasm-jco", Silmaril.Cli.Spec.Jco.tool),
   ("wasm-wac", Silmaril.Cli.Spec.Wac.tool)]

def toolPos : Pos := { id := "tool", type := .enum (tools.map (·.1)) }

def sub (name about : String) (pos : List Pos) : Command :=
  { name, about, pos, opts := [{ helpOpt with help := "Print help" }] }

/-- The command line of `cli-spec` itself. -/
def grammar : Command where
  name := "cli-spec"
  about := "Print what a pinned CLI specification says"
  opts := [{ helpOpt with help := "Print help" }]
  subs := [
    sub "tools" "List the pinned tools" [],
    sub "paths" "List the command paths of a tool" [toolPos],
    sub "show" "Print the derived help of a command path"
      [toolPos, { id := "path", arity := .many }],
    { sub "text" "Print the derived help of a command path in clap's exact layout"
        [toolPos, { id := "path", arity := .many }] with
      opts := [{ id := "long", short := ["l"], help := "The long help (`--help`)" },
        { id := "width", short := ["w"], arg := some .str, metavar := "N",
          help := "clap's terminal width (as from COLUMNS; at most 100)" },
        { helpOpt with help := "Print help" }] },
    sub "run" "Print what the front end prints on an argument vector, with its exit code"
      [toolPos, { id := "argv", arity := .many }],
    sub "rows" "Print the arguments of a command path with the left column of their help row"
      [toolPos, { id := "path", arity := .many }],
    sub "parse" "Read an argument vector" [toolPos, { id := "argv", arity := .many }],
    sub "corpus" "Print argument vectors derived from the grammar, with their exit class"
      [toolPos],
    sub "compare" "Print the corpus vectors on which the reading and the reference differ"
      [toolPos],
    sub "errors" "Print the corpus vectors the reading refuses, after the first line of the message"
      [toolPos]]

def self : Clap.Tool := { grammar }

end CliSpec

open CliSpec in
def main (args : List String) : IO UInt32 := do
  let surface := self.surface.root
  match self.read (fun _ => none) args with
  | .help path =>
    match surface.find? (path.drop 1) with
    | some c => IO.print (c.help path); return 0
    | none => return 2
  | .needCommand path =>
    IO.eprint (surface.help path); return 2
  | .error msg =>
    IO.eprintln s!"error: {msg}\n\n{surface.usage ["cli-spec"]}\n\nFor more information, try '--help'."
    return 2
  | .version => return 0
  | .undecided _ m _ | .run _ m =>
    if m.path == ["tools"] then
      tools.forM fun (n, _) => IO.println n
      return 0
    let some tool := (m.str? "tool").bind (fun t => tools.lookup t) | return 2
    match m.path with
    | ["paths"] =>
      tool.surface.root.paths.forM fun p => IO.println (" ".intercalate p)
      return 0
    | ["show"] =>
      let path := m.strs "path"
      match tool.surface.root.find? path with
      | some c => IO.print (c.help (tool.grammar.name :: path)); return 0
      | none => IO.eprintln s!"error: no command path {path}"; return 2
    | ["text"] =>
      let path := m.strs "path"
      match tool.grammar.walk path with
      | some _ =>
        IO.print (tool.clapHelp path (m.flag "long") (Clap.Help.widthOf (m.str? "width")))
        return 0
      | none => IO.eprintln s!"error: no command path {path}"; return 2
    | ["run"] =>
      let argv := m.strs "argv"
      let o := tool.read (fun _ => none) argv
      match tool.text argv o with
      | some (.stdout, s) => IO.println s
      | some (.stderr, s) => IO.eprintln s
      | none => IO.println "run"
      return ((o.exit tool).getD 0).toUInt32
    | ["rows"] =>
      let path := m.strs "path"
      match tool.grammar.walk path with
      | some c =>
        c.pos.forM fun p => IO.println (p.id ++ "\t" ++ (Clap.surfacePos p).spec)
        c.opts.forM fun o => IO.println (o.id ++ "\t" ++ (Clap.surfaceOpt o).spec)
        return 0
      | none => IO.eprintln s!"error: no command path {path}"; return 2
    | ["parse"] =>
      let o := tool.read (fun _ => none) (m.strs "argv")
      IO.println (repr o).pretty
      IO.println s!"exit: {o.cls tool}"
      return 0
    | ["corpus"] =>
      tool.surface.root.corpus.forM fun argv =>
        IO.println ((tool.read (fun _ => none) argv).cls tool ++ "\t" ++ "\t".intercalate argv)
      return 0
    | ["compare"] =>
      (Clap.disagreements tool).forM fun (argv, v) =>
        IO.println (s!"{repr v}".replace "\n" " " ++ "\t" ++ "\t".intercalate argv)
      return 0
    | ["errors"] =>
      tool.surface.root.corpus.forM fun argv =>
        match tool.read (fun _ => none) argv with
        | .error msg => IO.println ("error: " ++ ((msg.splitOn "\n").headD "") ++ "\t" ++
            "\t".intercalate argv)
        | _ => pure ()
      return 0
    | _ => return 2
