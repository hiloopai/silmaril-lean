module

public import Silmaril.Cli.Demo.Defs
public import Silmaril.Cli.Args.Thms
public import Silmaril.Cli.Front.Thms
public meta import Silmaril.Cli.Demo.Defs

@[expose] public section

/-!
# The demo grammar: compiled examples

Kernel-checked (`decide`, `rfl`) and evaluated (`#guard`) examples of the derived parser,
renderer, resolution, help and error texts on `demo`, and instances of the general theorems of
`Silmaril.Cli.Args.Thms`. The guide `docs/projects/wasm-binaryen-tooling.md` quotes them.
-/

namespace Silmaril.Cli.Demo

open Silmaril.Cli

/-- The demo grammar is well formed. -/
theorem demo_wf : demo.WF := by decide

/-- One invocation of `demo`. -/
def inv₁ : Invocation :=
  [{ cmd := "demo", opts := [("verbose", .on)] },
   { cmd := "asyncify", opts := [("output", .val "out.wasm")], args := ["in.wasm"] }]

/-- Options may come after positionals; long names, `=`, and attached short values. -/
theorem scan_demo₁ :
    scan demo ["-v", "asyncify", "in.wasm", "-o", "out.wasm"] = .ok inv₁ ∧
    scan demo ["--verbose", "asyncify", "--output=out.wasm", "in.wasm"] = .ok inv₁ ∧
    scan demo ["-v", "asyncify", "-oout.wasm", "in.wasm"] = .ok inv₁ ∧
    scan demo ["-v", "asyncify", "-o=out.wasm", "in.wasm"] = .ok inv₁ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The normal form. -/
theorem render_demo₁ :
    render demo inv₁ = ["--verbose", "asyncify", "--output", "out.wasm", "in.wasm"] := by rfl

/-- The round trip, from the general theorem. -/
theorem scan_render_demo₁ : scan demo (render demo inv₁) = .ok inv₁ :=
  scan_render_scan demo_wf scan_demo₁.1

/-- Clusters: a counted flag `-vvv`, and a global flag after the subcommand clustered with an
option that takes the next token (`-qo out.wasm`). -/
theorem scan_demo_clusters :
    scan demo ["-vvv", "asyncify", "in.wasm", "-qo", "out.wasm"] =
      .ok [{ cmd := "demo", opts := [("verbose", .on), ("verbose", .on), ("verbose", .on)] },
        { cmd := "asyncify", opts := [("quiet", .on), ("output", .val "out.wasm")],
          args := ["in.wasm"] }] := by rfl

/-- An exact multi-letter token (`-O2`), a negated flag (`--no-selective`) and an optional
value (`--color`, `--color=never`), with their normal forms. -/
theorem scan_demo_tokens :
    scan demo ["--color", "asyncify", "-O2", "--no-selective", "-o", "b", "a"] =
      .ok [{ cmd := "demo", opts := [("color", .on)] },
        { cmd := "asyncify", opts := [("O2", .on), ("selective", .off), ("output", .val "b")],
          args := ["a"] }] ∧
    render demo [{ cmd := "demo", opts := [("color", .val "never")] },
        { cmd := "asyncify", opts := [("O2", .on), ("selective", .off), ("output", .val "b")],
          args := ["a"] }] =
      ["--color=never", "asyncify", "-O2", "--no-selective", "--output", "b", "a"] := by
  constructor <;> rfl

/-- `--` makes the rest positional; the renderer puts it back because the command has
subcommands. -/
theorem scan_demo₂ :
    scan demo ["run", "m.wasm", "--", "-x"] =
      .ok [{ cmd := "demo" }, { cmd := "run", args := ["m.wasm", "-x"] }] ∧
    render demo [{ cmd := "demo" }, { cmd := "run", args := ["m.wasm", "-x"] }] =
      ["run", "--", "m.wasm", "-x"] := by
  constructor <;> rfl

/-- Usage errors, located at the subcommand where they are found. -/
theorem scan_demo_errors :
    scan demo ["asyncify", "in.wasm", "-o"] = .error (["asyncify"], .missingValue "-o") ∧
    scan demo ["--selective"] = .error ([], .unknownOption "--selective") ∧
    scan demo ["asyncify", "--selective=yes"] =
      .error (["asyncify"], .unexpectedValue "--selective=yes") ∧
    scan demo ["asyncify", "-vx"] = .error (["asyncify"], .unknownOption "-vx") ∧
    scan demo ["frobnicate"] = .error ([], .unknownCommand "frobnicate") := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Adding a flag is a grammar morphism: every old command line keeps its parse. -/
theorem demo_extends : demo ⊑ demo.addOpt (flag "dry-run" ["n"]) :=
  extends_addOpt _ (by decide)

example : scan (demo.addOpt (flag "dry-run" ["n"]))
    ["-v", "asyncify", "in.wasm", "-o", "out.wasm"] = .ok inv₁ :=
  scan_extends demo_extends scan_demo₁.1

/-! ## Resolution and the front end (evaluated) -/

-- typed values, an alias (`r`), a default, an environment variable, `many` positionals
#guard interpret demo (fun v => if v == "DEMO_FUEL" then some "42" else none)
    ["r", "m.wasm", "f", "1", "2"] ==
  .run { path := ["run"], values := [("input", [.str "m.wasm"]), ("export", [.str "f"]),
    ("args", [.nat 1, .nat 2]), ("fuel", [.nat 42]), ("side", [.str "src"]),
    ("verbose", []), ("quiet", []), ("color", []), ("version", []), ("help", [])] }

-- a counted flag, a global flag given after the subcommand, a negated flag
#guard match interpret demo (fun _ => none)
    ["-vv", "asyncify", "a.wasm", "-qo", "b.wasm", "--selective", "--no-selective"] with
  | .run m => m.count "verbose" == 2 && m.flag "quiet" && m.str? "output" == some "b.wasm" &&
      m.nat? "pages" == some 1 && !m.switch "selective" true && m.path == ["asyncify"]
  | _ => false

-- usage errors from resolution, located at the subcommand
#guard interpret demo (fun _ => none) ["asyncify", "a.wasm"] ==
  .error ["demo", "asyncify"] (.missingOption "output")
#guard interpret demo (fun _ => none) ["run", "m.wasm", "f", "x"] ==
  .error ["demo", "run"] (.badValue "args" "x" .nat)
#guard interpret demo (fun _ => none) ["--color=sometimes", "run", "m", "f"] ==
  .error ["demo"] (.badValue "color" "sometimes" (.enum ["auto", "always", "never"]))
#guard interpret demo (fun _ => none) ["asyncify", "a", "b", "-o", "c"] ==
  .error ["demo", "asyncify"] (.extraArgument "b")
#guard interpret demo (fun _ => none) [] == .error ["demo"] (.missingCommand "demo")

-- help, version and exit codes
#guard interpret demo (fun _ => none) ["asyncify", "--help"] == .help ["demo", "asyncify"]
#guard interpret demo (fun _ => none) ["asyncify", "-qh"] == .help ["demo", "asyncify"]
#guard interpret demo (fun _ => none) ["-V"] == .version "0.1.0"
#guard (interpret demo (fun _ => none) ["-V"]).text demo == some (.stdout, "demo 0.1.0")
#guard (interpret demo (fun _ => none) ["--nope"]).exitCode? == some 2

#guard demo.help ["demo"] == "Instrument and run Wasm modules

Usage: demo [OPTIONS] <COMMAND>

Commands:
  asyncify  Run the verified pass
  run       Run an export

Options:
  -v, --verbose     Print more (repeat for more) [repeatable]
  -q, --quiet       Print less
  --color[=<WHEN>]  Colour output [possible values: auto, always, never]
  -V, --version     Print version
  -h, --help        Print help

Exit status:
  0  success
  1  the tool failed
  2  usage error"

#guard (demo.at ["demo", "asyncify"]).help ["demo", "asyncify"] == "Run the verified pass

Usage: demo asyncify [OPTIONS] --output <PATH> <INPUT>

Arguments:
  <INPUT>  Input module

Options:
  -o, --output <PATH>  Output file [required]
  --pages <N>          Memory pages [default: 1]
  --[no-]selective     Instrument only suspending calls [repeatable]
  -O2                  Optimise first
  -q, --quiet          Print less
  -h, --help           Print help"

-- the usage line of the subcommand where the error was found
#guard (interpret demo (fun _ => none) ["asyncify", "in.wasm", "-o"]).text demo ==
  some (.stderr, "error: a value is required for '-o' but none was supplied

Usage: demo asyncify [OPTIONS] --output <PATH> <INPUT>

For more information, try '--help'.")

/-! ## Real command lines -/

theorem wasmOpt_wf : wasmOpt.WF := by decide
theorem wasmTools_wf : wasmTools.WF := by decide

/-- `wasm-opt -O2 -all in.wasm -go out.wasm --vacuum --vacuum`. -/
theorem scan_wasmOpt :
    scan wasmOpt ["-O2", "-all", "in.wasm", "-go", "out.wasm", "--vacuum", "--vacuum"] =
      .ok [{ cmd := "wasm-opt"
             opts := [("O2", .on), ("all-features", .on), ("debuginfo", .on),
               ("output", .val "out.wasm"), ("vacuum", .on), ("vacuum", .on)]
             args := ["in.wasm"] }] := by rfl

/-- `wasm-tools parse -vv -to out.wat in.wat` and its normal form. -/
theorem scan_wasmTools :
    scan wasmTools ["parse", "-vv", "-to", "out.wat", "in.wat"] =
      .ok [{ cmd := "wasm-tools" },
           { cmd := "parse"
             opts := [("verbose", .on), ("verbose", .on), ("wat", .on), ("output", .val "out.wat")]
             args := ["in.wat"] }] ∧
    normalize wasmTools ["parse", "-vv", "-to", "out.wat", "in.wat"] =
      .ok ["parse", "--verbose", "--verbose", "--wat", "--output", "out.wat", "in.wat"] := by
  constructor <;> rfl

#guard match interpret wasmTools (fun _ => none)
    ["component", "new", "--merge-imports-based-on-semver=false", "m.wasm", "-o", "c.wasm"] with
  | .run m => m.path == ["component", "new"] &&
      m.str? "merge-imports-based-on-semver" == some "false" && m.str? "output" == some "c.wasm"
  | _ => false
#guard interpret wasmTools (fun _ => none) ["component", "new", "--merge-imports-based-on-semver=x"] ==
  .error ["wasm-tools", "component", "new"]
    (.badValue "merge-imports-based-on-semver" "x" (.enum ["true", "false"]))
#guard (interpret wasmTools (fun _ => none) ["component", "new", "-x"]).text wasmTools ==
  some (.stderr, "error: unexpected argument '-x' found

Usage: wasm-tools component new [OPTIONS] [INPUT]

For more information, try '--help'.")

/-! ## The front end as a behaviour specification -/

/-- What `demo` does once it runs: a loose spec, say, success with nothing on stderr. -/
def runSpec : Matches → Spec := fun _ => Spec.succeeds ⊓ Spec.silent

/-- `demo`'s `main`, read in the behaviour model, refines the interpreter's spec. -/
example : Beh.toSpec (demo.modelMain fun m => Beh.ofSpec (runSpec m)) ≤ demo.spec runSpec :=
  main_refines_ofSpec demo runSpec

/-- On `demo asyncify`, which lacks its required input, `demo` reports a usage error: exit 2,
nothing on stdout, files untouched. -/
example (i : Input) (hi : i.args = ["asyncify"]) (o : Obs) (h : demo.spec runSpec i o) :
    Spec.usageError i o := by
  refine spec_usageError ⟨["demo", "asyncify"], .missingOption "output", ?_⟩ h
  simp only [Command.outcome, hi]
  rfl

end Silmaril.Cli.Demo
