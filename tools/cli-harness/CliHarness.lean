import Silmaril.Cli.Io.Run.Defs
import Silmaril.Cli.Io.Echon.Defs
import Silmaril.Cli.Io.Surface.Defs
import Silmaril.Cli.Spec.WasmTools.Defs
import Silmaril.Cli.Spec.WasmOpt.Defs
import Silmaril.Cli.Spec.Asyncify.Defs
import Silmaril.Cli.Spec.WasmVerify.Defs
import Silmaril.Cli.Spec.Jco.Defs
import Silmaril.Cli.Spec.Wac.Defs
import Silmaril.Cli.Clap.Main.Defs

/-!
# `cli-harness`

Runs a binary on the cases of a suite and checks every observation against the suite's
decidable check (`Check`), which `Silmaril.Cli.Io.Check.Thms` proves sound for the behaviour
specification the Lean programs are proved to satisfy (`Check.Sound`). See `docs/projects/wasm-binaryen-tooling.md`.

```
cli-harness SUITE -- CMD [ARGS…]          SUITE ∈ echo, cat, copy, echon
cli-harness surface TOOL -- CMD [ARGS…]   TOOL ∈ wasm-tools, wasm-opt, wasm-asyncify,
                                          wasm-verify
cli-harness front TOOL -- CMD [ARGS…]     TOOL ∈ wasm-asyncify, wasm-jco, wasm-wac,
                                          wasm-opt (help vectors only)
```

`front TOOL` runs every vector of the clap view's corpus and checks the binary against the
clap front end's specification `Clap.Tool.frontSpec` (exactly the derived help, usage-error
text and exit code on the vectors that do not run) with `Clap.Tool.frontCheck`, proved sound
(`Silmaril.Cli.Clap.Main.Thms`: `Tool.frontCheck_sound`). The Lean tools run behind
`Clap.Tool.main`, so this replaces the looser `surface` check (`Tool.frontSpec` of
`Silmaril.Cli.Io.Surface`) for them; `wasm-opt` takes only its help from the grammar
(`Clap.Tool.helpOr`), so only the vectors that ask for help are checked.

`surface TOOL` runs every argument vector of the surface's corpus (`Surface.Command.corpus`)
and checks the front end against `Tool.frontSpec` with `Tool.frontCheck`
(`Silmaril.Cli.Io.Surface`); it prints one line per failure and a summary.

Each case runs `CMD ARGS… case-args…` in a fresh temporary directory with the case's files, an
empty inherited environment plus the case's, and the case's stdin. Exit status: `0` when every
case passes, `1` when one fails, `2` on a usage error.
-/

open Silmaril.Cli Silmaril.Cli.Io Silmaril.Cli.Io.Examples Silmaril.Cli.Io.Echon

/-- Deterministic pseudo-random bytes. -/
def noise (n seed : Nat) : Bytes := Id.run do
  let mut x := seed
  let mut out : Array UInt8 := #[]
  for _ in [0:n] do
    x := (x * 1103515245 + 12345) % 2147483648
    out := out.push (x / 65536 % 256).toUInt8
  pure out.toList

def echoCases : List Case :=
  [ { name := "no-args" },
    { name := "one", args := ["a"] },
    { name := "spaces", args := ["a", "b c", "d"] },
    { name := "empty-arg", args := ["", "x"] },
    { name := "utf8", args := ["héllo", "wörld", "λ"] },
    { name := "dashes", args := ["--", "-n", "--help"] } ]

def catCases : List Case :=
  [0, 1, 4095, 4096, 4097, 70000].map fun n =>
    { name := s!"{n}B", stdin := noise n (n + 7) }

def copyCases : List Case :=
  [ { name := "ok", args := ["in.bin", "-o", "out.bin"], files := [("in.bin", noise 1000 3)] },
    { name := "ok-empty", args := ["in.bin", "-o", "out.bin"], files := [("in.bin", [])] },
    { name := "ok-subdir", args := ["d/in.bin", "-o", "./out.bin"],
      files := [("d/in.bin", noise 77 5)] },
    { name := "missing", args := ["nope.bin", "-o", "out.bin"] },
    { name := "usage", args := ["in.bin"], files := [("in.bin", noise 10 4)] } ]

def echonCases : List Case :=
  [ { name := "none" },
    { name := "words", args := ["a", "b c"] },
    { name := "no-newline", args := ["-n", "x", "y"] },
    { name := "sep", args := ["--sep", ",", "a", "b"] },
    { name := "sep-eq", args := ["--sep=-", "a", "b"] },
    { name := "sep-env", args := ["a", "b"], env := [("ECHON_SEP", "+")] },
    { name := "sep-arg-over-env", args := ["--sep", ":", "a", "b"], env := [("ECHON_SEP", "+")] },
    { name := "dashdash", args := ["--", "-n", "--help"] },
    { name := "help", args := ["--help"] },
    { name := "help-short", args := ["-h"] },
    { name := "version", args := ["--version"] },
    { name := "unknown-option", args := ["--bogus"] },
    { name := "missing-value", args := ["a", "--sep"] } ]

def suite : String → Option (Check × List Case)
  | "echo" => some (echoCheck, echoCases)
  | "cat" => some (catCheck, catCases)
  | "copy" => some (copyCheck, copyCases)
  | "echon" => some (echonCheck, echonCases)
  | _ => none

def surfaces : List (String × Silmaril.Cli.Surface.Tool) :=
  [("wasm-tools", Silmaril.Cli.Spec.WasmTools.wasmTools),
   ("wasm-opt", Silmaril.Cli.Spec.WasmOpt.tool.surface),
   ("wasm-asyncify", Silmaril.Cli.Spec.Asyncify.tool.surface),
   ("wasm-verify", Silmaril.Cli.Spec.WasmVerify.tool.surface)]

/-- The class of a vector's outcome, for the report. -/
def outcomeClass : Silmaril.Cli.Surface.Outcome → String
  | .run _ => "run"
  | .help _ => "help"
  | .version _ => "version"
  | .needCommand _ => "need-command"
  | .error _ => "usage-error"

def runSurface (name : String) (cmd : String) (pre : List String) : IO UInt32 := do
  let some t := surfaces.lookup name
    | IO.eprintln s!"cli-harness: unknown surface {name}"; return 2
  let vecs := t.root.corpus
  let mut fails := 0
  let mut counts : List (String × Nat) := []
  for v in vecs do
    let c : Case := { name := " ".intercalate v, args := v }
    let s ← runBinary cmd pre c
    let cls := outcomeClass (t.root.parse v)
    counts := match counts.lookup cls with
      | some n => (cls, n + 1) :: counts.filter (·.1 != cls)
      | none => (cls, 1) :: counts
    if !(t.frontCheck c.input s) then
      IO.println s!"FAIL: {name} [{cls}] {c.name}: {showSnap s}"
      fails := fails + 1
  IO.println s!"{name}: {vecs.length - fails}/{vecs.length} vectors meet Tool.frontSpec ({counts})"
  pure (if fails = 0 then 0 else 1)

/-- The tools behind a clap front end, and whether only their help comes from it. -/
def fronts : List (String × Silmaril.Cli.Clap.Tool × Bool) :=
  [("wasm-asyncify", Silmaril.Cli.Spec.Asyncify.tool, false),
   ("wasm-jco", Silmaril.Cli.Spec.Jco.tool, false),
   ("wasm-wac", Silmaril.Cli.Spec.Wac.tool, false),
   ("wasm-opt", Silmaril.Cli.Spec.WasmOpt.tool, true)]

/-- The class of a clap outcome, for the report. -/
def clapClass : Silmaril.Cli.Clap.Outcome → String
  | .run _ _ => "run"
  | .undecided _ _ _ => "undecided"
  | .help _ => "help"
  | .version => "version"
  | .needCommand _ => "need-command"
  | .error _ => "usage-error"

def runFront (name : String) (cmd : String) (pre : List String) : IO UInt32 := do
  let some (t, helpOnly) := fronts.lookup name
    | IO.eprintln s!"cli-harness: unknown front end {name}"; return 2
  let mut fails := 0
  let mut checked := 0
  let mut counts : List (String × Nat) := []
  for v in t.surface.root.corpus do
    let c : Case := { name := " ".intercalate v, args := v }
    let cls := clapClass (t.outcome c.input)
    if helpOnly && cls != "help" then continue
    checked := checked + 1
    counts := match counts.lookup cls with
      | some n => (cls, n + 1) :: counts.filter (·.1 != cls)
      | none => (cls, 1) :: counts
    let s ← runBinary cmd pre c
    if !(t.frontCheck c.input s) then
      IO.println s!"FAIL: {name} [{cls}] {c.name}: {showSnap s}"
      fails := fails + 1
  IO.println s!"{name}: {checked - fails}/{checked} vectors meet Clap.Tool.frontSpec ({counts})"
  pure (if fails = 0 then 0 else 1)

def main : List String → IO UInt32
  | "surface" :: name :: "--" :: cmd :: pre => runSurface name cmd pre
  | "front" :: name :: "--" :: cmd :: pre => runFront name cmd pre
  | name :: "--" :: cmd :: pre => do
    match suite name with
    | some (chk, cases) =>
      let fails ← checkCases name chk cmd pre cases
      IO.println s!"{name}: {cases.length - fails}/{cases.length} cases passed"
      pure (if fails = 0 then 0 else 1)
    | none =>
      IO.eprintln s!"cli-harness: unknown suite {name}"
      pure 2
  | _ => do
    IO.eprintln "usage: cli-harness SUITE -- CMD [ARGS…]   (SUITE: echo, cat, copy, echon)"
    pure 2
