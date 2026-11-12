import Silmaril.Wasm.FX.Asyncify.Tool.Run.Defs
import Silmaril.Wasm.FX.Asyncify.Tool.Spill.Defs
import Silmaril.Wasm.FX.Asyncify.Tool.Examples.Defs
import Silmaril.Wasm.FX.Asyncify.Tool.Selective.Defs
import Silmaril.Cli.Spec.Asyncify.Defs

/-!
# `wasm-asyncify`

Command-line front end of `Silmaril.Wasm.FX.Asyncify.Tool`: it reads files, calls one pure
function of the core and writes the result. See `docs/projects/wasm-binaryen-tooling.md`.

```
wasm-asyncify asyncify IN.wasm -o OUT.wasm [--pages N] [--no-elide] [--selective]
                                                          the verified pass on a binary: statement
                                                          form, else operands spilled to locals;
                                                          re-entry checks elided (--no-elide: the
                                                          guarded pass, statement form only;
                                                          --selective: only calls that may
                                                          suspend are instrumented, statement
                                                          form only, checks not elided)
wasm-asyncify run-src IN.wasm EXPORT ARGS [--fuel N]     the source model, test host
wasm-asyncify run-tgt OUT.wasm EXPORT ARGS [--fuel N]    the target model, test host
wasm-asyncify example NAME -o OUT.wasm                   a built-in example module
wasm-asyncify examples                                   list the examples
```

`ARGS` is a comma-separated list of unsigned 32-bit numbers (possibly empty: `""`).

The command line is read by the grammar `Silmaril.Cli.Spec.Asyncify.tool` through
`Silmaril.Cli.Clap.Tool.main`: `-h` prints the derived help of a command, a usage error prints
`error: …` and the derived usage line and exits 2, and the program refines
`Asyncify.tool.spec` (`Silmaril.Cli.Clap.Tool.main_refines`; docs/projects/wasm-binaryen-tooling.md). Exit status:
0 on success, 1 when the command fails, 2 on a usage error.
-/

open Silmaril.Wasm.FX.Asyncify.Tool

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"wasm-asyncify: {msg}"
  pure 1

def parseArgs (s : String) : Option (List W) :=
  if s.isEmpty then some [] else
    (s.splitOn ",").mapM fun x => x.trimAscii.toString.toNat?.map (BitVec.ofNat 32)

def decodeFile (path : String) : IO (Option Silmaril.Wasm.Module) := do
  let b ← IO.FS.readBinFile path
  pure (Silmaril.Wasm.Binary.Core.decode? b)

def runCmd (tgt : Bool) (path name argStr : String) (fuel : Nat) : IO UInt32 := do
  let some m ← decodeFile path | fail s!"{path} does not decode as a Core module"
  let some as := parseArgs argStr | fail s!"bad arguments {argStr}"
  match (if tgt then runTgt else runSrc) m name as fuel with
  | .ok o => IO.println (showObs o); pure 0
  | .error e => fail e

/-- The commands, on the matches of `Silmaril.Cli.Spec.Asyncify.tool` (required options,
positionals and defaults are filled in by the reading). -/
def run (m : Silmaril.Cli.Matches) : IO UInt32 := do
  let str (k : String) : String := (m.str? k).getD ""
  match m.path with
  | ["asyncify"] =>
    let b ← IO.FS.readBinFile (str "in")
    let pass : ByteArray → Nat → Except String ByteArray :=
      if m.flag "selective" then fun b p => asyncifyBytesSelective b p
      else if m.flag "no-elide" then (asyncifyBytes · ·) else (asyncifyBytesW · ·)
    match pass b ((m.nat? "pages").getD 1) with
    | .ok bs => IO.FS.writeBinFile (str "-o") bs; pure 0
    | .error e => fail e
  | ["run-src"] => runCmd false (str "in") (str "export") (str "args") ((m.nat? "fuel").getD 1000000)
  | ["run-tgt"] => runCmd true (str "in") (str "export") (str "args") ((m.nat? "fuel").getD 1000000)
  | ["example"] =>
    let name := str "name"
    let some mod := Examples.all.lookup name | fail s!"no example {name}"
    match Silmaril.Wasm.Binaryen.Exe.encodeModule? mod with
    | .ok bs => IO.FS.writeBinFile (str "-o") ⟨bs.toArray⟩; pure 0
    | .error e => fail s!"encoding failed: {e}"
  | ["examples"] => Examples.all.forM (fun (n, _) => IO.println n); pure 0
  | p => fail s!"no command {p}"

def main : List String → IO UInt32 := Silmaril.Cli.Spec.Asyncify.tool.main run
