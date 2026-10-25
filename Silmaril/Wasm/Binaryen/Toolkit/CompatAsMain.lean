module

public import Silmaril.Wasm.Binaryen.Toolkit.AsBinaryen
public import Silmaril.Wasm.Binaryen.Toolkit.CompatCLI

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def compatAsUsage : String :=
  "usage: wasm-as IN.wat [-o OUT.wasm | --output OUT.wasm]\n" ++
  "  Output defaults to IN with a trailing .wat replaced by .wasm. '-' uses standard IO.\n" ++
  "  Supports --output=FILE, --, --all-features/-all, -h/--help and --version.\n" ++
  "  Checked Core WAT and documented Binaryen source macros; validation is always enabled.\n" ++
  "  All implemented features are enabled; unsupported syntax and feature-disable/debug flags reject."

def runCompatAs (args : List String) : IO UInt32 := do
  if compatHelp args then IO.println compatAsUsage; return 0
  if compatVersion args then IO.println compatVersionText; return 0
  let opts ← match parseCompatFiles args with
    | .error e => return ← compatUsageError compatAsUsage e
    | .ok opts => pure opts
  let input ← match opts.inputs with
    | [input] => pure input
    | _ => return ← compatUsageError compatAsUsage "expected one input file"
  let defaultOutput :=
    (if input.endsWith ".wat" then (input.dropEnd 4).toString else input) ++ ".wasm"
  try
    let text ← compatReadText input
    match assembleBinaryenText text with
    | .error e => IO.eprintln ("wasm-as: " ++ e); return 1
    | .ok artifact =>
      compatWriteBytes (opts.output.getD defaultOutput) artifact.bytes
      return 0
  catch e => IO.eprintln (toString e); return 1

end Silmaril.Wasm.Binaryen.Toolkit
