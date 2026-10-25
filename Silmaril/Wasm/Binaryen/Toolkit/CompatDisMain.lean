module

public import Silmaril.Wasm.Binaryen.Toolkit.DisassembleLegacy
public import Silmaril.Wasm.Binaryen.Toolkit.CompatCLI

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def compatDisUsage : String :=
  "usage: wasm-dis IN.wasm [-o OUT.wat | --output OUT.wat]\n" ++
  "  Text goes to stdout if output is omitted. '-' uses standard IO.\n" ++
  "  Supports --output=FILE, --, -h/--help and --version. Options may precede input.\n" ++
  "  Certified Core/compact/shared/atomic WAT; Binaryen memory proposals and legacy EH.\n" ++
  "  Disassembly does not validate modules. Unsupported proposal syntax rejects.\n" ++
  "  Source maps and feature flags reject; no ignored options."

def runCompatDis (args : List String) : IO UInt32 := do
  if compatHelp args then IO.println compatDisUsage; return 0
  if compatVersion args then IO.println compatVersionText; return 0
  let opts ← match parseCompatFiles args with
    | .error e => return ← compatUsageError compatDisUsage e
    | .ok opts => pure opts
  let input ← match opts.inputs with
    | [input] => pure input
    | _ => return ← compatUsageError compatDisUsage "expected one input file"
  try
    let bytes ← compatReadBytes input
    match disassembleToolkitBytes bytes with
    | .error e => IO.eprintln ("wasm-dis: " ++ e); return 1
    | .ok artifact =>
      compatWriteText (opts.output.getD "-") artifact.text
      return 0
  catch e => IO.eprintln (toString e); return 1

end Silmaril.Wasm.Binaryen.Toolkit
