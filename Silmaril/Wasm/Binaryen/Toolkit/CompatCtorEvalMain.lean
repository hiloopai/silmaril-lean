module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalFallback
public import Silmaril.Wasm.Binaryen.Toolkit.CompatCLI

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def compatCtorEvalUsage : String :=
  "usage: wasm-ctor-eval IN.wasm [-o OUT.wasm | --output OUT.wasm]\n" ++
  "  Output options may occur anywhere; --output=FILE and -- are supported.\n" ++
  "  Without output, check/evaluate without writing. '-' uses standard IO.\n" ++
  "  Evaluates a bounded closed i32/i64 scalar-global start-assignment wrapper.\n" ++
  "  Other decoded valid modules keep their original bytes; skipped/transformed is reported.\n" ++
  "  Retains functions/exports, serializes initialized state and removes start.\n" ++
  "  Arbitrary constructor effects are not evaluated; unmatched valid modules stay unchanged.\n" ++
  "  --ctors, --kept-exports and unsupported text/debug/feature flags reject."

def runCompatCtorEval (args : List String) : IO UInt32 := do
  if compatHelp args then IO.println compatCtorEvalUsage; return 0
  if compatVersion args then IO.println compatVersionText; return 0
  let opts ← match parseCompatFiles args with
    | .error e => return ← compatUsageError compatCtorEvalUsage e
    | .ok opts => pure opts
  let input ← match opts.inputs with
    | [input] => pure input
    | _ => return ← compatUsageError compatCtorEvalUsage "expected one input file"
  try
    let bytes ← compatReadBytes input
    match CtorEval.evaluateBytesOrKeep bytes with
    | .error e => IO.eprintln ("wasm-ctor-eval: " ++ e); return 1
    | .ok artifact =>
      IO.eprintln artifact.report
      if let some output := opts.output then compatWriteBytes output artifact.bytes
      return 0
  catch e => IO.eprintln (toString e); return 1

end Silmaril.Wasm.Binaryen.Toolkit
