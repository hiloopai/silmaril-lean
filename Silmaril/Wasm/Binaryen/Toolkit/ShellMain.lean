module

public import Silmaril.Wasm.Binaryen.Toolkit.Shell
public import Silmaril.Wasm.Binaryen.Toolkit.CLIUsage

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- This bounded interpreter is separate from Binaryen's WAST/script shell. -/
def shellUsage : String :=
  "usage: wasm-shell-lean FUEL MODULE.wasm EXPORT [I32_ARGUMENT ...]\n" ++
  "  no imports; explicit step budget per initialization/invocation\n" ++
  "  fixed deterministic numerical policy; growth uses SingleThreaded.neverFail\n" ++
  "  fuel exhaustion is inconclusive; arguments wrap modulo 2^32"

structure ShellArgs where
  budget : Nat
  inputPath : String
  exportName : String
  args : List Execution.Core.Val

def parseShellArgs : List String → Except String ShellArgs
  | "shell" :: fuel :: input :: name :: args => do
      let budget ← match fuel.toNat? with
        | some n => .ok n
        | none => .error "shell: FUEL must be a natural number"
      let values ← args.mapM fun arg => do
        let value ← match arg.toInt? with
          | some n => .ok n
          | none => .error ("shell: invalid i32 integer: " ++ arg)
        pure (Execution.Core.Val.i32 (BitVec.ofInt 32 value))
      pure ⟨budget, input, name, values⟩
  | _ => .error usage

def shellFailureMessage : ShellFailure → String
  | .rejected reason => "shell: " ++ reason
  | .fuelExhausted phase =>
      "shell: fuel exhausted during " ++ reprStr phase ++ "; result is inconclusive"
  | .initializationResult result => "shell: initialization ended with " ++ reprStr result
  | .unclassified phase => "shell: unclassified stopped state during " ++ reprStr phase

def shellValueMessage : Execution.Core.Val → String
  | .num ⟨.int .i32, bits⟩ => "i32:" ++ toString bits.toNat
  | .num ⟨.int .i64, bits⟩ => "i64:" ++ toString bits.toNat
  | value => reprStr value

def shellResultMessage : Execution.Core.Result → String
  | .values values => "return [" ++ String.intercalate ", " (values.map shellValueMessage) ++ "]"
  | .trap => "trap"
  | .throw address => "throw " ++ toString address

/-- Shared file IO and rendering for the legacy and standalone argument parsers. -/
def runParsedShell (parsed : Except String ShellArgs) : IO UInt32 := do
  let opts ← match parsed with
    | .ok opts => pure opts
    | .error e => do IO.eprintln e; return 2
  try
    let bytes ← IO.FS.readBinFile opts.inputPath
    match shellBytes SingleThreaded.neverFail opts.budget opts.exportName opts.args bytes with
    | .error e =>
        IO.eprintln (shellFailureMessage e)
        return match e with
          | .fuelExhausted _ => 3
          | .initializationResult _ => 4
          | _ => 1
    | .ok artifact =>
        IO.println (shellResultMessage artifact.result)
        return match artifact.result with
          | .values _ => 0
          | _ => 4
  catch e =>
    IO.eprintln (toString e)
    return 1

def runShell (args : List String) : IO UInt32 :=
  runParsedShell (parseShellArgs args)

/-- Standalone arguments share the original parser, including its integer
conversion and modulo-2^32 i32 values. -/
def parseStandaloneShellArgs : List String → Except String ShellArgs
  | fuel :: input :: name :: args => parseShellArgs ("shell" :: fuel :: input :: name :: args)
  | _ => .error shellUsage

/-- Standalone entry point for the exact same checked runner and output policy
as `binaryen-tools-lean shell`. The legacy command/API remain available. -/
def runStandaloneShell (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println shellUsage
    return 0
  runParsedShell (parseStandaloneShellArgs args)

end Silmaril.Wasm.Binaryen.Toolkit
