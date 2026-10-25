module

public import Silmaril.Wasm.Binaryen.Toolkit.PolicyMerge
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSource
public import Silmaril.Wasm.Binaryen.Toolkit.Disassemble
public import Silmaril.Wasm.Binaryen.Toolkit.CompatCLI

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def compatMergeUsage : String :=
  "usage: wasm-merge IN1 NAME1 [IN2 NAME2 ...] [-o OUT.wasm] [-S | --emit-text]\n" ++
  "  Binaryen order is FILE NAME; the legacy -lean executable uses NAME FILE.\n" ++
  "  Output options may occur anywhere; --output=FILE and -- are supported.\n" ++
  "  Without output, check/merge without writing. '-' uses standard IO.\n" ++
  "  Magic-detected binary or certified WAT input; -S emits checked WAT.\n" ++
  "  Checked in-order acyclic GC subset with automatic finite silent-start preparation.\n" ++
  "  All implemented features enabled (-all/--all-features); no resource sections or cycles.\n" ++
  "  Checked export rename/skip on closed function-only sources; aliases retain namespace-qualified queries.\n" ++
  "  Unsupported source-map, manifest, debug and feature-disable flags reject."

def compatMergeExtraOptions : List String → Bool → Option MergeExportNames.Policy → List String →
    Except String (Bool × MergeExportNames.Policy × List String)
  | [], text, policy, rest => .ok (text, policy.getD .reject, rest.reverse)
  | "--" :: rest, text, policy, parsed => .ok (text, policy.getD .reject, parsed.reverse ++ "--" :: rest)
  | flag :: rest, text, policy, parsed => do
      if flag == "-S" || flag == "--emit-text" then
        if text then throw "text-output option supplied more than once"
        compatMergeExtraOptions rest true policy parsed
      else if flag == "--rename-export-conflicts" || flag == "--skip-export-conflicts" then
        if policy.isSome then throw "export-conflict policy supplied more than once"
        compatMergeExtraOptions rest text
          (some (if flag == "--rename-export-conflicts" then .rename else .skip)) parsed
      else compatMergeExtraOptions rest text policy (flag :: parsed)

def parseCompatMergeInputs : List String → Except String (List (String × String))
  | [] => .ok []
  | path :: name :: rest => ((name, path) :: ·) <$> parseCompatMergeInputs rest
  | _ => .error "each input file must be followed by its module name"

def runCompatMerge (args : List String) : IO UInt32 := do
  if compatHelp args then IO.println compatMergeUsage; return 0
  if compatVersion args then IO.println compatVersionText; return 0
  let (textOutput, policy, remaining) ← match compatMergeExtraOptions args false none [] with
    | .error e => return ← compatUsageError compatMergeUsage e
    | .ok options => pure options
  let opts ← match parseCompatFiles remaining with
    | .error e => return ← compatUsageError compatMergeUsage e
    | .ok opts => pure opts
  let inputs ← match parseCompatMergeInputs opts.inputs with
    | .error e => return ← compatUsageError compatMergeUsage e
    | .ok [] => return ← compatUsageError compatMergeUsage "expected at least one input file/name pair"
    | .ok inputs => pure inputs
  try
    let inputs ← inputs.mapM fun (name, path) => do
      let bytes ← compatReadBytes path
      pure (name, bytes)
    let sources ← match prepareMergeSources inputs with
      | .error e => IO.eprintln ("wasm-merge: " ++ e); return 1
      | .ok sources => pure sources
    match mergePolicyBytes policy (sources.map fun (ns, source) => (ns, source.bytes)) with
    | .error e => IO.eprintln ("wasm-merge: " ++ e); return 1
    | .ok artifact =>
      if textOutput then
        match disassembleBytes artifact.bytes with
        | .error e => IO.eprintln ("wasm-merge: " ++ e); return 1
        | .ok text =>
            if let some output := opts.output then compatWriteText output text.text
      else if let some output := opts.output then compatWriteBytes output artifact.bytes
      return 0
  catch e => IO.eprintln (toString e); return 1

end Silmaril.Wasm.Binaryen.Toolkit
