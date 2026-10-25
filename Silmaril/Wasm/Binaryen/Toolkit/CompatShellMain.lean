module

public import Silmaril.Wasm.Binaryen.Toolkit.ShellMain
public import Silmaril.Wasm.Binaryen.Toolkit.CompatCLI

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def compatShellUsage : String :=
  "usage: wasm-shell --fuel N --invoke EXPORT IN.wasm [I32_ARGUMENT ...]\n" ++
  "  This is an explicit Silmaril binary-invocation extension, not a WAST shell.\n" ++
  "  Binaryen's positional SCRIPT.wast and stdin script interfaces are unsupported.\n" ++
  "  --fuel and --invoke are required; their order is flexible. No imports.\n" ++
  "  Fixed deterministic neverFail policy; per-phase fuel; exhaustion is inconclusive.\n" ++
  "  Arguments wrap modulo 2^32. Exit 3 is fuel exhaustion; exit 4 is trap/exception."

def parseCompatShellAux : List String → Option String → Option String →
    List String → Except String ShellArgs
  | [], fuel, name, inputs =>
    match fuel, name, inputs.reverse with
    | some fuel, some name, input :: values => parseStandaloneShellArgs (fuel :: input :: name :: values)
    | _, _, _ => .error "--fuel N, --invoke EXPORT and one binary input are required; WAST is unsupported"
  | "--fuel" :: value :: rest, fuel, name, inputs =>
    if fuel.isSome then .error "--fuel supplied more than once"
    else parseCompatShellAux rest (some value) name inputs
  | "--invoke" :: value :: rest, fuel, name, inputs =>
    if name.isSome then .error "--invoke supplied more than once"
    else parseCompatShellAux rest fuel (some value) inputs
  | arg :: rest, fuel, name, inputs =>
    if arg.startsWith "-" && !arg.toInt?.isSome then
      .error ("unsupported option: " ++ arg)
    else parseCompatShellAux rest fuel name (arg :: inputs)

def runCompatShell (args : List String) : IO UInt32 := do
  if compatHelp args then IO.println compatShellUsage; return 0
  if compatVersion args then IO.println compatVersionText; return 0
  match parseCompatShellAux args none none [] with
  | .error e => compatUsageError compatShellUsage e
  | .ok opts => runParsedShell (.ok opts)

end Silmaril.Wasm.Binaryen.Toolkit
