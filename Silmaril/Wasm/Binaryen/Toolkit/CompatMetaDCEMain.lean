module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEFallback
public import Silmaril.Wasm.Binaryen.Toolkit.CompatCLI

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def compatMetaDCEUsage : String :=
  "usage: wasm-metadce IN.wasm --graph-file GRAPH.json [-o OUT.wasm]\n" ++
  "  Input, graph and output options may occur in any order.\n" ++
  "  --graph-file=FILE, --output=FILE, -h and -- are supported.\n" ++
  "  Without output, check/eliminate without writing. '-' uses standard IO.\n" ++
  "  Closed numeric-signature function-only base-profile optimization subset.\n" ++
  "  Other decoded valid modules keep original bytes; skipped/applied is reported.\n" ++
  "  External graph nodes support name/reaches/root/export; graph imports reject.\n" ++
  "  Exact observations concern only graph-reachable exported entry points."

/-- Remove only the explicit graph option, leaving file/output parsing shared
with the other compatibility tools. A separator protects literal path names. -/
def parseCompatGraphAux : List String → Option String → List String →
    Except String (String × List String)
  | [], some graph, rest => .ok (graph, rest.reverse)
  | [], none, _ => .error "--graph-file is required"
  | "--" :: paths, some graph, rest => .ok (graph, rest.reverse ++ "--" :: paths)
  | "--" :: _, none, _ => .error "--graph-file is required before --"
  | "--graph-file" :: [], _, _ => .error "--graph-file requires a file name"
  | "--graph-file" :: path :: flags, graph, rest =>
      if graph.isSome then .error "--graph-file supplied more than once"
      else if path.isEmpty then .error "graph file name must not be empty"
      else parseCompatGraphAux flags (some path) rest
  | flag :: flags, graph, rest =>
      if flag.startsWith "--graph-file=" then
        if graph.isSome then .error "--graph-file supplied more than once"
        else
          let path := (flag.drop 13).toString
          if path.isEmpty then .error "graph file name must not be empty"
          else parseCompatGraphAux flags (some path) rest
      else parseCompatGraphAux flags graph (flag :: rest)

def runCompatMetaDCE (args : List String) : IO UInt32 := do
  if compatHelp args then IO.println compatMetaDCEUsage; return 0
  if compatVersion args then IO.println compatVersionText; return 0
  let (graph, files) ← match parseCompatGraphAux args none [] with
    | .error e => return ← compatUsageError compatMetaDCEUsage e
    | .ok parts => pure parts
  let opts ← match parseCompatFiles files with
    | .error e => return ← compatUsageError compatMetaDCEUsage e
    | .ok opts => pure opts
  let input ← match opts.inputs with
    | [input] => pure input
    | _ => return ← compatUsageError compatMetaDCEUsage "expected one input file"
  if input == "-" && graph == "-" then
    return ← compatUsageError compatMetaDCEUsage "input and graph cannot both use stdin"
  try
    let inputBytes ← compatReadBytes input
    let graphText ← compatReadText graph
    match MetaDCE.eliminateBytesOrKeep graphText inputBytes with
    | .error e => IO.eprintln ("wasm-metadce: " ++ e); return 1
    | .ok artifact =>
      IO.eprintln artifact.report
      if let some output := opts.output then compatWriteBytes output artifact.bytes
      return 0
  catch e => IO.eprintln (toString e); return 1

end Silmaril.Wasm.Binaryen.Toolkit
