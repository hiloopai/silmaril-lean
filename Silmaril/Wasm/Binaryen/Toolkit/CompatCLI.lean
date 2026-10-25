module

@[expose] public section

/-! # Explicit, partial compatibility with Binaryen version_133's CLI

The shared parser accepts output options in any position and never discards an
unknown option. This is command-line compatibility, not additional feature or
semantic coverage. All file writes happen after successful pure processing.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

structure CompatFileArgs where
  inputs : List String
  output : Option String

def parseCompatFilesAux : List String → List String → Option String →
    Except String CompatFileArgs
  | [], inputs, output => .ok ⟨inputs.reverse, output⟩
  | "--" :: rest, inputs, output => .ok ⟨inputs.reverse ++ rest, output⟩
  | flag :: rest, inputs, output => do
      if flag == "-o" || flag == "--output" then
        if output.isSome then throw "output option supplied more than once"
        match rest with
        | [] => throw (flag ++ " requires a file name")
        | path :: rest =>
          if path.isEmpty then throw "output file name must not be empty"
          parseCompatFilesAux rest inputs (some path)
      else if flag.startsWith "--output=" then
        if output.isSome then throw "output option supplied more than once"
        let path := (flag.drop 9).toString
        if path.isEmpty then throw "output file name must not be empty"
        parseCompatFilesAux rest inputs (some path)
      else if flag == "--all-features" || flag == "-all" then
        -- The tools already enable every implemented syntax feature. These
        -- request that supported set; unsupported inputs still reject.
        parseCompatFilesAux rest inputs output
      else if flag.startsWith "-" && flag != "-" then
        throw ("unsupported option: " ++ flag)
      else
        parseCompatFilesAux rest (flag :: inputs) output

def parseCompatFiles (args : List String) : Except String CompatFileArgs :=
  parseCompatFilesAux args [] none

def compatHelp (args : List String) : Bool := args == ["--help"] || args == ["-h"]

def compatVersion (args : List String) : Bool := args == ["--version"]

def compatVersionText : String :=
  "Silmaril scoped Binaryen CLI compatibility (shape baseline: Binaryen version_133)"

def compatReadText (path : String) : IO String :=
  if path == "-" then do (← IO.getStdin).readToEnd else IO.FS.readFile path

def compatReadBytes (path : String) : IO ByteArray :=
  if path == "-" then do (← IO.getStdin).readBinToEnd else IO.FS.readBinFile path

def compatWriteText (path : String) (text : String) : IO Unit :=
  if path == "-" then IO.print text else IO.FS.writeFile path text

def compatWriteBytes (path : String) (bytes : ByteArray) : IO Unit :=
  if path == "-" then do (← IO.getStdout).write bytes else IO.FS.writeBinFile path bytes

def compatUsageError (usage message : String) : IO UInt32 := do
  IO.eprintln (message ++ "\n" ++ usage)
  return 2

end Silmaril.Wasm.Binaryen.Toolkit
