module
public import Silmaril.Compiler.Native.Lower.Defs
public import Silmaril.Compiler.Native.Emit.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Defs
public import Silmaril.Compiler.Native.Frontend.Defs
public import Silmaril.Compiler.C.Main.Defs
/-! The native ccomp driver. C parsing, typing and lowering remain in Lean;
GNU as assembles selected instructions and the system C driver links native
objects. It never delegates C compilation to another C compiler. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Driver
open Silmaril.Compile
open Silmaril.Compile.Driver
open Silmaril.Compile.C.Main (CM failWith env tool timed lift preprocess inputText textAil readBin)

/-- Delay construction of pure frontend/lowering work until after the clock
read. Passing an already constructed `CM` can evaluate that work before timing. -/
@[noinline] def timedStage {α : Type} (options : Options) (stage : String)
    (action : Unit → CM α) : CM α := do
  let started ← IO.monoNanosNow
  let result ← action ()
  if options.time then
    IO.eprintln s!"time {stage} {(Float.ofNat ((← IO.monoNanosNow) - started)) / 1e9}"
  return result

def compile (options : Options) (tag : String) (program : Silmaril.Cerberus.Ail.TypedProgram)
    (optimize : Bool := true)
    (enumBindings : List (Silmaril.Cerberus.Sym × Silmaril.Cerberus.IntegerType) := []) :
    Except String String := do
  let artifact ← Lower.compile tag program (enumBindings := enumBindings)
  let optimized := if optimize && options.opt != some .O0 then
      { artifact with mir := (Optimize.optimize #[artifact.mir])[0]! }
    else artifact
  Emit.emit #[optimized]

/-- Native C frontend: preserve the full actual desugaring state while retaining
the imported driver's asm filtering, typed program and diagnostics. -/
def frontend (_options : Options) (source : ByteArray) : Except Diag Frontend.Result := do
  match Frontend.run (← Silmaril.Compile.Driver.asmText source) with
  | .ok result => pure result
  | .error why => throw (.reject why)

def inputResult (options : Options) (tmp path : String) (index : Nat)
    (lang : Lang) (kind : InputKind) (stdin : ByteArray) : CM Frontend.Input := do
  if kind == .ail then
    return .ofTyped (← lift "" (decodeAil path (← IO.FS.readFile path)))
  let text ← timedStage options s!"preprocess {path}" fun _ => inputText options path lang kind stdin
  timedStage options s!"frontend {path}" fun _ => do
    if options.ailFromOracle then
      return .ofTyped (← textAil options tmp path index text)
    return (← lift s!"{path}: " (frontend options text)).input

/-- Compatibility projection for callers that only consume typed Ail. -/
def inputProgram (options : Options) (tmp path : String) (index : Nat)
    (lang : Lang) (kind : InputKind) (stdin : ByteArray) : CM Silmaril.Cerberus.Ail.TypedProgram := do
  return (← inputResult options tmp path index lang kind stdin).program

def assembly (options : Options) (tmp path : String) (index : Nat)
    (lang : Lang) (kind : InputKind) (stdin : ByteArray) : CM String := do
  let input ← inputResult options tmp path index lang kind stdin
  let optimize := (← env "CCOMP_MIR_OPT" "1") != "0"
  timedStage options "native lower/SSA/ABI" fun _ => do
    match compile options s!"u{index}" input.program optimize (enumBindings := input.enumBindings) with
    | .ok text => return text
    | .error error => failWith 1 s!"{path}: {error}"

def assemble (options : Options) (tmp : String) (index : Nat) (text output : String) : CM Unit := do
  let path := s!"{tmp}/native.{index}.s"
  IO.FS.writeFile path text
  let _ ← tool options "as" (#["--64", "-o", output, path] ++ options.asPass.toArray)

def linkFlags (options : Options) : Array String := Id.run do
  let mut args := #["-no-pie"]
  if options.static || options.noLibc then args := args.push "-static"
  if options.nostdlib || options.noLibc then args := args.push "-nostdlib"
  if options.nostartfiles then args := args.push "-nostartfiles"
  if options.nodefaultlibs then args := args.push "-nodefaultlibs"
  if options.pthread then args := args.push "-pthread"
  if options.rdynamic then args := args.push "-rdynamic"
  if options.strip then args := args.push "-s"
  for dir in options.libDirs do args := args.push ("-L" ++ dir)
  return args

/-- Ship native implementation headers with the executable. User include
directories retain priority; `-nostdinc` suppresses this standard search path. -/
def nativePreprocessOptions (options : Options) (tmp : String) : CM Options := do
  let options : Options := { options with preprocessor := some (options.preprocessor.getD .system) }
  if options.nostdinc then return options
  let directory := s!"{tmp}/native-include"
  IO.FS.createDirAll directory
  IO.FS.writeFile s!"{directory}/stdarg.h"
    (include_str "../../../../tools/ccomp-native/include/stdarg.h")
  return { options with dirs := options.dirs ++ [(.system, directory)] }

def run (options : Options) : CM Unit := do
  if options.target == some .rv64 then
    failWith 2 "the native System V route targets x86_64; RV64 remains in ccomp-legacy"
  if options.float == some .soft then
    failWith 2 "the native System V route currently uses SSE floating operations"
  let files := options.inputs.filterMap fun
    | .file path lang => some (path, lang, InputKind.ofFile path lang)
    | _ => none
  if files.isEmpty then failWith 1 "no input files"
  let stdin ← if files.any (fun f => f.1 == "-") then (← IO.getStdin).readBinToEnd else pure .empty
  if options.mode != .link && options.output.isSome && files.length > 1 then
    failWith 2 "cannot specify -o for multiple inputs without linking"
  let tmp := s!"{← env "TMPDIR" "/tmp"}/silmaril-ccomp.{← IO.monoNanosNow}"
  IO.FS.createDirAll tmp
  try
    let options ← nativePreprocessOptions options tmp
    let mut objects : Array String := #[]
    let mut index := 0
    for input in options.inputs do
      match input with
      | .lib name => objects := objects.push ("-l" ++ name)
      | .linker arg => objects := objects ++ #["-Xlinker", arg]
      | .linkerCommas args => objects := objects.push ("-Wl," ++ args)
      | .file path lang =>
        let kind := InputKind.ofFile path lang
        if kind == .linkInput then
          if options.mode == .link then objects := objects.push path
          else IO.eprintln s!"ccomp: warning: {path}: linker input unused"
        else if options.mode == .preprocess then
          let text ← preprocess options path lang kind stdin
          if let some out := options.output then IO.FS.writeBinFile out text
          else (← IO.getStdout).write text
        else
          if kind == .header || kind == .asm || kind == .asmCpp then
            failWith 2 s!"{path}: native C/Ail input required"
          if options.dryRun then
            IO.eprintln s!"ccomp: native Lean frontend/SSA/ABI, as: {path}"
          else
            let text ← assembly options tmp path index lang kind stdin
            if options.mode == .assemble then
              IO.FS.writeFile (options.output.getD (stem path ++ ".s")) text
            else
              let out := if options.mode == .compile then objectName options path
                else s!"{tmp}/input.{index}.o"
              assemble options tmp index text out
              objects := objects.push out
          index := index + 1
    if options.mode == .link && !options.dryRun then
      if options.noLibc && !options.nostartfiles then
        let source := include_str "../../../../tools/ccomp-native/runtime/crt0-x86_64.S"
        let startup := s!"{tmp}/crt0.o"
        assemble options tmp index source startup
        objects := #[startup] ++ objects
      let linker ← env "CCOMP_NATIVE_LINKER" "cc"
      let _ ← tool options linker (linkFlags options ++ #["-o", options.output.getD "a.out"] ++ objects)
      pure ()
  finally
    (try IO.FS.removeDirAll tmp catch _ => pure () : IO Unit)

def main (args : List String) : IO UInt32 := do
  let extra := responseTokens (← env "CCOMP_OPTIONS" "")
  let args ← expandResponseFiles Silmaril.Compile.C.Main.readResponseFile 64 (extra ++ args)
  match parseArgs args with
  | .error error => IO.eprintln error.render; return error.code
  | .ok options =>
    -- -S is implemented by this route. Retain the remaining original flag checks.
    let checks := ({ options with stopS := false } : Options).checks
    for diagnostic in checks do IO.eprintln diagnostic.render
    if let some error := checks.find? (·.severity == .error) then return error.code
    if !options.queries.isEmpty then
      for query in options.queries do Silmaril.Compile.C.Main.answer options query
      return 0
    match ← (run options).run with
    | .ok () => return 0
    | .error error => IO.eprintln error.render; return error.code

end Silmaril.Compiler.Native.Driver
