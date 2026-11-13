module

public import Silmaril.Compiler.Driver.Core.Defs
public import Silmaril.Compiler.Driver.Preprocess.Defs
/-! # `ccomp`: the C compiler driver

`ccomp` is invoked like `cc` (`CC=ccomp make`, Rust's `cc` crate, configure probes):

```
ccomp [-c | -E | -M…] [-o OUT] [-I DIR] [-D NAME[=VALUE]] [-U NAME] [-include FILE]
      [-std=…] [-O…] [-g…] [-W…] [-f…] [-m…] [-x LANG] [-L DIR] [-l LIB] [-Wl,…]
      [--preprocessor=cerberus|system|none|lean] [--float=soft|native] [--ail-from-oracle]
      [@FILE] FILE…
```

This module is the IO shell; the meaning of the options is `Silmaril.Compile.Driver.Options`
(the parser, the printer and their round trip, the classification of each option, gcc's manual
cited), the preprocessors are `Silmaril.Compile.Driver.Preprocess`, and the compiler itself is
the pure `Silmaril.Compile.C.compileTU` and `linkObjects` (`Silmaril.Compile.Driver.Core`).
`docs/CCompilerDriver.md` describes the whole command line; `docs/projects/cerberus.md` the compiler.

Inputs, by `-x` or suffix: `.c` (preprocessed first), `.i` (preprocessed C), `.ail`/`.sexp` (a
typed-Ail document, `cerb-oracle --level tail`), `.o` (a ccomp object), `.a` (an archive of ccomp
objects, made by `ar`). Without `-c` or `-E` the inputs are compiled and linked, with the runtime,
into the executable OUT (default `a.out`). Diagnostics go to stderr as `ccomp: error: …`; the
exit status is 0 on success, 1 when a program is rejected or not supported, 2 on usage or I/O
errors, 3 when an external tool fails.

Environment: `CCOMP_OPTIONS` (arguments read before the command line, e.g.
`--ail-from-oracle` for tools that take a bare compiler name), `CERB_RUNTIME` (Cerberus's
headers), `CERB_ORACLE`, `CCOMP_AIL_CACHE` (typed Ail cached by the SHA-256 of the `.i`),
`CCOMP_CPP` (the `cc` used as preprocessor), `TMPDIR`.

## Stages

1. **Preprocessing** (external, trusted for now): `--preprocessor=`, default `cerberus` (the
   system `cc -E` with Cerberus's flags and headers), see `Preprocess`.
2. **Frontend**: all in Lean by default (`Driver.frontend`): `Registry.Stage.asm` (an `asm`
   with an empty template becomes the expression of its operands, one that cannot be dropped
   is rejected), then `Registry.Stage.frontend`: the parser `Silmaril.Cerberus.Frontend.parse`
   (Cabs), `Frontend.desugar` and `Frontend.typecheck` (typed Ail), ported from Cerberus by
   the Cerberus port and checked byte-exact against it. A frontend reject is a compile
   error, never silently sent to Cerberus. `--ail-from-oracle` takes the typed Ail from
   Cerberus instead (after the same `asm` stage, since Cerberus drops `asm` statements too).
3. **Middle**, **link**, **backend**: `Registry.Stage.lower` (`compileReachableUnits`),
   `Registry.Stage.mirOpt` (the proved Mir passes; `CCOMP_MIR_OPT=0` skips them),
   `Registry.Stage.link` (`Mir.link` with its proved checker), `Registry.backend`
   (checked register renumbering, spilling, code generation and the ELF object).
   `--float=soft` (the default until `Registry.Stage.x86Native` is validated, ideas 576-578)
   lowers floating point to calls of the runtime's soft-float routines, so the program has
   no Lir float instruction and goes through the proved Lir → x86 chain; `--float=native`
   lowers it to Lir float instructions, which select the unvalidated native-float stage
   `Registry.Stage.x86Native` (scalar SSE2).
   The driver calls compiler code only through the stage registry
   (`Silmaril/Compile/Registry.lean`; the evaluator checks it).
4. **System link** (external, trusted): `as` assembles `RUNTIME/crt0-x86_64.S`, `ld` links it
   with the program object into a static executable.

`RUNTIME` is `tools/ccomp/runtime` of the checkout the executable was built in (`--runtime DIR`
overrides it).
-/

@[expose] public section

namespace Silmaril.Compile.C.Main

open Silmaril.Cerberus Ail.Codec
open Silmaril.Compile
open Silmaril.Compile.Driver

/-- The driver's options (`Silmaril.Compile.Driver.Options`) under the driver's name; the
evaluator reads the default float mode as `({} : Main.Options).nativeFloat` (false). -/
abbrev Options := Driver.Options

abbrev CM := ExceptT Diag IO

def failWith {α : Type} (code : UInt32) (msg : String) : CM α := throw { message := msg, code }

def env (name dflt : String) : IO String := do return (← IO.getEnv name).getD dflt

/-- Quote an argument for `-v` and `-###` output. -/
def shellQuote (a : String) : String :=
  if !a.isEmpty && a.all (fun (c : Char) => c.isAlphanum || "-_./=+,:@%".contains c) then a
  else "'" ++ a.replace "'" "'\\''" ++ "'"

def showCommand (cmd : String) (args : List String) : String :=
  " " ++ " ".intercalate ((cmd :: args).map shellQuote)

/-- Run an external tool (as, ld, sha256sum); its stdout. With `-v` the command is printed. -/
def tool (o : Options) (cmd : String) (args : Array String) : CM String := do
  if o.verbose then IO.eprintln (showCommand cmd args.toList)
  let r ← (IO.Process.output { cmd, args } : IO _)
  if r.exitCode != 0 then failWith 3 s!"{cmd} failed ({r.exitCode}): {r.stderr.take 2000}"
  return r.stdout

def timed {α : Type} (o : Options) (stage : String) (x : CM α) : CM α := do
  let t0 ← IO.monoNanosNow
  let r ← x
  if o.time then
    IO.eprintln s!"time {stage} {(Float.ofNat ((← IO.monoNanosNow) - t0)) / 1e9}"
  return r

def lift {α : Type} (pre : String) (r : Except Diag α) : CM α :=
  match r with
  | .ok a => pure a
  | .error d => throw { d with message := pre ++ d.message }

def readBin (path : String) : CM ByteArray := do
  try IO.FS.readBinFile path
  catch _ => failWith 2 s!"{path}: No such file or directory"

def runtimeDir (o : Options) : IO String := do
  match o.runtime with
  | some d => return d
  | none =>
    -- RUNTIME is tools/ccomp/runtime of the checkout: the executable is .lake/build/bin/ccomp
    let app ← IO.appPath
    let root := (((app.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD "."
    return (root / "tools" / "ccomp" / "runtime").toString

def preprocessEnv : IO PreprocessEnv := do
  let d : PreprocessEnv := {}
  return { cc := ← env "CCOMP_CPP" d.cc, cerbRuntime := ← env "CERB_RUNTIME" d.cerbRuntime }

/-! ## Stages -/

/-- Stage 1: preprocess one input with the preprocessor its options and kind select. -/
def preprocess (o : Options) (path : String) (lang : Lang) (kind : InputKind)
    (stdin : ByteArray) : CM ByteArray := do
  let pp := Preprocessor.ofKind (o.preprocessorFor kind)
  let penv ← preprocessEnv
  let req : PreprocessRequest := { options := o, path, lang, stdin }
  if o.verbose || o.dryRun then
    if let some (cmd, args) := pp.command penv req then IO.eprintln (showCommand cmd args)
  if o.dryRun then return .empty
  ExceptT.mk (pp.run penv req)

/-- Cerberus's typed Ail of a preprocessed file (`--ail-from-oracle`), cached. -/
def oracleAil (o : Options) (tmp : String) (name : String) (text : ByteArray) : CM String := do
  let iPath := s!"{tmp}/{name}.i"
  IO.FS.writeBinFile iPath text
  let cache ← env "CCOMP_AIL_CACHE" ""
  let key ← if cache.isEmpty then pure "" else do
    pure ((← tool o "sha256sum" #[iPath]).splitOn " ").head!
  let cached := s!"{cache}/{key}.tail.sexp"
  if !cache.isEmpty && (← System.FilePath.pathExists cached) then return ← IO.FS.readFile cached
  let oracle ← env "CERB_ORACLE" "cerb-oracle"
  let out := s!"{tmp}/{name}.tail.sexp"
  if o.verbose then IO.eprintln (showCommand oracle ["--level", "tail", "--output", out, iPath])
  let r ← (IO.Process.output { cmd := oracle, args := #["--level", "tail", "--output", out, iPath] } : IO _)
  if r.exitCode != 0 && r.exitCode != 1 then failWith 3 s!"cerb-oracle failed on {name}: {r.stderr.take 2000}"
  let doc ← IO.FS.readFile out
  if !cache.isEmpty then
    IO.FS.createDirAll cache
    let part := s!"{cached}.{← IO.monoNanosNow}"
    IO.FS.writeFile part doc
    (try IO.FS.rename part cached catch _ => pure () : IO Unit)
  return doc

/-- The text of one C or preprocessed input. -/
def inputText (o : Options) (path : String) (lang : Lang) (kind : InputKind) (stdin : ByteArray) :
    CM ByteArray :=
  if kind == .preprocessed && path != "-" then readBin path
  else preprocess o path lang kind stdin

/-- A unique name for the temporary files of an input. -/
def tmpName (path : String) (i : Nat) : String :=
  if path == "-" then s!"stdin{i}" else s!"{stem path}{i}"

/-- Cerberus's typed-Ail document of one C or preprocessed input (`--ail-from-oracle`), after
the `asm` stage. -/
def oracleDoc (o : Options) (tmp path : String) (i : Nat) (text : ByteArray) : CM String := do
  oracleAil o tmp (tmpName path i) (← lift s!"{path}: " (asmText text))

/-- The typed Ail of one C or preprocessed input (frontend). -/
def textAil (o : Options) (tmp path : String) (i : Nat) (text : ByteArray) : CM Ail.TypedProgram := do
  if o.ailFromOracle then return ← lift "" (decodeAil path (← oracleDoc o tmp path i text))
  lift s!"{path}: " (Driver.frontend o text)

/-- Look for `libNAME.a` in the `-L` directories and the runtime directory. -/
def findLib (o : Options) (rt name : String) : IO (Option String) := do
  for d in o.libDirs ++ [rt] do
    let p := s!"{d}/lib{name}.a"
    if ← System.FilePath.pathExists p then return some p
  return none

def foreignObject (what : String) : String :=
  s!"{what}: not a ccomp object: ccomp links only objects it compiled (its code uses a " ++
    "linear-memory ABI; see docs/CCompilerDriver.md)"

/-- The typed-Ail units of a link input (an object or an archive). -/
def linkInputUnits (path : String) (b : ByteArray) : CM (List LinkUnit) := do
  if let some doc := objectAil b then return [{ name := path, prog := ← lift "" (decodeAil path doc) }]
  match arMembers b with
  | some members =>
    members.filterMapM fun (n, data) => do
      let name := s!"{path}({n})"
      match objectAil data with
      | some doc => return some { name, prog := ← lift "" (decodeAil name doc) }
      | none => failWith 1 (foreignObject name)
  | none => failWith 1 (foreignObject path)

/-! ## Queries -/

def answer (o : Options) (q : Query) : IO Unit := do
  let m := o.target.getD .x86_64
  let rt ← runtimeDir o
  match q with
  | .version => IO.print (versionText m)
  | .help =>
    IO.println "usage: ccomp [options] file...\nOptions (gcc's meaning; docs/CCompilerDriver.md):"
    for sp in specs do
      IO.println s!"  {sp.spelling}{if sp.form == .flag then "" else "…"}  {sp.doc}"
  | .dumpversion | .dumpfullversion => IO.println ccompVersion
  | .dumpmachine | .printMultiarch => IO.println m.triple
  | .printProgName p => IO.println (progName p)
  | .printFileName f =>
    let mut found := f
    for d in o.libDirs ++ [rt] do
      if ← System.FilePath.pathExists s!"{d}/{f}" then
        found := s!"{d}/{f}"
        break
    IO.println found
  | .printSearchDirs =>
    IO.println s!"install: {rt}/\nprograms: ={rt}/\nlibraries: ={":".intercalate (o.libDirs ++ [rt])}"
  | .printLibgccFileName => IO.println "libgcc.a"
  | .printMultiOsDirectory => IO.println "../lib"
  | .printSysroot => IO.println ""

/-! ## Run -/

structure FileInput where
  path : String
  lang : Lang
  kind : InputKind
  index : Nat

def unusedInput (path : String) : IO Unit :=
  IO.eprintln s!"ccomp: warning: {path}: linker input file unused because linking not done"

mutual

def run (o : Options) : CM Unit := do
  let files : List FileInput := (o.inputs.filterMap fun
      | .file p l => some (p, l)
      | _ => none).zipIdx.map fun ((p, l), i) => ⟨p, l, InputKind.ofFile p l, i⟩
  if files.isEmpty then throw { severity := .fatal, message := "no input files", code := 1 }
  if o.mode != .preprocess && files.any (fun f => f.path == "-" && f.lang == .none) then
    throw { severity := .fatal, message := "-E or -x required when input is from standard input" }
  let stdin ← if files.any (·.path == "-") then (← IO.getStdin).readBinToEnd else pure .empty
  let tmp := s!"{← env "TMPDIR" "/tmp"}/ccomp.{← IO.monoNanosNow}"
  IO.FS.createDirAll tmp
  try
    match o.mode with
    | .assemble => failWith 2 "-S is not supported: ccomp has no assembly output (use -c)"
    | .preprocess =>
      if o.output.isSome && files.length > 1 then
        failWith 2 "cannot specify '-o' with '-c', '-S' or '-E' with multiple files"
      for f in files do
        if f.kind == .linkInput || f.kind == .ail then
          unusedInput f.path
        else
          let kind := if f.kind == .preprocessed then .preprocessed else .c
          let lang := if f.path == "-" && f.lang == .none then .c else f.lang
          let text ← preprocess o f.path lang kind stdin
          if !o.dryRun then
            match o.output with
            | some out => IO.FS.writeBinFile out text
            | none => (← IO.getStdout).write text
    | .compile =>
      let compiled := files.filter fun f => f.kind != .linkInput
      if o.output.isSome && compiled.length > 1 then
        failWith 2 "cannot specify '-o' with '-c', '-S' or '-E' with multiple files"
      for f in files do
        compileOne o tmp stdin f
    | .link => link o tmp files stdin
  finally
    (try IO.FS.removeDirAll tmp catch _ => pure () : IO Unit)

/-- `-c` of one input. -/
def compileOne (o : Options) (tmp : String) (stdin : ByteArray) (f : FileInput) : CM Unit := do
  match f.kind with
  | .linkInput => unusedInput f.path
  | .header => failWith 2 s!"{f.path}: precompiled headers are not supported"
  | .asm | .asmCpp => failWith 2 s!"{f.path}: assembler input is not supported by ccomp"
  | .ail =>
    let doc ← IO.FS.readFile f.path
    let obj ← lift "" (docObject o f.path doc)
    IO.FS.writeBinFile (objectName o f.path) obj
  | .c | .preprocessed =>
    let text ← timed o s!"preprocess {f.path}" (inputText o f.path f.lang f.kind stdin)
    if o.dryRun then return
    let obj ← timed o s!"frontend {f.path}" do
      if o.ailFromOracle then
        let doc ← oracleDoc o tmp f.path f.index text
        lift "" (docObject o f.path doc)
      else lift s!"{f.path}: " (Driver.compileTU o text)
    IO.FS.writeBinFile (objectName o f.path) obj

/-- Compile and link everything, in command-line order, with the C library and the runtime. -/
def link (o : Options) (tmp : String) (files : List FileInput) (stdin : ByteArray) : CM Unit := do
  let rt ← runtimeDir o
  let noLibc := o.noLibc || o.nostdlib || o.nodefaultlibs
  let mut units : List LinkUnit := []
  let mut ldArgs : List String := []
  -- the C library, with Cerberus's headers whatever the program's preprocessor
  if !noLibc then
    let libo : Options :=
      { ailFromOracle := o.ailFromOracle, verbose := o.verbose, dryRun := o.dryRun, float := o.float }
    let lib := s!"{rt}/libc.c"
    let text ← preprocess libo lib .none .c .empty
    if !o.dryRun then
      let prog ← timed o s!"frontend {lib}" (textAil libo tmp lib 0 text)
      units := units ++ [{ name := lib, prog, weak := true }]
  let mut fileIdx := 0
  for inp in o.inputs do
    match inp with
    | .file .. =>
      let some f := files[fileIdx]? | failWith 2 "internal error: inputs"
      fileIdx := fileIdx + 1
      match f.kind with
      | .c | .preprocessed =>
        let text ← timed o s!"preprocess {f.path}" (inputText o f.path f.lang f.kind stdin)
        if !o.dryRun then
          let prog ← timed o s!"frontend {f.path}" (textAil o tmp f.path (f.index + 1) text)
          units := units ++ [{ name := f.path, prog }]
      | .ail => units := units ++ [{ name := f.path, prog := ← lift "" (decodeAil f.path (← IO.FS.readFile f.path)) }]
      | .header => failWith 2 s!"{f.path}: precompiled headers are not supported"
      | .asm | .asmCpp => failWith 2 s!"{f.path}: assembler input is not supported by ccomp"
      | .linkInput => units := units ++ (← linkInputUnits f.path (← readBin f.path))
    | .lib n =>
      match ← findLib o rt n with
      | some p => units := units ++ (← linkInputUnits p (← readBin p))
      | none =>
        if n ∈ providedLibs then
          if o.verbose then IO.eprintln s!"ccomp: note: -l{n}: provided by ccomp's runtime"
        else failWith 1 s!"cannot find -l{n}: No such file or directory"
    | .linkerCommas p => ldArgs := ldArgs ++ (p.splitOn ",").filter (!·.isEmpty)
    | .linker a => ldArgs := ldArgs ++ [a]
  if o.dryRun then return
  let mirUnits ← timed o "middle" (lift "" (lowerUnits o units))
  -- `CCOMP_MIR_OPT=0` skips the Mir passes (for differential testing)
  let mirUnits ← if (← env "CCOMP_MIR_OPT" "1") == "0" then pure mirUnits
    else timed o "mirOpt" (do return optimizeMir mirUnits)
  let linked ← timed o "link" (lift "" (linkMir mirUnits))
  if let some f := o.emitLir then IO.FS.writeFile f (showLir linked)
  let obj ← timed o "backend" (lift "" (backend o linked))
  let objPath := s!"{tmp}/prog.o"
  IO.FS.writeBinFile objPath obj
  let out := o.output.getD "a.out"
  timed o "system link" do
    let crt0o := s!"{tmp}/crt0.o"
    match targetArch o with
    | .x86_64 =>
      let _ ← tool o "as" #["--64", "-o", crt0o, s!"{rt}/crt0-x86_64.S"]
      let _ ← tool o "ld" (#["-static", "-nostdlib", "-z", "noexecstack", "-o", out, crt0o, objPath] ++
        ldArgs.toArray)
    | .rv64 =>
      -- not part of the evaluated pipeline yet (x86-64 first)
      let pre ← env "CCOMP_RV64_PREFIX" "riscv64-linux-gnu-"
      let _ ← tool o s!"{pre}as" #["-march=rv64im", "-mabi=lp64", "-o", crt0o, s!"{rt}/crt0-rv64.S"]
      let _ ← tool o s!"{pre}ld" (#["-static", "-nostdlib", "-z", "noexecstack", "-o", out, crt0o,
        objPath] ++ ldArgs.toArray)

end

def readResponseFile (p : String) : IO (Option String) := do
  try return some (← IO.FS.readFile p) catch _ => return none

def main (args : List String) : IO UInt32 := do
  let extra := responseTokens (← env "CCOMP_OPTIONS" "")
  let args ← expandResponseFiles readResponseFile 64 (extra ++ args)
  match parseArgs args with
  | .error d => IO.eprintln d.render; return d.code
  | .ok o =>
    let ds := o.checks
    for d in ds do IO.eprintln d.render
    if let some d := ds.find? (·.severity == .error) then return d.code
    if o.verbose then
      IO.eprintln s!"ccomp version {ccompVersion} (Silmaril)\nTarget: {(o.target.getD .x86_64).triple}\nThread model: single"
      for d in o.notes do IO.eprintln d.render
    if !o.queries.isEmpty then
      for q in o.queries do answer o q
      return 0
    if o.verbose && (o.inputs.all fun | .file .. => false | _ => true) then return 0
    match ← (run o).run with
    | .ok () => return 0
    | .error d => IO.eprintln d.render; return d.code

end Silmaril.Compile.C.Main
