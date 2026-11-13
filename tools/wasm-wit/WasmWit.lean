import Silmaril.Wasm.Wit.Tool.Defs
import Silmaril.Wasm.Wit.Tool.Source.Defs
import Silmaril.Wasm.Perf.WatPrint.Defs
import Silmaril.Wasm.Perf.WatReadB.Defs

/-!
# `wasm-wit`

Command-line front end of `Silmaril.Wasm.Wit.Tool`. This file only reads the input
files, calls one pure function of the core and writes its result; every
transformation is in `Silmaril/Wasm/Wit/Tool/Defs.lean` and
`Silmaril/Wasm/Wit/Tool/Source/Defs.lean` (theorems in `Silmaril.Wasm.Wit.Tool.Thms`
and `Silmaril.Wasm.Wit.Tool.Source.Thms`). See `tools/wasm-tools/README.md`.

```
wasm-wit print   IN.wasm [-o OUT.wat]              component bytes → component WAT
wasm-wit parse   IN.wat  [-o OUT.wasm]             component WAT → component bytes
wasm-wit decode  SRC                               the WIT package (model)
wasm-wit wit     SRC [-o OUT.wit]                  WIT text, with the dependency packages
wasm-wit encode  SRC [-o OUT.wasm]                 the bytes of `wasm-tools component wit --wasm`
wasm-wit check   SRC                               validity, distinct names, canonical, fixpoint
wasm-wit project IN.wasm|IN.wat [-o OUT.wat|OUT.wasm]
                                                    the world (component type) of a component
wasm-wit embed   SRC --world W [--encoding E] [--into CORE.wasm] [-o OUT.wasm]
                                                    the `component-type` payload of a world
wasm-wit extract CORE.wasm [-o OUT.wit|OUT.wasm]   the world a core module embeds
```

`SRC` is a WIT binary (`.wasm`), a WIT file (`.wit`) or a directory holding one
`.wit` file (and possibly `deps/`). WIT text takes `--deps DIR` (each `.wit` file
of `DIR`, and each subdirectory holding one `.wit` file, is a dependency
document; default `SRC/deps` for a directory) and `--features F1,F2` (enables
`@unstable` items).

Exit status: 0 on success (for `check`: every check passed), 1 on a failed
command or check, 2 on a usage error.
-/

open Silmaril.Wasm.Component
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Wit.Tool

def usage : String := String.intercalate "\n" [
  "usage: wasm-wit COMMAND IN [options]",
  "",
  "  print   IN.wasm [-o OUT.wat]      component bytes to component WAT",
  "  parse   IN.wat  [-o OUT.wasm]     component WAT to component bytes",
  "  decode  SRC                       print the WIT package model",
  "  wit     SRC [-o OUT.wit]          WIT text with the dependency packages (unverified printer)",
  "  encode  SRC [-o OUT.wasm]         the WIT package as a type-only component",
  "  check   SRC                       check validity and the round trip",
  "  project IN.(wasm|wat) [-o OUT]    the world of a component (projectX), as WAT (bytes if OUT ends in .wasm)",
  "  embed   SRC --world W [--encoding utf8|utf16|compact-utf16] [--into CORE.wasm] [-o OUT]",
  "                                    the component-type payload of a world (appended to CORE.wasm with --into)",
  "  extract CORE.wasm [-o OUT]        the world embedded in a core module, as WIT (payload if OUT ends in .wasm)",
  "",
  "SRC: IN.wasm (a WIT binary), IN.wit or a directory with one .wit file; WIT text takes",
  "  --deps DIR (default SRC/deps for a directory) and --features F1,F2.",
  ""]

/-- Write text to `OUT` or standard output. -/
def emitText (out : Option String) (t : String) : IO Unit :=
  match out with
  | some f => IO.FS.writeFile f t
  | none => IO.print t

/-- Write bytes to `OUT` or standard output. -/
def emitBytes (out : Option String) (b : ByteArray) : IO Unit :=
  match out with
  | some f => IO.FS.writeBinFile f b
  | none => do (← IO.getStdout).write b

def orFail {α} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"wasm-wit {what}: {e}")

def yesNo (b : Bool) : String := if b then "yes" else "no"

/-- Options after the input. -/
structure Opts where
  out : Option String := none
  deps : Option String := none
  features : List String := []
  world : Option String := none
  encoding : Binary.StringEncoding := .utf8
  into : Option String := none

def parseOpts : Opts → List String → Except String Opts
  | o, [] => pure o
  | o, "-o" :: f :: r => parseOpts { o with out := some f } r
  | o, "--deps" :: d :: r => parseOpts { o with deps := some d } r
  | o, "--features" :: fs :: r =>
    parseOpts { o with features := o.features ++ (fs.splitOn ",").filter (· ≠ "") } r
  | o, "--world" :: w :: r => parseOpts { o with world := some w } r
  | o, "--into" :: f :: r => parseOpts { o with into := some f } r
  | o, "--encoding" :: e :: r =>
    match e with
    | "utf8" => parseOpts { o with encoding := .utf8 } r
    | "utf16" => parseOpts { o with encoding := .utf16 } r
    | "compact-utf16" => parseOpts { o with encoding := .compactUtf16 } r
    | _ => throw s!"unknown encoding {e}"
  | _, a :: _ => throw s!"unexpected argument {a}"

/-- The `.wit` files of a directory, sorted. -/
def witFiles (dir : String) : IO (Array String) := do
  let es ← System.FilePath.readDir dir
  let fs ← es.filterM fun e => do
    pure (e.fileName.endsWith ".wit" && !(← e.path.isDir))
  pure ((fs.map (·.path.toString)).qsort (· < ·))

/-- The one `.wit` file of a directory. -/
def oneWit (dir : String) : IO String := do
  match (← witFiles dir).toList with
  | [f] => pure f
  | [] => throw (IO.userError s!"wasm-wit: no .wit file in {dir}")
  | _ => throw (IO.userError
      s!"wasm-wit: several .wit files in {dir} (multi-file packages are not supported)")

/-- The dependency documents of a `deps` directory: its `.wit` files, then its
subdirectories holding one `.wit` file, as `(path, text)`. -/
def readDeps (dir : String) : IO (List (String × String)) := do
  let files ← witFiles dir
  let es ← System.FilePath.readDir dir
  let subs ← es.filterM fun e => e.path.isDir
  let subs := (subs.map (·.path.toString)).qsort (· < ·)
  let mut out := []
  for f in files do out := out ++ [(f, ← IO.FS.readFile f)]
  for d in subs do
    let f ← oneWit d
    out := out ++ [(f, ← IO.FS.readFile f)]
  pure out

/-- The WIT text of a source: main `(path, text)` and dependencies. -/
def readSource (inp : String) (o : Opts) : IO ((String × String) × List (String × String)) := do
  let isDir ← System.FilePath.isDir inp
  let main ← if isDir then oneWit inp else pure inp
  let dflt := System.FilePath.mk inp / "deps"
  let depDir ← match o.deps with
    | some d => pure (some d)
    | none => if isDir && (← dflt.isDir) then pure (some dflt.toString) else pure none
  let deps ← match depDir with
    | some d => readDeps d
    | none => pure []
  pure ((main, ← IO.FS.readFile main), deps)

/-- `SRC` is WIT text (a `.wit` file or a directory). -/
def isText (inp : String) : IO Bool := do
  pure (inp.endsWith ".wit" || (← System.FilePath.isDir inp))

/-- The bytes of a source: a binary as is, WIT text through `encodeText`. -/
def sourceBytes (cmd inp : String) (o : Opts) : IO ByteArray := do
  if ← isText inp then
    let (m, ds) ← readSource inp o
    orFail cmd (encodeText m ds o.features)
  else IO.FS.readBinFile inp

def report (b : ByteArray) (r : Report) : IO UInt32 := do
  let p := r.decoded.pkg
  IO.println s!"package:   {p.name.ns}:{p.name.name}{(p.name.version.map ("@" ++ ·)).getD ""} \
    ({p.interfaces.length} interfaces, {p.worlds.length} worlds; \
    {r.decoded.env.length} interfaces shown)"
  IO.println s!"valid:     {yesNo r.valid}"
  IO.println s!"unique:    {yesNo r.unique}"
  IO.println s!"canonical: {yesNo r.canonical}"
  IO.println s!"encodes:   {yesNo r.reencoded.isSome}"
  IO.println s!"fixpoint:  {yesNo r.fixpoint} ({b.size} bytes in, \
    {(r.reencoded.map (·.size)).getD 0} bytes re-encoded)"
  IO.println s!"ok:        {yesNo r.ok}"
  pure (if r.ok then 0 else 1)

def encodingName : Binary.StringEncoding → String
  | .utf8 => "utf8" | .utf16 => "utf16" | .compactUtf16 => "compact-utf16"

def run (cmd inp : String) (o : Opts) : IO UInt32 := do
  let out := o.out
  match cmd with
  | "print" =>
    -- `printWatF = printWat` (`Perf.WatPrint.printWatF_eq`), with a string builder
    let t ← orFail cmd (Silmaril.Wasm.Perf.WatPrint.printWatF (← IO.FS.readBinFile inp))
    emitText out (t ++ "\n"); pure 0
  | "parse" =>
    -- `parseWatB = parseWat` (`Perf.WatReadB.parseWatB_eq`): on ASCII text the lexer reads the
    -- UTF-8 bytes by index (no `List Char` of the text), else the tail-recursive `WatRead` lexer
    let b ← orFail cmd (Silmaril.Wasm.Perf.WatReadB.parseWatB (← IO.FS.readFile inp))
    emitBytes out b; pure 0
  | "decode" =>
    let d ← orFail cmd (decode (← sourceBytes cmd inp o))
    emitText out (toString (repr d.pkg) ++ "\n"); pure 0
  | "wit" =>
    let t ← orFail cmd (witAll (← sourceBytes cmd inp o))
    emitText out t; pure 0
  | "encode" =>
    if ← isText inp then
      emitBytes out (← sourceBytes cmd inp o); pure 0
    else
      let b ← orFail cmd (reencode (← IO.FS.readBinFile inp))
      emitBytes out b; pure 0
  | "check" =>
    if ← isText inp then
      let (m, ds) ← readSource inp o
      let (b, r) ← orFail cmd (checkText m ds o.features)
      report b r
    else
      let b ← IO.FS.readBinFile inp
      report b (← orFail cmd (check b))
  | "project" =>
    let w ← if inp.endsWith ".wat" then orFail cmd (projectWatX (← IO.FS.readFile inp))
      else orFail cmd (projectBytesX (← IO.FS.readBinFile inp))
    match out with
    | some f =>
      if f.endsWith ".wasm" then
        -- `encodeF = Binary.encode` (`Perf.EncodeB.encode_eq_encodeF`), `printF = Wat.print`
        -- (`Perf.WatPrint.printF_eq`): the fast implementations, called directly
        match Silmaril.Wasm.Perf.EncodeB.encodeF (worldAst w) with
        | some b => IO.FS.writeBinFile f b; pure 0
        | none => throw (IO.userError "wasm-wit project: a number or size exceeds 2^32")
      else emitText out (Silmaril.Wasm.Perf.WatPrint.printF (worldAst w) ++ "\n"); pure 0
    | none => emitText none (Silmaril.Wasm.Perf.WatPrint.printF (worldAst w) ++ "\n"); pure 0
  | "embed" =>
    let some w := o.world | IO.eprint "wasm-wit embed: --world is required\n"; pure 2
    let pl ← if ← isText inp then do
        let (m, ds) ← readSource inp o
        orFail cmd (embedText m ds o.features w o.encoding)
      else orFail cmd (embedBytes (← IO.FS.readBinFile inp) w o.encoding)
    match o.into with
    | some core => emitBytes out (← orFail cmd (Binary.embedPayload (← IO.FS.readBinFile core) pl))
    | none => emitBytes out pl
    pure 0
  | "extract" =>
    let m ← IO.FS.readBinFile inp
    if (out.map (·.endsWith ".wasm")).getD false then
      emitBytes out (← orFail cmd (Binary.extractPayload m)); return 0
    let (p, n, w, se) ← orFail cmd (Binary.extractWorldType m)
    IO.eprintln s!"wasm-wit extract: world {n}, string encoding {encodingName se}"
    emitText out (Binary.printPackage { name := p, worlds := [(n, w)] }); pure 0
  | _ => IO.eprint usage; pure 2

def main (args : List String) : IO UInt32 := do
  match args with
  | cmd :: inp :: rest =>
    match parseOpts {} rest with
    | .ok o => run cmd inp o
    | .error e => IO.eprintln s!"wasm-wit: {e}"; IO.eprint usage; pure 2
  | _ => IO.eprint usage; pure 2
