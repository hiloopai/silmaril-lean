module

public import Silmaril.Compiler.Clang.Json.Defs
public import Silmaril.Compiler.Clang.ToAil.Defs
public import Silmaril.Cerberus.Ail.Codec.Defs

/-! # `cfront`: the Clang frontend driver

```
cfront decode FILE.json   -- decode Clang's JSON AST and print it back (compact JSON), exit 0
cfront ail FILE.json      -- translate it to typed Ail: a `$document_tail` document, exit 0
cfront ail --partial FILE.json -- omit failed bodies as declarations, report skips on stderr
cfront ail --producer TEXT FILE.json -- name the AST's producer in the document header
```

The header of a printed document names its producer. A JSON AST does not say which clang wrote
it, so cfront does not claim one: the header is `cfront (AST producer not recorded)` unless the
caller, who ran clang, passes `--producer` (for example the first line of `clang --version`).
The header is metadata taken from the caller, not checked by cfront.

`FILE.json` is the output of the pinned `clang -Xclang -ast-dump=json -fsyntax-only` (see
`Silmaril.Clang.AST`). `ail` prints the typed Ail in the oracle's S-expression format
(`cerb-oracle --level tail`, `Silmaril.Cerberus.Ail.Codec`), so ccomp (`ccomp -o BIN X.sexp`) and
csem (`csem run X.sexp`) consume it unchanged; when the translation rejects the program it prints
a `$reject` document (stage `cfront`) and exits 1.

Exit status: 0 success; 1 the translation rejects the program; 3 the JSON does not decode (unknown
node kind or key; message on stderr); 2 usage or I/O error. The driver reads its input file and
nothing else: no processes, no environment, no other files.
-/

@[expose] public section

namespace Silmaril.Clang.Main

open Silmaril.Cerberus Ail.Codec

/-- The default header of the documents `cfront ail` prints (module docstring): no clang version
is claimed. The implementation is the one the typed Ail assumes (Cerberus's, so the documents
are interchangeable). -/
def commit : String := "cfront (AST producer not recorded)"
def impl : String := "gcc_4.9.0_x86_64-apple-darwin10.8.0"

def usage : String :=
  "usage: cfront decode FILE.json\n       cfront ail [--partial] [--producer TEXT] FILE.json"

def load (path : String) : IO (Except String Node) := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes | return .error "input is not valid UTF-8"
  return Json.decode text

/-- Emit a document, optionally retaining unsupported function bodies as declarations. -/
def translateFile (path : String) (partialBodies : Bool) (commit : String := commit) :
    IO UInt32 := do
  let out ← IO.getStdout
  match ← load path with
  | .error e => IO.eprintln s!"cfront: {path}: {e}"; return 3
  | .ok n =>
    match ToAil.translateWith n partialBodies with
    | .ok (prog, skipped) =>
      for f in skipped do IO.eprintln s!"cfront: skipped {f.name}: {f.reason}"
      out.putStr (printTailDocument (.document commit impl prog)); out.flush; return 0
    | .error e =>
      out.putStr (printTailDocument (.reject commit impl "cfront" (.loc .unknown) e))
      out.flush
      IO.eprintln s!"cfront: {path}: {e}"
      return 1

def run (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | ["decode", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"cfront: {path}: {e}"; return 3
    | .ok n => out.putStrLn (Json.encode n); out.flush; return 0
  | "ail" :: rest =>
    let rec opts : List String → Bool → Option String → Option (Bool × Option String × String)
      | ["--partial", path], _, p => some (true, p, path)
      | "--partial" :: r, _, p => opts r true p
      | "--producer" :: t :: r, b, _ => opts r b (some t)
      | [path], b, p => if path.startsWith "--" then none else some (b, p, path)
      | _, _, _ => none
    match opts rest false none with
    | some (b, p, path) => translateFile path b (p.getD commit)
    | none => IO.eprintln usage; return 2
  | _ => IO.eprintln usage; return 2

def main (args : List String) : IO UInt32 := do
  try run args
  catch e => IO.eprintln s!"cfront: {e}"; return 2

end Silmaril.Clang.Main
