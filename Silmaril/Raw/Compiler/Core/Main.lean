module

public import Silmaril.Compiler.Core.Verified.Defs
public import Silmaril.Compiler.Core.Emit.Defs
public import Silmaril.Compiler.Core.Reader.Defs
/-! # `ccomp-verified`: the verified Core route's driver (trusted, frozen)

```
ccomp-verified [-o OUT] FILE
```

`FILE` is C (`.c`, preprocessed with Cerberus's command), preprocessed C (`.i`) or a Core
document (`.core`, `.sexp`: `cerb-oracle --level core`). The driver obtains the Core
document of the input from Cerberus (`cerb-oracle --level core`; cached by the SHA-256 of the
preprocessed text in `CCOMP_CORE_CACHE` when that is set), decodes
it with the checked reader `Reader.read` (proved equal to `Codec.WellFormed.parseDocument`:
`Reader.read_eq`), checks the pins and runs
`Verified.compile`. `none` is the exit status 1 with "outside the verified fragment";
`some a` is written by `Emit.object`, assembled with `crt0-x86_64.S` and linked by
`Emit.ldArgs` into the static executable `OUT` (default `a.out`). No other code is linked:
there is no C library on this route.

Trust restriction (wide constants): Cerberus (pin b3e11ea33) decodes wide and Unicode
character constants wrongly (as signed 8-bit `char`), and inside an enumerator the constant
is folded to a plain `int`, so no check on the Core document can see it. C and preprocessed
C input whose text contains an `L`, `u` or `U` character or string literal token is
therefore refused before Cerberus runs, like a program outside the verified fragment
(`wideLiteral`). `u8` strings are byte-identical to ordinary strings in Core and are not
refused. A raw Core document (`.core`, `.sexp`) is not checked: for those inputs the Core
document itself is the trust boundary.

Exit status: 0 success, 1 rejected (Cerberus rejects the program, or it is outside the
verified fragment), 2 usage or I/O error, 3 an external tool failed.

Configuration (environment; `docs/projects/cerberus.md`, "Running it"):

* `CERB_RUNTIME`: Cerberus's runtime directory, whose `libc/include` headers preprocess `.c`
  input. Default: `$OPAM_SWITCH_PREFIX/lib/cerberus-lib/runtime` (the opam install of
  `cerberus-lib` at the pinned commit).
* `CERB_ORACLE`: the pinned Core exporter, run as `CERB_ORACLE --level core --output OUT IN.i`.
  Default: `cerb-oracle` on `PATH`.
* `CCOMP_CORE_CACHE` (optional) and `TMPDIR`.

This file is part of the trusted base and is frozen with `Spec.lean` and `Emit.lean`. (The
release copy differs from the campaign's frozen copy only in these defaults, which were paths
on the campaign host.)
-/

@[expose] public section

namespace Silmaril.Compile.Core.Main

open Silmaril.Cerberus

structure Failure where
  code : UInt32
  msg : String

abbrev CM := ExceptT Failure IO

def failWith {α : Type} (code : UInt32) (msg : String) : CM α := throw ⟨code, msg⟩

def env (name dflt : String) : IO String := do return (← IO.getEnv name).getD dflt

def tool (cmd : String) (args : Array String) : CM String := do
  let r ← (IO.Process.output { cmd, args } : IO _)
  if r.exitCode != 0 then failWith 3 s!"{cmd} failed ({r.exitCode}): {r.stderr.take 2000}"
  return r.stdout

/-- `CERB_RUNTIME`, else the runtime of the opam switch `OPAM_SWITCH_PREFIX`. -/
def cerbRuntime : CM String := do
  match ← IO.getEnv "CERB_RUNTIME", ← IO.getEnv "OPAM_SWITCH_PREFIX" with
  | some rt, _ => return rt
  | none, some sw => return s!"{sw}/lib/cerberus-lib/runtime"
  | none, none =>
    failWith 2 "error: set CERB_RUNTIME to Cerberus's runtime directory (or OPAM_SWITCH_PREFIX)"

/-- Cerberus's preprocessing of a `.c` file (as `ccomp` and `cerb-oracle` do). -/
def preprocess (path : String) : CM ByteArray := do
  let rt ← cerbRuntime
  let args := #["-std=c11", "-E", "-CC", "-Werror", "-Wno-builtin-macro-redefined", "-nostdinc",
    "-undef", "-D__cerb__", s!"-I{rt}/libc/include", s!"-I{rt}/libc/include/posix", "-include",
    s!"{rt}/libc/include/builtins.h", path]
  let r ← (IO.Process.output { cmd := "cc", args } : IO _)
  if r.exitCode != 0 then failWith 1 s!"error: {path}: preprocessing failed: {r.stderr.take 2000}"
  return r.stdout.toUTF8

/-- The Core document of preprocessed text, from Cerberus (cached). -/
def coreOf (tmp : String) (text : ByteArray) : CM String := do
  let iPath := s!"{tmp}/input.i"
  IO.FS.writeBinFile iPath text
  let cache ← env "CCOMP_CORE_CACHE" ""
  if !cache.isEmpty then
    let key := ((← tool "sha256sum" #[iPath]).splitOn " ").head!
    let cached := s!"{cache}/{key}.core.sexp"
    if ← System.FilePath.pathExists cached then return ← IO.FS.readFile cached
  let oracle ← env "CERB_ORACLE" "cerb-oracle"
  let out := s!"{tmp}/input.core.sexp"
  let r ← (IO.Process.output { cmd := oracle, args := #["--level", "core", "--output", out, iPath] } : IO _)
  if r.exitCode == 1 then failWith 1 s!"error: Cerberus rejects the program: {r.stderr.take 2000}"
  if r.exitCode != 0 then failWith 3 s!"cerb-oracle failed ({r.exitCode}): {r.stderr.take 2000}"
  IO.FS.readFile out

/-- Whether the byte `b` can continue an identifier or a preprocessing number (`[0-9A-Za-z_$]`):
an `L`, `u` or `U` after such a byte is not the start of a token. -/
def identByte (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || b == 95 || b == 36

/-- The lexical context of a byte of C text, for `wideLiteral`. -/
inductive Lex where
  | code | str | strEsc | chr | chrEsc | lineComment | blockOpen | block | blockStar

/-- Whether C text contains a wide or Unicode character or string literal token: `L'`, `u'`,
`U'`, `L"`, `u"` or `U"` where the prefix starts a token (it does not follow an identifier or
number byte). Occurrences inside ordinary string literals, character literals and comments
(kept by `-CC`) do not count. `u8"…"` does not count: after `u` the next byte is `8`, and the
`"` then follows an identifier byte. -/
def wideLiteral (t : ByteArray) : Bool := Id.run do
  let mut st := Lex.code
  let mut prev : UInt8 := 10
  for i in [0:t.size] do
    let b := t.data.getD i 0
    let next := t.data.getD (i + 1) 0
    match st with
    | .code =>
      if b == 34 then st := .str                                    -- "
      else if b == 39 then st := .chr                               -- '
      else if b == 47 && next == 42 then st := .blockOpen           -- /*
      else if b == 47 && next == 47 then st := .lineComment         -- //
      else if (b == 76 || b == 117 || b == 85) && !identByte prev && -- L u U
          (next == 39 || next == 34) then
        return true
    | .str => if b == 92 then st := .strEsc else if b == 34 || b == 10 then st := .code
    | .strEsc => st := .str
    | .chr => if b == 92 then st := .chrEsc else if b == 39 || b == 10 then st := .code
    | .chrEsc => st := .chr
    | .lineComment => if b == 10 then st := .code
    | .blockOpen => st := .block
    | .block => if b == 42 then st := .blockStar
    | .blockStar => if b == 47 then st := .code else if b != 42 then st := .block
    prev := b
  return false

/-- The trust restriction on C and preprocessed C input (see the module documentation). -/
def trusted (path : String) (text : ByteArray) : CM ByteArray := do
  if wideLiteral text then
    failWith 1 s!"error: {path}: outside the verified fragment (trust restriction: wide constant)"
  return text

/-- The decoded Core document of an input file. C and preprocessed C pass the trust restriction
`trusted` first; a raw Core document (`.core`, `.sexp`) is read as is: for those inputs the
Core document is the trust boundary. -/
def document (tmp path : String) : CM Codec.Document := do
  let text ← if path.endsWith ".c" then coreOf tmp (← trusted path (← preprocess path))
    else if path.endsWith ".i" then coreOf tmp (← trusted path (← IO.FS.readBinFile path))
    else IO.FS.readFile path
  match Reader.read text with
  | .error e => failWith 1 s!"error: {path}: not a Core document (a reject?): {e.message}"
  | .ok doc =>
    if doc.commit != "b3e11ea334e95359907d4abf9194f0e7fedc6c6a" ||
        doc.implementation != "gcc_4.9.0_x86_64-apple-darwin10.8.0" then
      failWith 1 s!"error: {path}: Core document with unsupported pins"
    return doc

/-- `RUNTIME`: `tools/ccomp-verified/runtime` of the checkout the executable was built in. It holds
the verified route's startup code, which passes `argc`/`argv` (the file that `Spec.observe` mirrors;
`Spec.lean` and `Emit.lean` still name its campaign path `tools/ccomp/runtime/crt0-x86_64.S`, where
ccomp's own startup code now lives: docs/CompilerConsolidation.md, "Forks"). -/
def runtimeDir : IO String := do
  let app ← IO.appPath
  let root := (((app.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD "."
  return (root / "tools" / "ccomp-verified" / "runtime").toString

def run (out input : String) : CM Unit := do
  let tmp := s!"{← env "TMPDIR" "/tmp"}/ccomp-verified.{← IO.monoNanosNow}"
  IO.FS.createDirAll tmp
  try
    let doc ← document tmp input
    match Verified.compile doc with
    | none => failWith 1 s!"error: {input}: outside the verified fragment"
    | some a =>
      let obj := s!"{tmp}/prog.o"
      IO.FS.writeBinFile obj (Emit.object a)
      let crt0 := s!"{tmp}/crt0.o"
      let _ ← tool "as" #["--64", "-o", crt0, s!"{← runtimeDir}/crt0-x86_64.S"]
      let _ ← tool "ld" (Emit.ldArgs a out obj crt0)
  finally
    (try IO.FS.removeDirAll tmp catch _ => pure () : IO Unit)

def usage : String := "usage: ccomp-verified [-o OUT] FILE"

def main (args : List String) : IO UInt32 := do
  let (out, rest) := match args with
    | "-o" :: o :: rest => (o, rest)
    | rest => ("a.out", rest)
  let rest := rest.filter (fun a => a != "--via" && a != "core" && a != "--verified")
  match rest with
  | [input] =>
    match ← (run out input).run with
    | .ok () => return 0
    | .error f => IO.eprintln s!"ccomp-verified: {f.msg}"; return f.code
  | _ => IO.eprintln usage; return 2

end Silmaril.Compile.Core.Main
