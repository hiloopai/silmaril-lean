module

public import Silmaril.Compiler.Driver.Options.Defs
/-! # Preprocessing as a pluggable stage

A `Preprocessor` turns (options, one input file) into the bytes of a `.i` file: preprocessed C
with GNU line markers (`# LINE "FILE" FLAGS`, unless `-P`), which the Cerberus parser (and
`Silmaril.Cerberus.Frontend.parse`) reads. Selected by `--preprocessor=`:

| kind | implementation | headers | used for |
| --- | --- | --- | --- |
| `cerberus` (default) | the system `cc -E` with `-nostdinc -undef -D__cerb__` | Cerberus's libc headers and `builtins.h` | the oracle-exact path: the headers our frontend and libc agree on |
| `system` | the system `cc -E` | the system headers (glibc), adapted for the frontend | programs that need system headers; see the trade-off below |
| `none` | none: the input is already preprocessed | — | `.i` inputs (always), or `--preprocessor=none` |
| `lean` | not yet implemented | — | the slot of a Lean preprocessor (docs/CCompilerDriver.md, roadmap) |

The argument lists are pure functions (`cerberusArgs`, `systemArgs`, `userArgs`, `depArgs`): what
is passed to the external `cpp` is part of the model and can be reasoned about; `run` only
executes them.

## The header trade-off

glibc's headers, as gcc preprocesses them, use GNU C: `__attribute__`, `__asm__`, `__extension__`,
`__builtin_va_list`, `__inline`, and (with gcc's default `-std=gnu17`) `sys/select.h` with a cast
in an integer constant expression. Cerberus's frontend rejects these. `system` therefore

* undefines `__GNUC__` (`-U__GNUC__ -U__GNUC_MINOR__ -U__GNUC_PATCHLEVEL__`), so that
  `sys/cdefs.h` defines `__attribute__`, `__extension__`, `__inline`, `__restrict` away, as it does
  for non-GNU compilers;
* defines `__builtin_va_list` as `int`, Cerberus's `va_list` (`stdarg.h` of gcc otherwise declares
  `typedef __builtin_va_list __gnuc_va_list`);
* uses `-std=c11` unless `-std=` is given, so that `__STRICT_ANSI__` keeps the GNU and POSIX
  extensions out (`_DEFAULT_SOURCE` pulls in `sys/select.h`).

What it cannot fix: glibc's *ABI* names are not the ones of ccomp's C library
(`tools/ccomp/runtime/libc.c`, written against Cerberus's headers): `stdout` is a glibc object
(`extern FILE *stdout`; Cerberus's headers say `__stdout`), `errno` is `(*__errno_location ())`,
`assert` calls `__assert_fail`, `getc` may be a macro over `_IO_getc`, `isdigit` uses
`__ctype_b_loc`. Programs using these preprocess and compile with `system` but fail to link
(undefined references). The default is therefore `cerberus`, whose headers and libc agree.
-/

@[expose] public section

namespace Silmaril.Compile.Driver

/-- One preprocessing job. -/
structure PreprocessRequest where
  options : Options
  /-- the input file, `-` for stdin -/
  path : String
  /-- the `-x` language in force for the input (`none`: by suffix) -/
  lang : Lang := .none
  /-- the bytes of stdin, when `path` is `-` -/
  stdin : ByteArray := .empty

/-- The environment of the external preprocessors. -/
structure PreprocessEnv where
  /-- the C compiler driver used as `cpp` (env `CCOMP_CPP`, default `cc`) -/
  cc : String := "cc"
  /-- Cerberus's runtime: `libc/include` and `libc/include/builtins.h` (env `CERB_RUNTIME`) -/
  cerbRuntime : String := "cerberus-runtime"

/-- A preprocessor: the command it runs (for `-v` and `-###`), if it is external, and the run. -/
structure Preprocessor where
  kind : PreprocessorKind
  command : PreprocessEnv → PreprocessRequest → Option (String × List String)
  run : PreprocessEnv → PreprocessRequest → IO (Except Diag ByteArray)

/-! ## Arguments (pure) -/

def DirKind.flag : DirKind → String
  | .angled => "-I" | .quote => "-iquote" | .system => "-isystem" | .after => "-idirafter"

/-- The user's preprocessor options, in gcc's spelling and in command-line order within each
kind (the order gcc gives them meaning in, §3.13 and §3.16). -/
def userArgs (o : Options) : List String :=
  (o.dirs.flatMap fun (k, d) => [k.flag, d]) ++
  (o.macros.flatMap fun
    | .define m => ["-D", m]
    | .undef m => ["-U", m]) ++
  (o.forced.flatMap fun
    | (.include, f) => ["-include", f]
    | (.imacros, f) => ["-imacros", f]) ++
  (if o.nostdinc then ["-nostdinc"] else []) ++ (if o.undef then ["-undef"] else []) ++
  (if o.noLineMarkers then ["-P"] else []) ++ (if o.keepComments then ["-C"] else []) ++
  (if o.keepMacroComments then ["-CC"] else []) ++ (o.dumps.map ("-d" ++ ·)) ++
  (o.cppPass.map ("-Wp," ++ ·))

/-- Dependency options for the external `cpp`: `-M`/`-MM` as given (the rule replaces the
output), `-MD`/`-MMD` with the file and targets of `Options.depPlan` made explicit (since `cpp`
runs with its output on stdout, it cannot infer them from `-o`). -/
def depArgs (o : Options) (input : String) : List String :=
  if o.depM || o.depMM then
    (if o.depMM then ["-MM"] else ["-M"]) ++ (o.depMF.toList.flatMap (["-MF", ·])) ++
    (o.depMT.flatMap (["-MT", ·])) ++ (o.depMQ.flatMap (["-MQ", ·])) ++
    (if o.depMP then ["-MP"] else []) ++ (if o.depMG then ["-MG"] else [])
  else match o.depPlan input with
  | none => []
  | some p =>
    (if p.system then ["-MD"] else ["-MMD"]) ++ ["-MF", p.file] ++ (p.targets.flatMap (["-MT", ·])) ++
    (p.quoted.flatMap (["-MQ", ·])) ++ (if p.phony then ["-MP"] else []) ++
    (if p.missingOk then ["-MG"] else [])

/-- The input, with `-x c` for stdin and for `-x c` inputs with another suffix. -/
def inputArgs (r : PreprocessRequest) : List String :=
  if r.path == "-" || r.lang == .c then ["-x", "c", r.path] else [r.path]

/-- Cerberus's preprocessing (what `cerberus` runs: `Pipeline.cpp`), then the user's options. -/
def cerberusArgs (env : PreprocessEnv) (r : PreprocessRequest) : List String :=
  let rt := env.cerbRuntime
  ["-std=c11", "-E", "-CC", "-Werror", "-Wno-builtin-macro-redefined", "-nostdinc", "-undef",
    "-D__cerb__", s!"-I{rt}/libc/include", s!"-I{rt}/libc/include/posix", "-include",
    s!"{rt}/libc/include/builtins.h"] ++ userArgs r.options ++ depArgs r.options r.path ++ inputArgs r

/-- The flags that make glibc's headers acceptable to the frontend (see the module doc). -/
def systemCompatArgs (o : Options) : List String :=
  (match o.std with
    | some s => ["-std=" ++ s.name]
    | none => ["-std=c11"]) ++
  ["-U__GNUC__", "-U__GNUC_MINOR__", "-U__GNUC_PATCHLEVEL__", "-D__builtin_va_list=int"]

/-- The system preprocessor with the system headers. `-pthread` defines `_REENTRANT`. -/
def systemArgs (r : PreprocessRequest) : List String :=
  ["-E"] ++ systemCompatArgs r.options ++ (if r.options.pthread then ["-pthread"] else []) ++
    userArgs r.options ++ depArgs r.options r.path ++ inputArgs r

/-- The preprocessor kind for an input: preprocessed inputs need none (§3.2: `.i` is "C code that
should not be preprocessed"); otherwise `--preprocessor=`, by default `cerberus`. -/
def Options.preprocessorFor (o : Options) (kind : InputKind) : PreprocessorKind :=
  if kind == .preprocessed then .none else o.preprocessor.getD .cerberus

/-! ## Line markers (pure) -/

/-- A GNU line marker `# LINE "FILE" FLAGS` (cpp manual §9 "Preprocessor Output"): the next
line is line LINE of FILE; flag 1 enters a header, 2 returns to a file, 3 a system header. -/
structure LineMarker where
  /-- the 0-based line of the `.i` text the marker is on -/
  at_ : Nat
  line : Nat
  file : String
  flags : List Nat
  deriving DecidableEq, Repr

/-- Read the GNU line markers of a `.i` text (`#line N "F"` is read as well). -/
def lineMarkers (text : ByteArray) : List LineMarker :=
  let s := String.fromUTF8? text |>.getD ""
  (s.splitOn "\n").zipIdx.filterMap fun (l, i) => do
    let l := if l.startsWith "#line " then "# " ++ (l.drop 6).toString else l
    guard (l.startsWith "# ")
    let ws := (l.drop 2).toString.splitOn " "
    let n ← ws.head?.bind String.toNat?
    let f ← ws[1]?
    guard (f.startsWith "\"" && f.endsWith "\"" && f.length ≥ 2)
    return { at_ := i, line := n, file := ((f.drop 1).dropEnd 1).toString
             flags := (ws.drop 2).filterMap String.toNat? }

/-! ## Implementations -/

def runExternal (cmd : String) (args : List String) (stdin : ByteArray) (path : String) :
    IO (Except Diag ByteArray) := do
  let cfg : IO.Process.SpawnArgs :=
    { cmd := cmd, args := args.toArray, stdin := .piped, stdout := .piped, stderr := .piped }
  let child ← IO.Process.spawn cfg
  let (stdinH, child) ← child.takeStdin
  if path == "-" then stdinH.write stdin
  stdinH.flush
  let errTask ← IO.asTask child.stderr.readToEnd
  let out ← child.stdout.readBinToEnd
  let code ← child.wait
  let err ← IO.ofExcept errTask.get
  if !err.isEmpty then IO.eprint err
  if code != 0 then
    return .error { message := s!"{path}: preprocessing failed ({cmd} exited with {code})", code := 1 }
  return .ok out

def cerberusPreprocessor : Preprocessor where
  kind := .cerberus
  command env r := some (env.cc, cerberusArgs env r)
  run env r := runExternal env.cc (cerberusArgs env r) r.stdin r.path

def systemPreprocessor : Preprocessor where
  kind := .system
  command env r := some (env.cc, systemArgs r)
  run env r := runExternal env.cc (systemArgs r) r.stdin r.path

def nonePreprocessor : Preprocessor where
  kind := .none
  command _ _ := none
  run _ r := do
    if r.path == "-" then return .ok r.stdin
    try return .ok (← IO.FS.readBinFile r.path)
    catch e => return .error (.usage s!"{r.path}: {e}")

/-- The slot of a preprocessor written in Lean: a pure `Options → (path → Option ByteArray) →
ByteArray → Except Diag ByteArray` (headers read through the lookup function), byte-exact against
`cpp`. Not implemented yet. -/
def leanPreprocessor : Preprocessor where
  kind := .lean
  command _ _ := none
  run _ r := return .error { message :=
    s!"{r.path}: --preprocessor=lean is not yet implemented (use system, cerberus or none)", code := 1 }

def Preprocessor.ofKind : PreprocessorKind → Preprocessor
  | .system => systemPreprocessor
  | .cerberus => cerberusPreprocessor
  | .none => nonePreprocessor
  | .lean => leanPreprocessor

/-! ## Checks -/

theorem preprocessorFor_i (o : Options) : o.preprocessorFor .preprocessed = .none := rfl

theorem preprocessorFor_default (k : InputKind) (h : k ≠ .preprocessed) :
    ({} : Options).preprocessorFor k = .cerberus := by
  simp [Options.preprocessorFor, h]

/-- `-D` and `-U` reach the preprocessor in command-line order. -/
theorem userArgs_macros (ms : List MacroOp) :
    userArgs { macros := ms } = ms.flatMap fun
      | .define m => ["-D", m]
      | .undef m => ["-U", m] := by
  simp [userArgs]

end Silmaril.Compile.Driver
