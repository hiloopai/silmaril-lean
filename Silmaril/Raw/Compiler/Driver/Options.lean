module

/-! # The command line of a C compiler, as data

This module is the beginning of a formal model of C compiler flags: the subset of the
gcc/clang command line that build tools use (`make`, autoconf probes, Rust's `cc`
crate, CMake), as a Lean structure `Options`, with

* a total parser `parseArgs : List String → Except Diag Options` (one argument list, after
  `@file` expansion, which `expandResponseFiles` models purely);
* a printer `Options.print : Options → List String`;
* the round trip `parseArgs_print : o.WF → parseArgs o.print = .ok o`, where `WF` is a
  decidable condition saying that each printed argument group reads back as itself (for
  example a warning payload `l,x` cannot round-trip: `-Wl,x` is a linker option, for gcc as
  well);
* the meaning of each option *as data*: the table `specs` gives, for every spelling, its
  argument form, the phase it affects (`Phase`: preprocessing, compilation, code generation,
  linking, diagnostics only, driver queries), how ccomp supports it (`Support`) and the gcc
  manual section that specifies it. Option families with open payloads (`-f…`, `-m…`, `-W…`,
  `-g…`) are classified by `fClass`, `mClass`, `wClass`.

gcc's behaviour is cited from the GCC 13 manual, chapter 3 "GCC Command Options"
(https://gcc.gnu.org/onlinedocs/gcc-13.3.0/gcc/Invoking-GCC.html): §3.2 Options Controlling the
Kind of Output, §3.4 Options Controlling C Dialect, §3.8 Options to Request or Suppress
Warnings, §3.10 Options for Debugging Your Program, §3.11 Options That Control Optimization,
§3.13 Options Controlling the Preprocessor, §3.14 Passing Options to the Assembler, §3.15
Options for Linking, §3.16 Options for Directory Search, §3.17 Options for Code Generation
Conventions, §3.18 GCC Developer Options, §3.19 Machine-Dependent Options (x86 Options). The
argument forms (joined, separate) follow gcc's option files (`gcc/c-family/c.opt`,
`gcc/common.opt`). `docs/CCompilerDriver.md` has the prose version and the ccomp-specific
choices.

## What is modelled exactly

* **Order.** `-D`/`-U` are kept in command-line order (`macros`): gcc processes them in
  order (§3.13 "‑D and ‑U options are processed in the order they are given"), so
  `-DX -UX` and `-UX -DX` differ. Directory options keep their order within each kind (§3.16:
  `-iquote`, then `-I`, then `-isystem`, then the standard directories, then `-idirafter`).
  `-include`/`-imacros` keep their order. Inputs, `-l` and `-Wl,` are interleaved in one list
  (`inputs`): a static link resolves archives in command-line order (§3.15 "It makes a
  difference where in the command you write this option").
* **Last one wins** for `-o`, `-O`, `-std=`, `-MF`, `--preprocessor=`, `--float=` (as in gcc;
  `-o` twice is an error in gcc 13 only for several outputs, which the driver checks).
* **Stop flags.** `-E`, `-S`, `-c` are three booleans and `Options.mode` takes the earliest
  stage (gcc: `-c -E` preprocesses). `-M`/`-MM` imply `-E` (§3.13).
* **`-x`** applies to the inputs after it until the next `-x` (§3.2); each input records the
  language in force (`Lang.none`: by file name suffix).
-/

@[expose] public section

namespace Silmaril.Compile.Driver

/-! ## Diagnostics -/

inductive Severity where
  | fatal
  | error
  | warning
  | note
  deriving DecidableEq, Repr

def Severity.name : Severity → String
  | .fatal => "fatal error"
  | .error => "error"
  | .warning => "warning"
  | .note => "note"

/-- A diagnostic of the driver or the compiler, with the exit status it implies when it is an
error: 1 a rejected or unsupported program, 2 a usage or I/O error, 3 an external tool failed. -/
structure Diag where
  severity : Severity := .error
  message : String
  code : UInt32 := 2
  deriving DecidableEq, Repr

/-- gcc's layout: `ccomp: error: unrecognized command-line option '-foo'`. -/
def Diag.render (d : Diag) (prog : String := "ccomp") : String :=
  s!"{prog}: {d.severity.name}: {d.message}"

def Diag.usage (msg : String) : Diag := { message := msg, code := 2 }
def Diag.reject (msg : String) : Diag := { message := msg, code := 1 }
def Diag.warn (msg : String) : Diag := { severity := .warning, message := msg }
def Diag.note (msg : String) : Diag := { severity := .note, message := msg }

/-! ## Enumerated payloads -/

/-- `-O…` (§3.11). `-O` alone is `-O1`; gcc reads `-O4` and above as `-O3`. -/
inductive OptLevel where
  | O0 | O1 | O2 | O3 | Os | Oz | Ofast | Og
  deriving DecidableEq, Repr

def OptLevel.payload : OptLevel → String
  | .O0 => "0" | .O1 => "1" | .O2 => "2" | .O3 => "3" | .Os => "s" | .Oz => "z"
  | .Ofast => "fast" | .Og => "g"

def OptLevel.ofPayload? (p : String) : Option OptLevel :=
  match p with
  | "" | "1" => some .O1
  | "0" => some .O0
  | "2" => some .O2
  | "3" => some .O3
  | "s" => some .Os
  | "z" => some .Oz
  | "fast" => some .Ofast
  | "g" => some .Og
  | _ => if !p.isEmpty && p.all Char.isDigit then some .O3 else none

theorem OptLevel.ofPayload_payload (l : OptLevel) : OptLevel.ofPayload? l.payload = some l := by
  cases l <;> rfl

/-- `-std=` (§3.4, "C Dialect Options", and §2 "Language Standards Supported by GCC"). Aliases
read as their canonical name: `c90`/`iso9899:1990` (and `-ansi`) as `c89`, `c9x`/`iso9899:1999`
as `c99`, `c1x`/`iso9899:2011` as `c11`, `c18`/`iso9899:2017`/`iso9899:2018` as `c17`, `c2x`
as `c23`, and the same for `gnu…`. -/
inductive Std where
  | c89 | c94 | c99 | c11 | c17 | c23 | c2y
  | gnu89 | gnu99 | gnu11 | gnu17 | gnu23 | gnu2y
  deriving DecidableEq, Repr

def Std.name : Std → String
  | .c89 => "c89" | .c94 => "iso9899:199409" | .c99 => "c99" | .c11 => "c11" | .c17 => "c17"
  | .c23 => "c23" | .c2y => "c2y" | .gnu89 => "gnu89" | .gnu99 => "gnu99" | .gnu11 => "gnu11"
  | .gnu17 => "gnu17" | .gnu23 => "gnu23" | .gnu2y => "gnu2y"

def Std.ofName? : String → Option Std
  | "c89" | "c90" | "iso9899:1990" => some .c89
  | "iso9899:199409" => some .c94
  | "c99" | "c9x" | "iso9899:1999" | "iso9899:199x" => some .c99
  | "c11" | "c1x" | "iso9899:2011" => some .c11
  | "c17" | "c18" | "iso9899:2017" | "iso9899:2018" => some .c17
  | "c23" | "c2x" | "iso9899:2024" => some .c23
  | "c2y" => some .c2y
  | "gnu89" | "gnu90" => some .gnu89
  | "gnu99" | "gnu9x" => some .gnu99
  | "gnu11" | "gnu1x" => some .gnu11
  | "gnu17" | "gnu18" => some .gnu17
  | "gnu23" | "gnu2x" => some .gnu23
  | "gnu2y" => some .gnu2y
  | _ => none

theorem Std.ofName_name (s : Std) : Std.ofName? s.name = some s := by cases s <;> rfl

/-- `-x LANG` (§3.2). `none` restores language detection by file name suffix. The C++,
Objective-C, Ada… languages of gcc are not recognized by ccomp. -/
inductive Lang where
  | none | c | cppOutput | cHeader | assembler | assemblerWithCpp
  deriving DecidableEq, Repr

def Lang.name : Lang → String
  | .none => "none" | .c => "c" | .cppOutput => "cpp-output" | .cHeader => "c-header"
  | .assembler => "assembler" | .assemblerWithCpp => "assembler-with-cpp"

def Lang.ofName? : String → Option Lang
  | "none" => some .none
  | "c" => some .c
  | "cpp-output" => some .cppOutput
  | "c-header" => some .cHeader
  | "assembler" => some .assembler
  | "assembler-with-cpp" => some .assemblerWithCpp
  | _ => none

theorem Lang.ofName_name (l : Lang) : Lang.ofName? l.name = some l := by cases l <;> rfl

/-- `--preprocessor=` (ccomp): which implementation produces the `.i` text
(`Silmaril.Compile.Driver.Preprocess`). -/
inductive PreprocessorKind where
  /-- the system `cc -E` with the system headers -/
  | system
  /-- the system `cc -E` with Cerberus's headers and builtins (`-nostdinc -undef -D__cerb__`) -/
  | cerberus
  /-- a preprocessor written in Lean (not yet implemented) -/
  | lean
  /-- the input is already preprocessed -/
  | none
  deriving DecidableEq, Repr

def PreprocessorKind.name : PreprocessorKind → String
  | .system => "system" | .cerberus => "cerberus" | .lean => "lean" | .none => "none"

def PreprocessorKind.ofName? : String → Option PreprocessorKind
  | "system" => some .system
  | "cerberus" => some .cerberus
  | "lean" => some .lean
  | "none" => some .none
  | _ => none

theorem PreprocessorKind.ofName_name (k : PreprocessorKind) :
    PreprocessorKind.ofName? k.name = some k := by cases k <;> rfl

/-- `--target` (ccomp; clang spells it `--target=`). -/
inductive Machine where
  | x86_64 | rv64
  deriving DecidableEq, Repr

def Machine.name : Machine → String
  | .x86_64 => "x86_64" | .rv64 => "rv64"

def Machine.ofName? : String → Option Machine
  | "x86_64" | "x86-64" | "x86" => some .x86_64
  | "rv64" | "riscv64" => some .rv64
  | _ => none

theorem Machine.ofName_name (m : Machine) : Machine.ofName? m.name = some m := by cases m <;> rfl

/-- `--float=` (ccomp): how floating-point operations are compiled. -/
inductive FloatMode where
  /-- Lir floating-point instructions and scalar SSE2 code (the unvalidated stage
  `Registry.Stage.x86Native`) -/
  | native
  /-- calls of the runtime library's soft-float routines, compiled by the proved Lir → x86
  chain (the default until `x86Native` is validated, ideas 576-578) -/
  | soft
  deriving DecidableEq, Repr

def FloatMode.name : FloatMode → String
  | .native => "native" | .soft => "soft"

def FloatMode.ofName? : String → Option FloatMode
  | "native" => some .native
  | "soft" => some .soft
  | _ => none

theorem FloatMode.ofName_name (m : FloatMode) : FloatMode.ofName? m.name = some m := by
  cases m <;> rfl

/-- The GNU triple `-dumpmachine` prints (what Ubuntu's gcc prints on the same machine). -/
def Machine.triple : Machine → String
  | .x86_64 => "x86_64-linux-gnu" | .rv64 => "riscv64-linux-gnu"

/-! ## The options -/

/-- Kinds of directory options (§3.16). Quoted includes search `quote`, then `angled`, then
`system`, then the standard directories, then `after`; angled includes start at `angled`. -/
inductive DirKind where
  | angled | quote | system | after
  deriving DecidableEq, Repr

/-- `-D NAME`, `-D NAME=VALUE`, `-D 'NAME(ARGS)=BODY'` (kept as written; `macroDefine` reads
it) and `-U NAME` (§3.13). -/
inductive MacroOp where
  | define (spec : String)
  | undef (name : String)
  deriving DecidableEq, Repr

/-- `-include FILE` and `-imacros FILE` (§3.13). -/
inductive ForcedKind where
  | include | imacros
  deriving DecidableEq, Repr

/-- What build tools ask the compiler without compiling (§3.2 `--version`, `--help`; §3.18
`-dumpversion`, `-dumpmachine`, `-print-…`). -/
inductive Query where
  | version | help | dumpversion | dumpfullversion | dumpmachine
  | printProgName (prog : String)
  | printFileName (file : String)
  | printSearchDirs | printLibgccFileName | printMultiOsDirectory | printMultiarch | printSysroot
  deriving DecidableEq, Repr

/-- A positional argument: a file (with the `-x` language in force, `-` is stdin), a library
`-lNAME`, or text for the linker (`-Wl,A,B`, `-Xlinker A`). -/
inductive Input where
  | file (path : String) (lang : Lang)
  | lib (name : String)
  | linkerCommas (payload : String)
  | linker (arg : String)
  deriving DecidableEq, Repr

/-- The options of one compiler invocation. List-valued fields keep command-line order. -/
structure Options where
  -- §3.2 overall
  stopE : Bool := false
  stopS : Bool := false
  stopC : Bool := false
  output : Option String := none
  inputs : List Input := []
  verbose : Bool := false
  dryRun : Bool := false
  pipe : Bool := false
  queries : List Query := []
  -- §3.13 preprocessor, §3.16 directories
  dirs : List (DirKind × String) := []
  macros : List MacroOp := []
  forced : List (ForcedKind × String) := []
  nostdinc : Bool := false
  undef : Bool := false
  noLineMarkers : Bool := false
  keepComments : Bool := false
  keepMacroComments : Bool := false
  dumps : List String := []
  cppPass : List String := []
  depM : Bool := false
  depMM : Bool := false
  depMD : Bool := false
  depMMD : Bool := false
  depMF : Option String := none
  depMT : List String := []
  depMQ : List String := []
  depMP : Bool := false
  depMG : Bool := false
  -- §3.4 dialect, §3.8 warnings
  std : Option Std := none
  warnings : List String := []
  noWarnings : Bool := false
  pedantic : Bool := false
  pedanticErrors : Bool := false
  -- §3.10 debugging, §3.11 optimization, §3.17 code generation, §3.19 machine
  debug : List String := []
  opt : Option OptLevel := none
  fflags : List String := []
  mflags : List String := []
  -- §3.14 assembler, §3.15 linking, §3.16 library directories
  asPass : List String := []
  libDirs : List String := []
  static : Bool := false
  shared : Bool := false
  pthread : Bool := false
  nostdlib : Bool := false
  nostartfiles : Bool := false
  nodefaultlibs : Bool := false
  rdynamic : Bool := false
  strip : Bool := false
  -- ccomp
  preprocessor : Option PreprocessorKind := none
  target : Option Machine := none
  float : Option FloatMode := none
  runtime : Option String := none
  ailFromOracle : Bool := false
  noLibc : Bool := false
  emitLir : Option String := none
  time : Bool := false
  permissive : Bool := false
  /-- unrecognized options accepted under `--ccomp-permissive` (each one warned about) -/
  unknown : List String := []
  deriving DecidableEq, Repr

/-! ## Recognized arguments -/

/-- One recognized argument group: what one option (with its argument) or one input means. -/
inductive Item where
  | stopE | stopS | stopC | output (f : String) | input (path : String) | lang (l : Lang)
  | lib (name : String) | linkerCommas (p : String) | linker (a : String)
  | verbose | dryRun | pipe | query (q : Query)
  | dir (k : DirKind) (d : String) | macro (m : MacroOp) | forced (k : ForcedKind) (f : String)
  | nostdinc | undef | noLineMarkers | keepComments | keepMacroComments | dump (p : String)
  | cppPass (p : String)
  | depM | depMM | depMD | depMMD | depMF (f : String) | depMT (t : String) | depMQ (t : String)
  | depMP | depMG
  | std (s : Std) | warning (w : String) | noWarnings | pedantic | pedanticErrors
  | debug (g : String) | opt (l : OptLevel) | fflag (f : String) | mflag (m : String)
  | asPass (p : String) | libDir (d : String)
  | static | shared | pthread | nostdlib | nostartfiles | nodefaultlibs | rdynamic | strip
  | preprocessor (k : PreprocessorKind) | target (m : Machine) | float (m : FloatMode)
  | runtime (d : String)
  | ailFromOracle | noLibc | emitLir (f : String) | time | permissive
  | unknown (a : String)
  deriving DecidableEq, Repr

/-- How an option takes its argument (gcc's `.opt` files): `flag` exactly as spelled;
`joined` the argument attached (`-Wall`, `-std=c11`, `-O2`; possibly empty: `-O`, `-g`);
`separate` the argument is the next word (`-include FILE`); `joinedOrSeparate` both
(`-I DIR`, `-IDIR`). -/
inductive Form where
  | flag | joined | separate | joinedOrSeparate
  deriving DecidableEq, Repr

/-- What an option affects. -/
inductive Phase where
  /-- how the driver runs: which stages, which outputs -/
  | driver
  /-- the preprocessed text (`.i`) -/
  | preprocess
  /-- the meaning of the program (dialect, implementation-defined choices) -/
  | compile
  /-- the generated code but not its meaning (optimization, debug information, PIC) -/
  | codegen
  /-- the link -/
  | link
  /-- which diagnostics are printed, never the output -/
  | diagnostics
  /-- prints information and exits -/
  | query
  deriving DecidableEq, Repr

/-- How ccomp supports an option. -/
inductive Support where
  /-- implemented with gcc's meaning -/
  | honoured
  /-- accepted, without effect; the note says why that is sound -/
  | ignored (note : String)
  /-- rejected with a diagnostic: honouring it would change the meaning of the program or
  produce something ccomp cannot produce -/
  | unsupported (why : String)
  deriving DecidableEq, Repr

/-- One row of the option table. -/
structure Spec where
  spelling : String
  form : Form
  phase : Phase
  support : Support
  /-- the gcc manual section, or "ccomp" -/
  gcc : String
  /-- the recognized item, from the argument (`""` for a flag) -/
  item : String → Except Diag Item
  doc : String

def badOpt (a : String) : Diag := .usage s!"unrecognized command-line option '{a}'"

/-- Shorthands for the table. -/
def Spec.flag (s : String) (ph : Phase) (sup : Support) (sec : String) (it : Item) (doc : String) :
    Spec := ⟨s, .flag, ph, sup, sec, fun _ => .ok it, doc⟩

def Spec.arg (s : String) (f : Form) (ph : Phase) (sup : Support) (sec : String)
    (it : String → Item) (doc : String) : Spec := ⟨s, f, ph, sup, sec, fun p => .ok (it p), doc⟩

def Spec.parsed (s : String) (f : Form) (ph : Phase) (sup : Support) (sec : String)
    (it : String → Except Diag Item) (doc : String) : Spec := ⟨s, f, ph, sup, sec, it, doc⟩

def ign (n : String) : Support := .ignored n
def uns (n : String) : Support := .unsupported n

def targetItem (p : String) : Except Diag Item :=
  match Machine.ofName? p with
  | some m => .ok (.target m)
  | none => .error (.usage s!"unknown target {p}")

open Phase Form in
/-- The option table, in matching order: the first row whose spelling matches an argument
wins, so longer spellings precede their prefixes (`-Wl,` before `-W`, `-dumpversion` before
`-d`). -/
def specs : List Spec := [
  -- §3.2 Options Controlling the Kind of Output
  .flag "-E" driver .honoured "3.2" .stopE "stop after preprocessing; the .i text goes to -o or stdout",
  .flag "-S" driver (uns "ccomp has no assembly output; use -c") "3.2" .stopS
    "stop after compilation proper, write assembly",
  .flag "-c" driver .honoured "3.2" .stopC
    "compile or assemble, do not link; ccomp objects are ELF files carrying the typed Ail (link-time compilation)",
  .arg "-o" joinedOrSeparate driver .honoured "3.2" .output "the output file",
  .parsed "-x" joinedOrSeparate driver .honoured "3.2" (fun p => match Lang.ofName? p with
      | some l => .ok (.lang l)
      | none => .error (.usage s!"language {p} not recognized")) "language of the following inputs",
  .flag "-v" query .honoured "3.2" .verbose "print the version and the commands run (to stderr)",
  .flag "-###" query .honoured "3.2" .dryRun "print the commands that would run, run nothing",
  .flag "-pipe" codegen (ign "ccomp keeps intermediate results in memory or a private directory") "3.2"
    .pipe "use pipes rather than temporary files",
  .flag "--version" query .honoured "3.2" (.query .version) "print the version",
  .flag "--help" query .honoured "3.2" (.query .help) "print a summary of the options",
  -- §3.18 GCC Developer Options (the probes of build tools)
  .flag "-dumpversion" query .honoured "3.18" (.query .dumpversion) "print the version number",
  .flag "-dumpfullversion" query .honoured "3.18" (.query .dumpfullversion) "print the full version number",
  .flag "-dumpmachine" query .honoured "3.18" (.query .dumpmachine) "print the target triple",
  .arg "-print-prog-name=" joined query .honoured "3.18" (.query ∘ .printProgName)
    "print the program the driver would run for PROG (as, ld, ar, cpp)",
  .arg "-print-file-name=" joined query .honoured "3.18" (.query ∘ .printFileName)
    "print the path of a library file, or the name itself if not found",
  .flag "-print-search-dirs" query .honoured "3.18" (.query .printSearchDirs)
    "print the installation, program and library directories",
  .flag "-print-libgcc-file-name" query .honoured "3.18" (.query .printLibgccFileName)
    "print the compiler support library (ccomp: its C runtime)",
  .flag "-print-multi-os-directory" query .honoured "3.18" (.query .printMultiOsDirectory)
    "print the OS library subdirectory",
  .flag "-print-multiarch" query .honoured "3.18" (.query .printMultiarch) "print the multiarch triple",
  .flag "-print-sysroot" query .honoured "3.18" (.query .printSysroot) "print the sysroot (empty)",
  -- §3.13 Options Controlling the Preprocessor, §3.16 Options for Directory Search
  .arg "-D" joinedOrSeparate preprocess .honoured "3.13" (.macro ∘ .define)
    "define a macro: NAME (as 1), NAME=VALUE, NAME(ARGS)=BODY; in order with -U",
  .arg "-U" joinedOrSeparate preprocess .honoured "3.13" (.macro ∘ .undef) "undefine a macro, in order with -D",
  .arg "-I" joinedOrSeparate preprocess .honoured "3.16" (.dir .angled) "add a directory for #include",
  .arg "-iquote" joinedOrSeparate preprocess .honoured "3.16" (.dir .quote)
    "add a directory for #include \"…\" only",
  .arg "-isystem" joinedOrSeparate preprocess .honoured "3.16" (.dir .system)
    "add a system directory (after -I, warnings suppressed)",
  .arg "-idirafter" joinedOrSeparate preprocess .honoured "3.16" (.dir .after)
    "add a directory searched after the standard ones",
  .arg "-include" joinedOrSeparate preprocess .honoured "3.13" (.forced .include)
    "process FILE as if #include \"FILE\" were its first line",
  .arg "-imacros" joinedOrSeparate preprocess .honoured "3.13" (.forced .imacros)
    "like -include but keep only the macros",
  .flag "-nostdinc" preprocess .honoured "3.16" .nostdinc "do not search the standard system directories",
  .flag "-undef" preprocess .honoured "3.13" .undef "do not predefine system- or GCC-specific macros",
  .flag "-P" preprocess .honoured "3.13" .noLineMarkers "no line markers in the -E output",
  .flag "-CC" preprocess .honoured "3.13" .keepMacroComments "keep comments, also inside macros",
  .flag "-C" preprocess .honoured "3.13" .keepComments "keep comments in the -E output",
  .arg "-Wp," joined preprocess .honoured "3.13" .cppPass "pass comma-separated options to the preprocessor",
  .flag "-M" preprocess .honoured "3.13" .depM "print a make rule of the dependencies instead of preprocessing (implies -E)",
  .flag "-MM" preprocess .honoured "3.13" .depMM "like -M, without system headers",
  .flag "-MD" preprocess .honoured "3.13" .depMD "write the dependencies to a .d file as a side effect",
  .flag "-MMD" preprocess .honoured "3.13" .depMMD "like -MD, without system headers",
  .arg "-MF" joinedOrSeparate preprocess .honoured "3.13" .depMF "the dependency file",
  .arg "-MT" joinedOrSeparate preprocess .honoured "3.13" .depMT "the target of the dependency rule",
  .arg "-MQ" joinedOrSeparate preprocess .honoured "3.13" .depMQ "the target, quoted for make",
  .flag "-MP" preprocess .honoured "3.13" .depMP "add a phony target for each header",
  .flag "-MG" preprocess .honoured "3.13" .depMG "treat missing headers as generated files",
  -- §3.4 Options Controlling C Dialect
  .parsed "-std=" joined compile .honoured "3.4" (fun p => match Std.ofName? p with
      | some v => .ok (.std v)
      | none => .error (badOpt s!"-std={p}")) "the language standard",
  .flag "-ansi" compile .honoured "3.4" (.std .c89) "-std=c90",
  -- §3.8 Options to Request or Suppress Warnings
  .flag "-pedantic-errors" diagnostics (ign "ccomp's frontend has no pedantic mode") "3.8"
    .pedanticErrors "errors for non-ISO constructs",
  .flag "-pedantic" diagnostics (ign "ccomp's frontend has no pedantic mode") "3.8" .pedantic
    "warnings for non-ISO constructs",
  .flag "-Wpedantic" diagnostics (ign "ccomp's frontend has no pedantic mode") "3.8" .pedantic "= -pedantic",
  .arg "-Wl," joined link .honoured "3.15" .linkerCommas "pass comma-separated options to the linker",
  .arg "-Wa," joined codegen (ign "ccomp does not run an assembler on C code") "3.14" .asPass
    "pass comma-separated options to the assembler",
  .arg "-W" joined diagnostics (ign "ccomp prints no warnings; see wClass") "3.8" .warning
    "enable or disable a warning (-Wall, -Wno-x, -Werror, -Werror=x)",
  .flag "-w" diagnostics .honoured "3.8" .noWarnings "suppress all warnings",
  -- §3.10, §3.11
  .arg "-g" joined codegen (ign "ccomp emits no debug information") "3.10" .debug
    "debug information (-g, -g0…3, -ggdb, -gdwarf-N)",
  .parsed "-O" joined codegen (ign "ccomp has one optimization level") "3.11"
    (fun p => match OptLevel.ofPayload? p with
      | some l => .ok (.opt l)
      | none => .error (.usage
          "argument to '-O' should be a non-negative integer, 'g', 's', 'z' or 'fast'"))
    "optimization level",
  -- §3.15 Options for Linking, §3.16
  .arg "-L" joinedOrSeparate link .honoured "3.16" .libDir "add a directory for -l",
  .arg "-l" joinedOrSeparate link .honoured "3.15" .lib "link libNAME.a (ccomp archives; see linkLibrary)",
  .arg "-Xlinker" separate link .honoured "3.15" .linker "pass one argument to the linker",
  .flag "-static" link (ign "ccomp executables are always static") "3.15" .static "link statically",
  .flag "-shared" link (uns "ccomp produces static executables only") "3.15" .shared "produce a shared object",
  .flag "-pthread" link .honoured "3.15" .pthread
    "POSIX threads: _REENTRANT for the system preprocessor; no library to link (ccomp programs are single-threaded)",
  .flag "-nostdlib" link .honoured "3.15" .nostdlib "no startup files, no default libraries (ccomp: --no-libc)",
  .flag "-nostartfiles" link (ign "ccomp's startup code is required by its linear-memory runtime") "3.15"
    .nostartfiles "no startup files",
  .flag "-nodefaultlibs" link .honoured "3.15" .nodefaultlibs "no default libraries (ccomp: --no-libc)",
  .flag "-rdynamic" link (ign "no dynamic symbol table in a static executable") "3.15" .rdynamic
    "export all symbols",
  .flag "-s" link (ign "ccomp executables carry no debug information") "3.15" .strip "strip the executable",
  -- §3.18 -d letters: macro dumps (after -dumpversion/-dumpmachine above)
  .arg "-d" joined preprocess .honoured "3.13" .dump
    "-dM (print the macros), -dD, -dN, -dI, -dU (with -E); other letters are developer dumps",
  -- §3.17, §3.19 (classified by fClass and mClass)
  .arg "-f" joined codegen (ign "see fClass") "3.17" .fflag "code generation conventions and language features",
  .arg "-m" joined codegen (ign "see mClass") "3.19" .mflag "machine options (-m64, -march=, -mtune=)",
  -- ccomp
  .parsed "--preprocessor=" joined preprocess .honoured "ccomp"
    (fun p => match PreprocessorKind.ofName? p with
      | some k => .ok (.preprocessor k)
      | none => .error (.usage s!"unknown preprocessor '{p}' (expected system, cerberus, lean or none)"))
    "which preprocessor: system, cerberus, lean, none",
  .parsed "--target=" joined compile .honoured "ccomp" targetItem "x86_64 or rv64",
  .parsed "--target" separate compile .honoured "ccomp" targetItem "x86_64 or rv64",
  .parsed "--float=" joined codegen .honoured "ccomp"
    (fun p => match FloatMode.ofName? p with
      | some m => .ok (.float m)
      | none => .error (.usage s!"unknown float mode '{p}' (expected native or soft)"))
    "floating point: soft (runtime routines, the proved chain; the default) or native (SSE2)",
  .arg "--runtime" separate link .honoured "ccomp" .runtime "the runtime directory (crt0, libc.c)",
  .flag "--ail-from-oracle" compile .honoured "ccomp" .ailFromOracle
    "take the typed Ail from Cerberus (cerb-oracle) until the Lean Cabs→Ail lands ",
  .flag "--no-libc" link .honoured "ccomp" .noLibc "do not link the C library libc.c",
  .arg "--emit-lir" separate driver .honoured "ccomp" .emitLir "write the linked Lir program to FILE",
  .flag "--time" driver .honoured "ccomp" .time "print the time of each stage",
  .flag "--ccomp-permissive" driver .honoured "ccomp" .permissive
    "warn about unrecognized options instead of rejecting them"
]

/-! ## Classification of the open option families -/

/-- `-f…` (§3.17 and the sections of each option). Options that would change the meaning of a
program are rejected, since ccomp implements one set of implementation-defined choices
(LP64, plain `char` signed, Cerberus's `Mem.Concrete` layouts). Unknown `-f` options are accepted
with a note, since there are hundreds and build tools probe many. -/
def fClass (f : String) : Phase × Support :=
  let f' := if f.startsWith "no-" then f.drop 3 |>.toString else f
  if f' ∈ ["unsigned-char", "signed-char", "short-enums", "short-wchar", "pack-struct",
      "unsigned-bitfields", "signed-bitfields", "trapv", "sanitize", "exec-charset",
      "wide-exec-charset", "input-charset"] || f'.startsWith "sanitize" || f'.startsWith "pack-struct="
      || f'.startsWith "exec-charset=" then
    if f == "signed-char" || f == "no-unsigned-char" || f == "signed-bitfields"
        || f == "no-trapv" || f.startsWith "no-sanitize" || f == "exec-charset=UTF-8"
        || f == "input-charset=UTF-8" then
      (.compile, .ignored "ccomp's choice already")
    else (.compile, .unsupported "it changes the meaning of the program, which ccomp does not model")
  else if f == "syntax-only" then (.driver, .unsupported "use -c (ccomp checks the whole unit)")
  else if f' ∈ ["PIC", "pic", "PIE", "pie"] then
    (.codegen, .ignored "ccomp code is position independent (it reaches memory through r15)")
  else if f' ∈ ["wrapv", "strict-aliasing", "strict-overflow", "common", "builtin", "freestanding",
      "hosted", "asm", "gnu89-inline", "ms-extensions", "plan9-extensions", "dollars-in-identifiers",
      "lax-vector-conversions", "openmp", "openacc", "cilkplus", "permissive"] then
    (.compile, .ignored "accepted; ccomp follows Cerberus's ISO C11 semantics, see docs/CCompilerDriver.md")
  else if f.startsWith "diagnostics" || f.startsWith "message-length" || f.startsWith "color"
      || f.startsWith "max-errors" || f == "show-column" || f == "no-show-column" then
    (.diagnostics, .ignored "diagnostics formatting")
  else (.codegen, .ignored "no effect on ccomp's output")

/-- `-m…` (§3.19, x86 Options). The x86-64 System V data model is the only one. -/
def mClass (m : String) : Phase × Support :=
  if m == "64" then (.codegen, .honoured)
  else if m ∈ ["32", "x32", "16"] then (.codegen, .unsupported "ccomp targets LP64 only")
  else if m.startsWith "arch=" || m.startsWith "tune=" || m.startsWith "cpu=" then
    (.codegen, .ignored "ccomp uses the base x86-64 instruction set")
  else if m.startsWith "abi=" && m != "abi=lp64" && m != "abi=sysv" then
    (.codegen, .unsupported "ccomp has one ABI")
  else (.codegen, .ignored "no effect on ccomp's output")

/-- `-W…` (§3.8): diagnostics only, except the pass-through forms matched earlier in `specs`.
`-Werror` would make warnings fatal; ccomp prints none. -/
def wClass (_w : String) : Phase × Support :=
  (.diagnostics, .ignored "ccomp prints no warnings")

/-! ## The parser -/

/-- What one argument starts: a complete item, or an option that needs the next argument. -/
inductive Step where
  | done (r : Except Diag Item)
  | needs (f : String → Except Diag Item)

/-- How one spec matches an argument (as characters): `some (some p)` with the payload `p`
(empty for a flag), `some none` when the argument is the spelling and the payload is the next
argument. -/
def matchSpec (a : List Char) (sp : Spec) : Option (Option (List Char)) :=
  let n := sp.spelling.toList
  match sp.form with
  | .flag => if a == n then some (some []) else none
  | .joined => if n.isPrefixOf a then some (some (a.drop n.length)) else none
  | .separate => if a == n then some none else none
  | .joinedOrSeparate =>
    if a == n then some none else if n.isPrefixOf a then some (some (a.drop n.length)) else none

/-- The first row of `specs` matching an argument, with its payload. -/
def lookup (a : String) : Option (Spec × Option String) :=
  specs.findSome? fun sp => (matchSpec a.toList sp).map fun p => (sp, p.map String.ofList)

/-- Inputs are the arguments that do not start with `-`, and `-` (stdin). -/
def isInput (a : String) : Bool := a == "-" || a.toList.head? != some '-'

def step (a : String) : Step :=
  if isInput a then .done (.ok (.input a)) else
  match lookup a with
  | some (sp, some p) => .done (sp.item p)
  | some (sp, none) => .needs sp.item
  | none => .done (.ok (.unknown a))

/-- The parser state: the options so far and the `-x` language in force. -/
structure PState where
  o : Options := {}
  lang : Lang := .none

/-- The effect of one item. -/
def applyPure (s : PState) : Item → PState
  | .stopE => { s with o.stopE := true }
  | .stopS => { s with o.stopS := true }
  | .stopC => { s with o.stopC := true }
  | .output f => { s with o.output := some f }
  | .input p => { s with o.inputs := s.o.inputs ++ [.file p s.lang] }
  | .lang l => { s with lang := l }
  | .lib n => { s with o.inputs := s.o.inputs ++ [.lib n] }
  | .linkerCommas p => { s with o.inputs := s.o.inputs ++ [.linkerCommas p] }
  | .linker a => { s with o.inputs := s.o.inputs ++ [.linker a] }
  | .verbose => { s with o.verbose := true }
  | .dryRun => { s with o.dryRun := true }
  | .pipe => { s with o.pipe := true }
  | .query q => { s with o.queries := s.o.queries ++ [q] }
  | .dir k d => { s with o.dirs := s.o.dirs ++ [(k, d)] }
  | .macro m => { s with o.macros := s.o.macros ++ [m] }
  | .forced k f => { s with o.forced := s.o.forced ++ [(k, f)] }
  | .nostdinc => { s with o.nostdinc := true }
  | .undef => { s with o.undef := true }
  | .noLineMarkers => { s with o.noLineMarkers := true }
  | .keepComments => { s with o.keepComments := true }
  | .keepMacroComments => { s with o.keepMacroComments := true }
  | .dump p => { s with o.dumps := s.o.dumps ++ [p] }
  | .cppPass p => { s with o.cppPass := s.o.cppPass ++ [p] }
  | .depM => { s with o.depM := true }
  | .depMM => { s with o.depMM := true }
  | .depMD => { s with o.depMD := true }
  | .depMMD => { s with o.depMMD := true }
  | .depMF f => { s with o.depMF := some f }
  | .depMT t => { s with o.depMT := s.o.depMT ++ [t] }
  | .depMQ t => { s with o.depMQ := s.o.depMQ ++ [t] }
  | .depMP => { s with o.depMP := true }
  | .depMG => { s with o.depMG := true }
  | .std v => { s with o.std := some v }
  | .warning w => { s with o.warnings := s.o.warnings ++ [w] }
  | .noWarnings => { s with o.noWarnings := true }
  | .pedantic => { s with o.pedantic := true }
  | .pedanticErrors => { s with o.pedanticErrors := true }
  | .debug g => { s with o.debug := s.o.debug ++ [g] }
  | .opt l => { s with o.opt := some l }
  | .fflag f => { s with o.fflags := s.o.fflags ++ [f] }
  | .mflag m => { s with o.mflags := s.o.mflags ++ [m] }
  | .asPass p => { s with o.asPass := s.o.asPass ++ [p] }
  | .libDir d => { s with o.libDirs := s.o.libDirs ++ [d] }
  | .static => { s with o.static := true }
  | .shared => { s with o.shared := true }
  | .pthread => { s with o.pthread := true }
  | .nostdlib => { s with o.nostdlib := true }
  | .nostartfiles => { s with o.nostartfiles := true }
  | .nodefaultlibs => { s with o.nodefaultlibs := true }
  | .rdynamic => { s with o.rdynamic := true }
  | .strip => { s with o.strip := true }
  | .preprocessor k => { s with o.preprocessor := some k }
  | .target m => { s with o.target := some m }
  | .float m => { s with o.float := some m }
  | .runtime d => { s with o.runtime := some d }
  | .ailFromOracle => { s with o.ailFromOracle := true }
  | .noLibc => { s with o.noLibc := true }
  | .emitLir f => { s with o.emitLir := some f }
  | .time => { s with o.time := true }
  | .permissive => { s with o.permissive := true }
  | .unknown a => { s with o.unknown := s.o.unknown ++ [a] }

/-- Unrecognized options are errors unless `--ccomp-permissive` is given (anywhere). -/
def applyItem (perm : Bool) (s : PState) (it : Item) : Except Diag PState :=
  match it with
  | .unknown a => if perm then .ok (applyPure s it) else .error (badOpt a)
  | _ => .ok (applyPure s it)

def missingArg (a : String) : Diag := .usage s!"missing argument to '{a}'"

/-- Read the arguments from left to right. -/
def parseLoop (perm : Bool) (s : PState) : List String → Except Diag PState
  | [] => .ok s
  | a :: rest =>
    match step a with
    | .done r => do parseLoop perm (← applyItem perm s (← r)) rest
    | .needs f =>
      match rest with
      | [] => .error (missingArg a)
      | b :: rest' => do parseLoop perm (← applyItem perm s (← f b)) rest'

/-- The command line (after `@file` expansion) as options. Total: every argument list gives
options or the first gcc-style diagnostic. -/
def parseArgs (args : List String) : Except Diag Options := do
  let s ← parseLoop (args.contains "--ccomp-permissive") {} args
  return s.o

/-! ## The printer -/

/-- The canonical arguments of one item: separate forms for options that take a separate
argument, joined forms otherwise. -/
def Item.print : Item → List String
  | .stopE => ["-E"] | .stopS => ["-S"] | .stopC => ["-c"]
  | .output f => ["-o", f]
  | .input p => [p]
  | .lang l => ["-x", l.name]
  | .lib n => ["-l", n]
  | .linkerCommas p => ["-Wl," ++ p]
  | .linker a => ["-Xlinker", a]
  | .verbose => ["-v"] | .dryRun => ["-###"] | .pipe => ["-pipe"]
  | .query .version => ["--version"]
  | .query .help => ["--help"]
  | .query .dumpversion => ["-dumpversion"]
  | .query .dumpfullversion => ["-dumpfullversion"]
  | .query .dumpmachine => ["-dumpmachine"]
  | .query (.printProgName p) => ["-print-prog-name=" ++ p]
  | .query (.printFileName p) => ["-print-file-name=" ++ p]
  | .query .printSearchDirs => ["-print-search-dirs"]
  | .query .printLibgccFileName => ["-print-libgcc-file-name"]
  | .query .printMultiOsDirectory => ["-print-multi-os-directory"]
  | .query .printMultiarch => ["-print-multiarch"]
  | .query .printSysroot => ["-print-sysroot"]
  | .dir .angled d => ["-I", d]
  | .dir .quote d => ["-iquote", d]
  | .dir .system d => ["-isystem", d]
  | .dir .after d => ["-idirafter", d]
  | .macro (.define m) => ["-D", m]
  | .macro (.undef m) => ["-U", m]
  | .forced .include f => ["-include", f]
  | .forced .imacros f => ["-imacros", f]
  | .nostdinc => ["-nostdinc"] | .undef => ["-undef"] | .noLineMarkers => ["-P"]
  | .keepComments => ["-C"] | .keepMacroComments => ["-CC"]
  | .dump p => ["-d" ++ p]
  | .cppPass p => ["-Wp," ++ p]
  | .depM => ["-M"] | .depMM => ["-MM"] | .depMD => ["-MD"] | .depMMD => ["-MMD"]
  | .depMF f => ["-MF", f] | .depMT t => ["-MT", t] | .depMQ t => ["-MQ", t]
  | .depMP => ["-MP"] | .depMG => ["-MG"]
  | .std v => ["-std=" ++ v.name]
  | .warning w => ["-W" ++ w]
  | .noWarnings => ["-w"] | .pedantic => ["-pedantic"] | .pedanticErrors => ["-pedantic-errors"]
  | .debug g => ["-g" ++ g]
  | .opt l => ["-O" ++ l.payload]
  | .fflag f => ["-f" ++ f]
  | .mflag m => ["-m" ++ m]
  | .asPass p => ["-Wa," ++ p]
  | .libDir d => ["-L", d]
  | .static => ["-static"] | .shared => ["-shared"] | .pthread => ["-pthread"]
  | .nostdlib => ["-nostdlib"] | .nostartfiles => ["-nostartfiles"]
  | .nodefaultlibs => ["-nodefaultlibs"] | .rdynamic => ["-rdynamic"] | .strip => ["-s"]
  | .preprocessor k => ["--preprocessor=" ++ k.name]
  | .target m => ["--target", m.name]
  | .float m => ["--float=" ++ m.name]
  | .runtime d => ["--runtime", d]
  | .ailFromOracle => ["--ail-from-oracle"] | .noLibc => ["--no-libc"]
  | .emitLir f => ["--emit-lir", f]
  | .time => ["--time"] | .permissive => ["--ccomp-permissive"]
  | .unknown a => [a]

def Input.items : Input → List Item
  | .file p l => [.lang l, .input p]
  | .lib n => [.lib n]
  | .linkerCommas p => [.linkerCommas p]
  | .linker a => [.linker a]

def flagItem (b : Bool) (it : Item) : List Item := if b then [it] else []

/-- The items after `--ccomp-permissive`. -/
def Options.itemsRest (o : Options) : List Item :=
  flagItem o.stopE .stopE ++ flagItem o.stopS .stopS ++ flagItem o.stopC .stopC ++
  (o.output.toList.map .output) ++ flagItem o.verbose .verbose ++ flagItem o.dryRun .dryRun ++
  flagItem o.pipe .pipe ++ (o.queries.map .query) ++
  (o.dirs.map fun (k, d) => .dir k d) ++ (o.macros.map .macro) ++
  (o.forced.map fun (k, f) => .forced k f) ++
  flagItem o.nostdinc .nostdinc ++ flagItem o.undef .undef ++
  flagItem o.noLineMarkers .noLineMarkers ++ flagItem o.keepComments .keepComments ++
  flagItem o.keepMacroComments .keepMacroComments ++ (o.dumps.map .dump) ++
  (o.cppPass.map .cppPass) ++
  flagItem o.depM .depM ++ flagItem o.depMM .depMM ++ flagItem o.depMD .depMD ++
  flagItem o.depMMD .depMMD ++ (o.depMF.toList.map .depMF) ++ (o.depMT.map .depMT) ++
  (o.depMQ.map .depMQ) ++ flagItem o.depMP .depMP ++ flagItem o.depMG .depMG ++
  (o.std.toList.map .std) ++ (o.warnings.map .warning) ++ flagItem o.noWarnings .noWarnings ++
  flagItem o.pedantic .pedantic ++ flagItem o.pedanticErrors .pedanticErrors ++
  (o.debug.map .debug) ++ (o.opt.toList.map .opt) ++ (o.fflags.map .fflag) ++
  (o.mflags.map .mflag) ++ (o.asPass.map .asPass) ++ (o.libDirs.map .libDir) ++
  flagItem o.static .static ++ flagItem o.shared .shared ++ flagItem o.pthread .pthread ++
  flagItem o.nostdlib .nostdlib ++ flagItem o.nostartfiles .nostartfiles ++
  flagItem o.nodefaultlibs .nodefaultlibs ++ flagItem o.rdynamic .rdynamic ++
  flagItem o.strip .strip ++
  (o.preprocessor.toList.map .preprocessor) ++ (o.target.toList.map .target) ++
  (o.float.toList.map .float) ++ (o.runtime.toList.map .runtime) ++ flagItem o.ailFromOracle .ailFromOracle ++
  flagItem o.noLibc .noLibc ++ (o.emitLir.toList.map .emitLir) ++ flagItem o.time .time ++
  (o.unknown.map .unknown) ++
  o.inputs.flatMap Input.items

/-- The items of a set of options, in a canonical order: `--ccomp-permissive` first (it changes
how the others are read), then each field. -/
def Options.items (o : Options) : List Item :=
  flagItem o.permissive .permissive ++ o.itemsRest

/-- A command line that `parseArgs` reads as `o` (under `o.WF`). -/
def Options.print (o : Options) : List String := o.items.flatMap Item.print

/-! ## The round trip -/

def Item.isUnknown : Item → Bool
  | .unknown _ => true
  | _ => false

/-- `it` reads back from its printed arguments. -/
def Item.reads (it : Item) : Bool :=
  match it.print with
  | [a] => match step a with
    | .done (.ok it') => it' == it
    | _ => false
  | [a, b] => match step a with
    | .needs f => match f b with
      | .ok it' => it' == it
      | .error _ => false
    | _ => false
  | _ => false

/-- The options print to arguments that read back: every item reads back, and unrecognized
options come with `--ccomp-permissive`. Decidable; `decide` or `#eval` checks it on concrete
options. The constant items always read back (`reads_const`): only payloads can fail, e.g. a
warning `l,x` (`-Wl,x` is a linker option) or an input path starting with `-`. -/
def Options.WF (o : Options) : Prop :=
  o.items.all (fun it => it.reads && (!it.isUnknown || o.permissive)) = true

instance (o : Options) : Decidable o.WF := by unfold Options.WF; infer_instance

theorem applyItem_of_ne_unknown (perm : Bool) (s : PState) (it : Item)
    (h : ∀ a, it ≠ .unknown a) : applyItem perm s it = .ok (applyPure s it) := by
  cases it <;> simp_all [applyItem]

theorem parseLoop_print_append (perm : Bool) (s : PState) (it : Item) (rest : List String)
    (h : it.reads = true) (hu : (∃ a, it = .unknown a) → perm = true) :
    parseLoop perm s (it.print ++ rest) = parseLoop perm (applyPure s it) rest := by
  have happ : applyItem perm s it = .ok (applyPure s it) := by
    by_cases hx : ∃ a, it = .unknown a
    · obtain ⟨a, rfl⟩ := hx
      simp [applyItem, hu ⟨a, rfl⟩]
    · exact applyItem_of_ne_unknown perm s it (fun a e => hx ⟨a, e⟩)
  unfold Item.reads at h
  split at h
  · rename_i a hp
    rw [hp]
    split at h
    · rename_i it' hs
      have : it' = it := by simpa using h
      subst this
      simp [parseLoop, hs, happ, bind, Except.bind]
    · simp at h
  · rename_i a b hp
    rw [hp]
    split at h
    · rename_i f hs
      split at h
      · rename_i it' hf
        have : it' = it := by simpa using h
        subst this
        simp [parseLoop, hs, hf, happ, bind, Except.bind]
      · simp at h
    · simp at h
  · simp at h

theorem parseLoop_items (perm : Bool) (s : PState) (items : List Item)
    (h : items.all (fun it => it.reads && (!it.isUnknown || perm)) = true) :
    parseLoop perm s (items.flatMap Item.print) = .ok (items.foldl applyPure s) := by
  induction items generalizing s with
  | nil => simp [parseLoop]
  | cons it items ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨⟨hr, hu⟩, h⟩ := h
    rw [List.flatMap_cons, parseLoop_print_append perm s it _ hr
      (fun ⟨a, e⟩ => by subst e; simpa [Item.isUnknown] using hu)]
    exact ih _ h

/-- The last-wins update of an optional field, by cases on the old value first (so that
`pick none x` is `x` by definition). -/
def pick {α : Type} : Option α → Option α → Option α
  | none, x => x
  | some a, x => match x with
    | some b => some b
    | none => some a

theorem pick_none {α : Type} (a : Option α) : pick a none = a := by cases a <;> rfl

theorem pick_some {α : Type} (a : Option α) (b : α) : pick a (some b) = some b := by
  cases a <;> rfl

theorem foldl_flagItem (s : PState) (b : Bool) (it : Item) :
    (flagItem b it).foldl applyPure s = if b then applyPure s it else s := by
  cases b <;> rfl

def upd_queries (xs : List Query) (s : PState) : PState := { s with o.queries := s.o.queries ++ xs }

theorem foldl_queries (xs : List Query) (s : PState) :
    (xs.map Item.query).foldl applyPure s = upd_queries xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_queries]

def upd_macros (xs : List MacroOp) (s : PState) : PState := { s with o.macros := s.o.macros ++ xs }

theorem foldl_macros (xs : List MacroOp) (s : PState) :
    (xs.map Item.macro).foldl applyPure s = upd_macros xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_macros]

def upd_dumps (xs : List String) (s : PState) : PState := { s with o.dumps := s.o.dumps ++ xs }

theorem foldl_dumps (xs : List String) (s : PState) :
    (xs.map Item.dump).foldl applyPure s = upd_dumps xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_dumps]

def upd_cppPass (xs : List String) (s : PState) : PState := { s with o.cppPass := s.o.cppPass ++ xs }

theorem foldl_cppPass (xs : List String) (s : PState) :
    (xs.map Item.cppPass).foldl applyPure s = upd_cppPass xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_cppPass]

def upd_depMT (xs : List String) (s : PState) : PState := { s with o.depMT := s.o.depMT ++ xs }

theorem foldl_depMT (xs : List String) (s : PState) :
    (xs.map Item.depMT).foldl applyPure s = upd_depMT xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_depMT]

def upd_depMQ (xs : List String) (s : PState) : PState := { s with o.depMQ := s.o.depMQ ++ xs }

theorem foldl_depMQ (xs : List String) (s : PState) :
    (xs.map Item.depMQ).foldl applyPure s = upd_depMQ xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_depMQ]

def upd_warnings (xs : List String) (s : PState) : PState := { s with o.warnings := s.o.warnings ++ xs }

theorem foldl_warnings (xs : List String) (s : PState) :
    (xs.map Item.warning).foldl applyPure s = upd_warnings xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_warnings]

def upd_debug (xs : List String) (s : PState) : PState := { s with o.debug := s.o.debug ++ xs }

theorem foldl_debug (xs : List String) (s : PState) :
    (xs.map Item.debug).foldl applyPure s = upd_debug xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_debug]

def upd_fflags (xs : List String) (s : PState) : PState := { s with o.fflags := s.o.fflags ++ xs }

theorem foldl_fflags (xs : List String) (s : PState) :
    (xs.map Item.fflag).foldl applyPure s = upd_fflags xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_fflags]

def upd_mflags (xs : List String) (s : PState) : PState := { s with o.mflags := s.o.mflags ++ xs }

theorem foldl_mflags (xs : List String) (s : PState) :
    (xs.map Item.mflag).foldl applyPure s = upd_mflags xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_mflags]

def upd_asPass (xs : List String) (s : PState) : PState := { s with o.asPass := s.o.asPass ++ xs }

theorem foldl_asPass (xs : List String) (s : PState) :
    (xs.map Item.asPass).foldl applyPure s = upd_asPass xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_asPass]

def upd_libDirs (xs : List String) (s : PState) : PState := { s with o.libDirs := s.o.libDirs ++ xs }

theorem foldl_libDirs (xs : List String) (s : PState) :
    (xs.map Item.libDir).foldl applyPure s = upd_libDirs xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_libDirs]

def upd_unknown (xs : List String) (s : PState) : PState := { s with o.unknown := s.o.unknown ++ xs }

theorem foldl_unknown (xs : List String) (s : PState) :
    (xs.map Item.unknown).foldl applyPure s = upd_unknown xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_unknown]

def upd_dirs (xs : List (DirKind × String)) (s : PState) : PState := { s with o.dirs := s.o.dirs ++ xs }

theorem foldl_dirs (xs : List (DirKind × String)) (s : PState) :
    (xs.map fun (k, d) => Item.dir k d).foldl applyPure s = upd_dirs xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_dirs]

def upd_forced (xs : List (ForcedKind × String)) (s : PState) : PState := { s with o.forced := s.o.forced ++ xs }

theorem foldl_forced (xs : List (ForcedKind × String)) (s : PState) :
    (xs.map fun (k, f) => Item.forced k f).foldl applyPure s = upd_forced xs s := by
  induction xs generalizing s <;> simp_all [applyPure, upd_forced]

/-- The `-x` language after a list of inputs. -/
def lastLang (l : Lang) : List Input → Lang
  | [] => l
  | .file _ l' :: is => lastLang l' is
  | _ :: is => lastLang l is

def upd_inputs (xs : List Input) (s : PState) : PState :=
  { o := { s.o with inputs := s.o.inputs ++ xs }, lang := lastLang s.lang xs }

theorem foldl_inputs (xs : List Input) (s : PState) :
    (xs.flatMap Input.items).foldl applyPure s = upd_inputs xs s := by
  induction xs generalizing s with
  | nil => simp [lastLang, upd_inputs]
  | cons x xs ih =>
    cases x <;> simp_all [Input.items, applyPure, lastLang, upd_inputs]

def upd_stopE (b : Bool) (s : PState) : PState := { s with o.stopE := s.o.stopE || b }

theorem foldl_stopE (b : Bool) (s : PState) :
    (flagItem b Item.stopE).foldl applyPure s = upd_stopE b s := by
  cases b <;> simp [flagItem, applyPure, upd_stopE]

def upd_stopS (b : Bool) (s : PState) : PState := { s with o.stopS := s.o.stopS || b }

theorem foldl_stopS (b : Bool) (s : PState) :
    (flagItem b Item.stopS).foldl applyPure s = upd_stopS b s := by
  cases b <;> simp [flagItem, applyPure, upd_stopS]

def upd_stopC (b : Bool) (s : PState) : PState := { s with o.stopC := s.o.stopC || b }

theorem foldl_stopC (b : Bool) (s : PState) :
    (flagItem b Item.stopC).foldl applyPure s = upd_stopC b s := by
  cases b <;> simp [flagItem, applyPure, upd_stopC]

def upd_verbose (b : Bool) (s : PState) : PState := { s with o.verbose := s.o.verbose || b }

theorem foldl_verbose (b : Bool) (s : PState) :
    (flagItem b Item.verbose).foldl applyPure s = upd_verbose b s := by
  cases b <;> simp [flagItem, applyPure, upd_verbose]

def upd_dryRun (b : Bool) (s : PState) : PState := { s with o.dryRun := s.o.dryRun || b }

theorem foldl_dryRun (b : Bool) (s : PState) :
    (flagItem b Item.dryRun).foldl applyPure s = upd_dryRun b s := by
  cases b <;> simp [flagItem, applyPure, upd_dryRun]

def upd_pipe (b : Bool) (s : PState) : PState := { s with o.pipe := s.o.pipe || b }

theorem foldl_pipe (b : Bool) (s : PState) :
    (flagItem b Item.pipe).foldl applyPure s = upd_pipe b s := by
  cases b <;> simp [flagItem, applyPure, upd_pipe]

def upd_nostdinc (b : Bool) (s : PState) : PState := { s with o.nostdinc := s.o.nostdinc || b }

theorem foldl_nostdinc (b : Bool) (s : PState) :
    (flagItem b Item.nostdinc).foldl applyPure s = upd_nostdinc b s := by
  cases b <;> simp [flagItem, applyPure, upd_nostdinc]

def upd_undef (b : Bool) (s : PState) : PState := { s with o.undef := s.o.undef || b }

theorem foldl_undef (b : Bool) (s : PState) :
    (flagItem b Item.undef).foldl applyPure s = upd_undef b s := by
  cases b <;> simp [flagItem, applyPure, upd_undef]

def upd_noLineMarkers (b : Bool) (s : PState) : PState := { s with o.noLineMarkers := s.o.noLineMarkers || b }

theorem foldl_noLineMarkers (b : Bool) (s : PState) :
    (flagItem b Item.noLineMarkers).foldl applyPure s = upd_noLineMarkers b s := by
  cases b <;> simp [flagItem, applyPure, upd_noLineMarkers]

def upd_keepComments (b : Bool) (s : PState) : PState := { s with o.keepComments := s.o.keepComments || b }

theorem foldl_keepComments (b : Bool) (s : PState) :
    (flagItem b Item.keepComments).foldl applyPure s = upd_keepComments b s := by
  cases b <;> simp [flagItem, applyPure, upd_keepComments]

def upd_keepMacroComments (b : Bool) (s : PState) : PState := { s with o.keepMacroComments := s.o.keepMacroComments || b }

theorem foldl_keepMacroComments (b : Bool) (s : PState) :
    (flagItem b Item.keepMacroComments).foldl applyPure s = upd_keepMacroComments b s := by
  cases b <;> simp [flagItem, applyPure, upd_keepMacroComments]

def upd_depM (b : Bool) (s : PState) : PState := { s with o.depM := s.o.depM || b }

theorem foldl_depM (b : Bool) (s : PState) :
    (flagItem b Item.depM).foldl applyPure s = upd_depM b s := by
  cases b <;> simp [flagItem, applyPure, upd_depM]

def upd_depMM (b : Bool) (s : PState) : PState := { s with o.depMM := s.o.depMM || b }

theorem foldl_depMM (b : Bool) (s : PState) :
    (flagItem b Item.depMM).foldl applyPure s = upd_depMM b s := by
  cases b <;> simp [flagItem, applyPure, upd_depMM]

def upd_depMD (b : Bool) (s : PState) : PState := { s with o.depMD := s.o.depMD || b }

theorem foldl_depMD (b : Bool) (s : PState) :
    (flagItem b Item.depMD).foldl applyPure s = upd_depMD b s := by
  cases b <;> simp [flagItem, applyPure, upd_depMD]

def upd_depMMD (b : Bool) (s : PState) : PState := { s with o.depMMD := s.o.depMMD || b }

theorem foldl_depMMD (b : Bool) (s : PState) :
    (flagItem b Item.depMMD).foldl applyPure s = upd_depMMD b s := by
  cases b <;> simp [flagItem, applyPure, upd_depMMD]

def upd_depMP (b : Bool) (s : PState) : PState := { s with o.depMP := s.o.depMP || b }

theorem foldl_depMP (b : Bool) (s : PState) :
    (flagItem b Item.depMP).foldl applyPure s = upd_depMP b s := by
  cases b <;> simp [flagItem, applyPure, upd_depMP]

def upd_depMG (b : Bool) (s : PState) : PState := { s with o.depMG := s.o.depMG || b }

theorem foldl_depMG (b : Bool) (s : PState) :
    (flagItem b Item.depMG).foldl applyPure s = upd_depMG b s := by
  cases b <;> simp [flagItem, applyPure, upd_depMG]

def upd_noWarnings (b : Bool) (s : PState) : PState := { s with o.noWarnings := s.o.noWarnings || b }

theorem foldl_noWarnings (b : Bool) (s : PState) :
    (flagItem b Item.noWarnings).foldl applyPure s = upd_noWarnings b s := by
  cases b <;> simp [flagItem, applyPure, upd_noWarnings]

def upd_pedantic (b : Bool) (s : PState) : PState := { s with o.pedantic := s.o.pedantic || b }

theorem foldl_pedantic (b : Bool) (s : PState) :
    (flagItem b Item.pedantic).foldl applyPure s = upd_pedantic b s := by
  cases b <;> simp [flagItem, applyPure, upd_pedantic]

def upd_pedanticErrors (b : Bool) (s : PState) : PState := { s with o.pedanticErrors := s.o.pedanticErrors || b }

theorem foldl_pedanticErrors (b : Bool) (s : PState) :
    (flagItem b Item.pedanticErrors).foldl applyPure s = upd_pedanticErrors b s := by
  cases b <;> simp [flagItem, applyPure, upd_pedanticErrors]

def upd_static (b : Bool) (s : PState) : PState := { s with o.static := s.o.static || b }

theorem foldl_static (b : Bool) (s : PState) :
    (flagItem b Item.static).foldl applyPure s = upd_static b s := by
  cases b <;> simp [flagItem, applyPure, upd_static]

def upd_shared (b : Bool) (s : PState) : PState := { s with o.shared := s.o.shared || b }

theorem foldl_shared (b : Bool) (s : PState) :
    (flagItem b Item.shared).foldl applyPure s = upd_shared b s := by
  cases b <;> simp [flagItem, applyPure, upd_shared]

def upd_pthread (b : Bool) (s : PState) : PState := { s with o.pthread := s.o.pthread || b }

theorem foldl_pthread (b : Bool) (s : PState) :
    (flagItem b Item.pthread).foldl applyPure s = upd_pthread b s := by
  cases b <;> simp [flagItem, applyPure, upd_pthread]

def upd_nostdlib (b : Bool) (s : PState) : PState := { s with o.nostdlib := s.o.nostdlib || b }

theorem foldl_nostdlib (b : Bool) (s : PState) :
    (flagItem b Item.nostdlib).foldl applyPure s = upd_nostdlib b s := by
  cases b <;> simp [flagItem, applyPure, upd_nostdlib]

def upd_nostartfiles (b : Bool) (s : PState) : PState := { s with o.nostartfiles := s.o.nostartfiles || b }

theorem foldl_nostartfiles (b : Bool) (s : PState) :
    (flagItem b Item.nostartfiles).foldl applyPure s = upd_nostartfiles b s := by
  cases b <;> simp [flagItem, applyPure, upd_nostartfiles]

def upd_nodefaultlibs (b : Bool) (s : PState) : PState := { s with o.nodefaultlibs := s.o.nodefaultlibs || b }

theorem foldl_nodefaultlibs (b : Bool) (s : PState) :
    (flagItem b Item.nodefaultlibs).foldl applyPure s = upd_nodefaultlibs b s := by
  cases b <;> simp [flagItem, applyPure, upd_nodefaultlibs]

def upd_rdynamic (b : Bool) (s : PState) : PState := { s with o.rdynamic := s.o.rdynamic || b }

theorem foldl_rdynamic (b : Bool) (s : PState) :
    (flagItem b Item.rdynamic).foldl applyPure s = upd_rdynamic b s := by
  cases b <;> simp [flagItem, applyPure, upd_rdynamic]

def upd_strip (b : Bool) (s : PState) : PState := { s with o.strip := s.o.strip || b }

theorem foldl_strip (b : Bool) (s : PState) :
    (flagItem b Item.strip).foldl applyPure s = upd_strip b s := by
  cases b <;> simp [flagItem, applyPure, upd_strip]

def upd_ailFromOracle (b : Bool) (s : PState) : PState := { s with o.ailFromOracle := s.o.ailFromOracle || b }

theorem foldl_ailFromOracle (b : Bool) (s : PState) :
    (flagItem b Item.ailFromOracle).foldl applyPure s = upd_ailFromOracle b s := by
  cases b <;> simp [flagItem, applyPure, upd_ailFromOracle]

def upd_noLibc (b : Bool) (s : PState) : PState := { s with o.noLibc := s.o.noLibc || b }

theorem foldl_noLibc (b : Bool) (s : PState) :
    (flagItem b Item.noLibc).foldl applyPure s = upd_noLibc b s := by
  cases b <;> simp [flagItem, applyPure, upd_noLibc]

def upd_time (b : Bool) (s : PState) : PState := { s with o.time := s.o.time || b }

theorem foldl_time (b : Bool) (s : PState) :
    (flagItem b Item.time).foldl applyPure s = upd_time b s := by
  cases b <;> simp [flagItem, applyPure, upd_time]

def upd_permissive (b : Bool) (s : PState) : PState := { s with o.permissive := s.o.permissive || b }

theorem foldl_permissive (b : Bool) (s : PState) :
    (flagItem b Item.permissive).foldl applyPure s = upd_permissive b s := by
  cases b <;> simp [flagItem, applyPure, upd_permissive]

def upd_output (x : Option String) (s : PState) : PState := { s with o.output := pick s.o.output x }

theorem foldl_output (x : Option String) (s : PState) :
    (x.toList.map Item.output).foldl applyPure s = upd_output x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_output, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_output, pick_some]; rfl

def upd_depMF (x : Option String) (s : PState) : PState := { s with o.depMF := pick s.o.depMF x }

theorem foldl_depMF (x : Option String) (s : PState) :
    (x.toList.map Item.depMF).foldl applyPure s = upd_depMF x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_depMF, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_depMF, pick_some]; rfl

def upd_std (x : Option Std) (s : PState) : PState := { s with o.std := pick s.o.std x }

theorem foldl_std (x : Option Std) (s : PState) :
    (x.toList.map Item.std).foldl applyPure s = upd_std x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_std, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_std, pick_some]; rfl

def upd_opt (x : Option OptLevel) (s : PState) : PState := { s with o.opt := pick s.o.opt x }

theorem foldl_opt (x : Option OptLevel) (s : PState) :
    (x.toList.map Item.opt).foldl applyPure s = upd_opt x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_opt, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_opt, pick_some]; rfl

def upd_preprocessor (x : Option PreprocessorKind) (s : PState) : PState := { s with o.preprocessor := pick s.o.preprocessor x }

theorem foldl_preprocessor (x : Option PreprocessorKind) (s : PState) :
    (x.toList.map Item.preprocessor).foldl applyPure s = upd_preprocessor x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_preprocessor, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_preprocessor, pick_some]; rfl

def upd_target (x : Option Machine) (s : PState) : PState := { s with o.target := pick s.o.target x }

theorem foldl_target (x : Option Machine) (s : PState) :
    (x.toList.map Item.target).foldl applyPure s = upd_target x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_target, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_target, pick_some]; rfl

def upd_float (x : Option FloatMode) (s : PState) : PState := { s with o.float := pick s.o.float x }

theorem foldl_float (x : Option FloatMode) (s : PState) :
    (x.toList.map Item.float).foldl applyPure s = upd_float x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_float, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_float, pick_some]; rfl

def upd_runtime (x : Option String) (s : PState) : PState := { s with o.runtime := pick s.o.runtime x }

theorem foldl_runtime (x : Option String) (s : PState) :
    (x.toList.map Item.runtime).foldl applyPure s = upd_runtime x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_runtime, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_runtime, pick_some]; rfl

def upd_emitLir (x : Option String) (s : PState) : PState := { s with o.emitLir := pick s.o.emitLir x }

theorem foldl_emitLir (x : Option String) (s : PState) :
    (x.toList.map Item.emitLir).foldl applyPure s = upd_emitLir x s := by
  cases x with
  | none => simp only [Option.toList, List.map, List.foldl, upd_emitLir, pick_none]
  | some v => simp only [Option.toList, List.map, List.foldl, upd_emitLir, pick_some]; rfl

set_option maxRecDepth 20000 in
theorem items_foldl (o : Options) : (o.items.foldl applyPure {}).o = o := by
  unfold Options.items Options.itemsRest
  simp only [List.foldl_append, foldl_queries, foldl_macros, foldl_dumps, foldl_cppPass, foldl_depMT, foldl_depMQ, foldl_warnings, foldl_debug, foldl_fflags, foldl_mflags, foldl_asPass, foldl_libDirs, foldl_unknown, foldl_dirs, foldl_forced, foldl_inputs, foldl_stopE, foldl_stopS, foldl_stopC, foldl_verbose, foldl_dryRun, foldl_pipe, foldl_nostdinc, foldl_undef, foldl_noLineMarkers, foldl_keepComments, foldl_keepMacroComments, foldl_depM, foldl_depMM, foldl_depMD, foldl_depMMD, foldl_depMP, foldl_depMG, foldl_noWarnings, foldl_pedantic, foldl_pedanticErrors, foldl_static, foldl_shared, foldl_pthread, foldl_nostdlib, foldl_nostartfiles, foldl_nodefaultlibs, foldl_rdynamic, foldl_strip, foldl_ailFromOracle, foldl_noLibc, foldl_time, foldl_permissive, foldl_output, foldl_depMF, foldl_std, foldl_opt, foldl_preprocessor, foldl_target, foldl_float, foldl_runtime, foldl_emitLir]
  simp only [upd_queries, upd_macros, upd_dumps, upd_cppPass, upd_depMT, upd_depMQ, upd_warnings, upd_debug, upd_fflags, upd_mflags, upd_asPass, upd_libDirs, upd_unknown, upd_dirs, upd_forced, upd_inputs, upd_stopE, upd_stopS, upd_stopC, upd_verbose, upd_dryRun, upd_pipe, upd_nostdinc, upd_undef, upd_noLineMarkers, upd_keepComments, upd_keepMacroComments, upd_depM, upd_depMM, upd_depMD, upd_depMMD, upd_depMP, upd_depMG, upd_noWarnings, upd_pedantic, upd_pedanticErrors, upd_static, upd_shared, upd_pthread, upd_nostdlib, upd_nostartfiles, upd_nodefaultlibs, upd_rdynamic, upd_strip, upd_ailFromOracle, upd_noLibc, upd_time, upd_permissive, upd_output, upd_depMF, upd_std, upd_opt, upd_preprocessor, upd_target, upd_float, upd_runtime, upd_emitLir, pick, Bool.false_or, List.nil_append]

theorem print_contains_permissive (o : Options) (hp : o.permissive = true) :
    o.print.contains "--ccomp-permissive" = true := by
  rw [Options.print, Options.items, hp]
  simp [flagItem, Item.print]

/-- **Round trip.** Printing well-formed options and parsing the result gives them back. -/
theorem parseArgs_print (o : Options) (h : o.WF) : parseArgs o.print = .ok o := by
  unfold parseArgs
  have h' : o.items.all (fun it => it.reads &&
      (!it.isUnknown || o.print.contains "--ccomp-permissive")) = true := by
    simp only [Options.WF, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    intro it m
    obtain ⟨hr, hu⟩ := h it m
    exact ⟨hr, hu.imp_right (print_contains_permissive o)⟩
  rw [show o.print = o.items.flatMap Item.print from rfl] at h' ⊢
  rw [parseLoop_items _ _ _ h']
  simp only [bind, Except.bind, pure, Except.pure, items_foldl]

/-! ## Response files (§3.2 `@file`)

gcc reads `@FILE` as the whitespace-separated arguments in FILE, with `'…'` and `"…"`
grouping and `\` escaping the next character (libiberty's `buildargv`); an `@FILE` that cannot
be read stays a literal argument; response files may nest. -/

/-- The arguments of a response file. -/
def responseTokens (text : String) : List String :=
  let rec go : List Char → List Char → Bool → Bool → Bool → Bool → List String → List String
    -- input, current word (reversed), in a word, backslash, single quote, double quote, out (reversed)
    | [], cur, inWord, _, _, _, out => (if inWord then String.ofList cur.reverse :: out else out).reverse
    | c :: cs, cur, inWord, bs, sq, dq, out =>
      if bs then go cs (c :: cur) true false sq dq out
      else if c == '\\' then go cs cur true true sq dq out
      else if sq then (if c == '\'' then go cs cur true false false dq out else go cs (c :: cur) true false sq dq out)
      else if dq then (if c == '"' then go cs cur true false sq false out else go cs (c :: cur) true false sq dq out)
      else if c == '\'' then go cs cur true false true dq out
      else if c == '"' then go cs cur true false sq true out
      else if c.isWhitespace then
        (if inWord then go cs [] false false false false (String.ofList cur.reverse :: out)
         else go cs [] false false false false out)
      else go cs (c :: cur) true false sq dq out
  go text.toList [] false false false false []

/-- Expand `@FILE` arguments with `read` (which gives a file's text, if it can be read), at most
`depth` levels deep (libiberty stops at 2000). -/
def expandResponseFiles {m : Type → Type} [Monad m] (read : String → m (Option String)) :
    Nat → List String → m (List String)
  | 0, args => pure args
  | depth + 1, args => do
    let mut out := []
    for a in args do
      if a.startsWith "@" && a.length > 1 then
        match ← read (a.drop 1).toString with
        | some text => out := out ++ (← expandResponseFiles read depth (responseTokens text))
        | none => out := out ++ [a]
      else out := out ++ [a]
    return out

/-! ## What the options mean -/

/-- The last stage that runs (§3.2 "Overall Options"). -/
inductive Mode where
  | preprocess | assemble | compile | link
  deriving DecidableEq, Repr

/-- gcc stops at the earliest stage requested: `-E` (or `-M`/`-MM`), then `-S`, then `-c`. -/
def Options.mode (o : Options) : Mode :=
  if o.stopE || o.depM || o.depMM then .preprocess
  else if o.stopS then .assemble
  else if o.stopC then .compile
  else .link

/-- Native floating point (`--float=native`); soft-float, the default, keeps the proved
Lir → x86 chain until `x86Native` is validated (ideas 576-578). -/
def Options.nativeFloat (o : Options) : Bool := o.float == some .native

/-- How an input file is processed (§3.2: the suffix rules, overridden by `-x`). -/
inductive InputKind where
  /-- C source: preprocess, then compile -/
  | c
  /-- preprocessed C (`.i`): compile -/
  | preprocessed
  /-- a typed-Ail document (`cerb-oracle --level tail`; ccomp only) -/
  | ail
  | header | asm | asmCpp
  /-- an object, archive or anything else: passed to the link -/
  | linkInput
  deriving DecidableEq, Repr

def basename (p : String) : String := (p.splitOn "/").getLast?.getD p

/-- The suffix of a file name (after the last dot of its last component), if any. -/
def suffix (p : String) : Option String :=
  match (basename p).splitOn "." with
  | [] | [_] => none
  | xs => xs.getLast?

/-- The file name without its suffix: `dir/a.b.c` → `dir/a.b`. -/
def dropSuffix (p : String) : String :=
  match suffix p with
  | some x => (p.dropEnd (x.length + 1)).toString
  | none => p

/-- The last component without its suffix: `dir/a.b.c` → `a.b`. -/
def stem (p : String) : String := basename (dropSuffix p)

/-- The kind of an input: by `-x`, else by suffix; stdin (`-`) without `-x` is C (gcc accepts it
only with `-E`, which the driver checks). -/
def InputKind.ofFile (path : String) (l : Lang) : InputKind :=
  match l with
  | .c => .c
  | .cppOutput => .preprocessed
  | .cHeader => .header
  | .assembler => .asm
  | .assemblerWithCpp => .asmCpp
  | .none => if path == "-" then .c else match suffix path with
    | some "c" => .c
    | some "i" => .preprocessed
    | some "h" => .header
    | some "s" => .asm
    | some "S" | some "sx" => .asmCpp
    | some "ail" | some "sexp" => .ail
    | _ => .linkInput

/-- `-D` as a definition: `NAME` defines `NAME` as `1`, `NAME=VALUE` as `VALUE` (§3.13). -/
def macroDefine (spec : String) : String × String :=
  match spec.splitOn "=" with
  | [n] => (n, "1")
  | n :: rest => (n, "=".intercalate rest)
  | [] => (spec, "1")

/-- The output of a compilation without `-o` (§3.2 `-o`): `SOURCE.o` in the current directory
for `-c`, `a.out` for a link, stdout for `-E`. -/
def objectName (o : Options) (input : String) : String :=
  match o.mode, o.output with
  | .compile, some f => f
  | _, _ => stem input ++ ".o"

/-- The dependency output of `-MD`/`-MMD` (§3.13): the file (from `-MF`, else the object name
with `.d`, the object being `-o` with `-c`, else `STEM.d` in the current directory), the targets
(`-MT`, `-MQ`, else the object name), whether system headers are listed, and `-MP`/`-MG`. -/
structure DepPlan where
  file : String
  targets : List String
  quoted : List String
  system : Bool
  phony : Bool
  missingOk : Bool
  deriving DecidableEq, Repr

def Options.depPlan (o : Options) (input : String) : Option DepPlan :=
  if !(o.depMD || o.depMMD) || o.depM || o.depMM then none else
  let obj := objectName o input
  let file := o.depMF.getD (match o.mode, o.output with
    | .compile, some f => dropSuffix f ++ ".d"
    | _, _ => stem input ++ ".d")
  some { file, targets := if o.depMT.isEmpty && o.depMQ.isEmpty then [obj] else o.depMT
         quoted := o.depMQ, system := o.depMD, phony := o.depMP, missingOk := o.depMG }

/-- The libraries (`-lNAME`) that ccomp's runtime provides, or that have no counterpart (like
`pthread` in a single-threaded program): accepted without an archive. -/
def providedLibs : List String := ["c", "m", "pthread", "dl", "rt", "util", "gcc", "gcc_s"]

/-- The version ccomp reports. It is not gcc's: ccomp does not define `__GNUC__`. -/
def ccompVersion : String := "0.1.0"

/-- `--version` (§3.2). -/
def versionText (m : Machine) : String :=
  s!"ccomp (Silmaril) {ccompVersion}\nTarget: {m.triple}\n" ++
  "A C11 compiler in Lean: Cerberus typed Ail -> Mir -> Lir -> verified x86-64 backend.\n"

/-- `-print-prog-name=PROG` (§3.18): the program ccomp runs for PROG. gcc prints the bare name
when it is not in its own directories, which is what ccomp does. -/
def progName (p : String) : String :=
  match p with
  | "cc1" | "cpp" => "cpp"
  | other => other

/-- Diagnostics implied by the options alone: errors for options ccomp cannot honour (with
`Support.unsupported`), warnings for the unrecognized options under `--ccomp-permissive`. Notes
for ignored options are printed only with `-v`. -/
def Options.checks (o : Options) : List Diag := Id.run do
  let mut ds : List Diag := []
  for a in o.unknown do
    ds := ds ++ [.warn s!"unrecognized command-line option '{a}' ignored (--ccomp-permissive)"]
  for it in o.items do
    match it with
    | .stopS => ds := ds ++ [.usage "-S is not supported: ccomp has no assembly output (use -c)"]
    | .shared => ds := ds ++ [.usage "-shared is not supported: ccomp produces static executables only"]
    | .fflag f => if let (_, .unsupported why) := fClass f then
        ds := ds ++ [.usage s!"-f{f} is not supported: {why}"]
    | .mflag m => if let (_, .unsupported why) := mClass m then
        ds := ds ++ [.usage s!"-m{m} is not supported: {why}"]
    | _ => pure ()
  return ds

/-- Notes for `-v`: each accepted option that has no effect, and why. -/
def Options.notes (o : Options) : List Diag :=
  o.items.filterMap fun it =>
    let arg := " ".intercalate it.print
    let sup : Option Support := match it with
      | .fflag f => some (fClass f).2
      | .mflag m => some (mClass m).2
      | .warning w => some (wClass w).2
      | _ => match it.print with
        | a :: _ => (lookup a).map (·.1.support)
        | [] => none
    match sup with
    | some (.ignored why) => some (.note s!"{arg}: ignored: {why}")
    | _ => none

/-! ## Checks on concrete command lines -/

theorem reads_stopC : Item.reads .stopC = true := by decide

theorem reads_include : Item.reads (.dir .angled "include") = true := by decide

/-- The compile command of Rust's `cc` crate (1.2, `opt-level=0`, x86_64-unknown-linux-gnu). -/
theorem parse_cc_crate :
    (parseArgs ["-O0", "-ffunction-sections", "-fdata-sections", "-fPIC", "-g", "-fno-omit-frame-pointer",
      "-m64", "-I", "src", "-Wall", "-Wextra", "-o", "out/foo.o", "-c", "src/foo.c"]).toOption =
    some ({ opt := some .O0
            fflags := ["function-sections", "data-sections", "PIC", "no-omit-frame-pointer"]
            debug := [""]
            mflags := ["64"]
            dirs := [(.angled, "src")]
            warnings := ["all", "extra"]
            output := some "out/foo.o"
            stopC := true
            inputs := [.file "src/foo.c" .none] } : Options) := by
  decide

def errorOf {α : Type} : Except Diag α → Option Diag
  | .error d => some d
  | .ok _ => none

theorem parse_unknown : errorOf (parseArgs ["-frobnicate", "-Q"]) = some (badOpt "-Q") := by decide

theorem parse_permissive :
    (parseArgs ["-Q", "--ccomp-permissive", "x.c"]).toOption =
      some ({ unknown := ["-Q"], permissive := true, inputs := [.file "x.c" .none] } : Options) := by
  decide

theorem parse_missing : errorOf (parseArgs ["x.c", "-o"]) = some (missingArg "-o") := by decide

theorem parse_lang :
    (parseArgs ["-x", "c", "-", "-xnone", "a.i", "-lm", "-Wl,--gc-sections"]).toOption =
      some ({ inputs := [.file "-" .c, .file "a.i" .none, .lib "m", .linkerCommas "--gc-sections"] } :
        Options) := by
  decide

theorem responseTokens_quotes :
    responseTokens "-o 'a b'  \"c\\\"d\" e\\ f\n" = ["-o", "a b", "c\"d", "e f"] := by decide

theorem mode_earliest : ({ stopC := true, stopE := true } : Options).mode = .preprocess := by decide

end Silmaril.Compile.Driver
