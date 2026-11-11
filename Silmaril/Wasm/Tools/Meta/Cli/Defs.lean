module

public import Silmaril.Wasm.Tools.Suggest.Defs

/-!
# The argument grammar of the `demangle`, `metadata` and `addr2line` subcommands

A model of the part of clap 4 (the argument parser of `wasm-tools 1.262.0`) these subcommands
use, as a pure function `parseArgs : Cmd → List String → Except String Parsed`:

* Arguments are read left to right. `--` makes every later argument positional; `-` alone is
  positional. `--long`, `--long=VALUE`, `--long VALUE`; short clusters `-abc`, where an option
  taking a value takes the rest of the cluster (a leading `=` dropped) or the next argument.
* A value may not start with `-` (unless it is `-` itself): then, or at the end of the
  arguments, the error is "a value is required" if the next argument is a known option, and
  "unexpected argument" for that argument otherwise. `--long=` is a missing value.
* `-h` prints the short help and `--help` the long help, as soon as they are read.
* An option or flag used twice that does not repeat ("cannot be used multiple times"), a flag
  seen a value ("unexpected value"), an unknown option ("unexpected argument" with the
  `-- ARG` tip), a second positional argument ("unexpected argument"), a value its parser
  refuses ("invalid value"), and after reading everything, two conflicting arguments ("cannot
  be used with"; reported for the first argument, in command-line order, that conflicts with
  another).
* Every error is clap's message (`clapError`), printed to stderr with exit status 2.

* An unknown long argument gets clap's suggestion (`Suggest.didYouMean` over the long names and
  `help`): "a similar argument exists" when one is similar enough, the `-- ARG` tip otherwise;
  its usage line lists the arguments used so far, in command-line order, then the suggested one
  (`usedUsage`). A conflict's usage line lists the arguments used except the conflicting one.

Not modelled: help text wrapping to the terminal width (`COLUMNS`): the help texts are the ones
upstream prints when `COLUMNS` is unset.

Theorems: `Silmaril.Wasm.Tools.Meta.Cli.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Cli

/-- `s` without its first `n` characters. -/
def dropS (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- An option or flag. `long = ""` for a short-only argument. -/
structure Opt where
  long : String
  short : Option Char := none
  /-- The value name, for an option that takes a value. -/
  value : Option String := none
  /-- May be seen more than once (`Vec` options and counted flags). -/
  repeats : Bool := false
  /-- The long names (or `-c` for short-only) of the arguments it conflicts with. -/
  conflicts : List String := []
  /-- The value parser: an error message for refused values. -/
  check : String → Option String := fun _ => none
  deriving Inhabited

/-- How the argument is named in messages: `--long <VALUE>`, `--long` or `-c`. -/
def Opt.display (o : Opt) : String :=
  let n := if o.long.isEmpty then "-" ++ (o.short.map toString).getD "" else "--" ++ o.long
  match o.value with
  | some v => n ++ " <" ++ v ++ ">"
  | none => n

/-- The key of an argument (`long`, or `-c`). -/
def Opt.key (o : Opt) : String :=
  if o.long.isEmpty then "-" ++ (o.short.map toString).getD "" else o.long

/-- A subcommand: its name in messages (`wasm-tools metadata add`), its arguments, and the name
of its optional positional argument. -/
structure Cmd where
  name : String
  opts : List Opt
  positional : String := "INPUT"
  /-- A second, repeated positional argument (`[ADDRESSES]...`), if any. -/
  rest : Option String := none
  deriving Inhabited

/-- The result of parsing: the arguments seen (key and value, in order; the values of a repeated
positional argument follow, keyed by its name), the positional argument, or a request for
help. -/
inductive Parsed where
  | ok (seen : List (String × Option String)) (input : Option String)
  /-- `-h` (`long = false`) or `--help`. -/
  | usage (long : Bool)
  deriving Inhabited, Repr, DecidableEq

def Cmd.usage (c : Cmd) : String :=
  c.name ++ " [OPTIONS] [" ++ c.positional ++ "]" ++ ((c.rest.map (" [" ++ · ++ "]...")).getD "")

/-- clap's error text (without the final newline handling: lines end with `\n`). -/
def clapError (msg : String) (usage : Option String) : String :=
  "error: " ++ msg ++ "\n\n" ++
  (match usage with | some u => "Usage: " ++ u ++ "\n\n" | none => "") ++
  "For more information, try '--help'.\n"

def errUnexpected (c : Cmd) (a : String) : String :=
  clapError ("unexpected argument '" ++ a ++ "' found\n\n  tip: to pass '" ++ a ++
    "' as a value, use '-- " ++ a ++ "'") (some c.usage)

/-- How a used argument is named in a usage line: `display`, with `...` for a repeated flag. -/
def Opt.usageName (o : Opt) : String :=
  if o.repeats && o.value.isNone then o.display ++ "..." else o.display

/-- The usage line clap builds from the arguments used (`create_usage_with_title(&used)`): the
used options in order, then the positional argument (`<INPUT>` if given, else `[INPUT]`);
the plain usage when nothing was used. -/
def usedUsage (c : Cmd) (used : List Opt) (input : Bool) (rest : Bool := false) : String :=
  if used.isEmpty && !input then c.usage else
  " ".intercalate (c.name :: used.map (·.usageName)) ++
    (if input then " <" ++ c.positional ++ ">" else " [" ++ c.positional ++ "]") ++
    ((c.rest.map fun r => if rest then " <" ++ r ++ ">..." else " [" ++ r ++ "]...").getD "")

def errPositional (c : Cmd) (a : String) : String :=
  clapError ("unexpected argument '" ++ a ++ "' found") (some c.usage)

def errNoValue (o : Opt) : String :=
  clapError ("a value is required for '" ++ o.display ++ "' but none was supplied") none

def errTwice (c : Cmd) (o : Opt) : String :=
  clapError ("the argument '" ++ o.display ++ "' cannot be used multiple times") (some c.usage)

def errInvalid (o : Opt) (v msg : String) : String :=
  clapError ("invalid value '" ++ v ++ "' for '" ++ o.display ++ "': " ++ msg) none

def errFlagValue (c : Cmd) (o : Opt) (v : String) : String :=
  clapError ("unexpected value '" ++ v ++ "' for '" ++ o.display ++ "' found; no more were expected")
    (some (c.name ++ " " ++ o.display ++ " [" ++ c.positional ++ "]"))

def errConflict (c : Cmd) (o p : Opt) (used : List Opt) (input : Bool) : String :=
  clapError ("the argument '" ++ o.display ++ "' cannot be used with '" ++ p.display ++ "'")
    (some (usedUsage c (used.filter (·.key != p.key)) input))

def Cmd.byLong (c : Cmd) (l : String) : Option Opt := c.opts.find? (fun o => !o.long.isEmpty && o.long == l)
def Cmd.byShort (c : Cmd) (ch : Char) : Option Opt := c.opts.find? (·.short == some ch)

/-- Whether an argument would be read as an option of `c` (for the missing-value rule). -/
def Cmd.knownFlag (c : Cmd) (a : String) : Bool :=
  if a.startsWith "--" then
    let n := ((dropS a 2).splitOn "=").headD ""
    n == "help" || (c.byLong n).isSome
  else match (dropS a 1).toList with
    | ch :: _ => ch == 'h' || (c.byShort ch).isSome
    | [] => false

/-- Whether an argument looks like an option (starts with `-` and is not `-`). -/
def flagLike (a : String) : Bool := a.startsWith "-" && a != "-"

/-- The parser's state. -/
structure St where
  seen : List (String × Option String) := []
  input : Option String := none
  dashdash : Bool := false
  /-- The values of the repeated positional argument. -/
  extra : List String := []

/-- The arguments used so far, each once, in the order of their first use. -/
def St.used (c : Cmd) (st : St) : List Opt :=
  (st.seen.map (·.1)).foldl (fun acc k =>
    if acc.any (·.key == k) then acc else
    match c.opts.find? (·.key == k) with
    | some o => acc ++ [o]
    | none => acc) []

/-- The `help` flag as clap lists it. -/
def helpOpt : Opt := { long := "help", short := some 'h' }

/-- clap's error for an unknown long argument `--n` (`did_you_mean_error`). -/
def errUnknownLong (c : Cmd) (st : St) (n : String) : String :=
  let a := "--" ++ n
  let longs := (c.opts.filter (!·.long.isEmpty)).map (·.long) ++ ["help"]
  let used := st.used c
  match Suggest.didYouMean n longs with
  | some l =>
    let o := ((c.opts ++ [helpOpt]).find? (·.long == l)).getD helpOpt
    let used := if used.any (·.key == o.key) then used else used ++ [o]
    clapError ("unexpected argument '" ++ a ++ "' found\n\n  tip: a similar argument exists: '--" ++
      l ++ "'") (some (usedUsage c used st.input.isSome !st.extra.isEmpty))
  | none =>
    clapError ("unexpected argument '" ++ a ++ "' found\n\n  tip: to pass '" ++ a ++
      "' as a value, use '-- " ++ a ++ "'") (some (usedUsage c used st.input.isSome !st.extra.isEmpty))

/-- One step of the result: continue with a state and the remaining arguments, stop with a
result, or fail. -/
inductive Step where
  | next (st : St) (rest : List String)
  /-- A help flag: the long help (`--help`) or the short one (`-h`). -/
  | help (long : Bool)
  | fail (e : String)

/-- Record an occurrence of `o` (with its value). -/
def record (c : Cmd) (st : St) (o : Opt) (v : Option String) : Except String St :=
  if !o.repeats && st.seen.any (·.1 == o.key) then .error (errTwice c o) else
  match v with
  | some x =>
    match o.check x with
    | some m => .error (errInvalid o x m)
    | none => .ok { st with seen := st.seen ++ [(o.key, v)] }
  | none => .ok { st with seen := st.seen ++ [(o.key, v)] }

/-- The error when `o` lacks its value and the next argument is `next?`. -/
def missingValue (c : Cmd) (st : St) (o : Opt) (next? : Option String) : String :=
  match next? with
  | some n => if c.knownFlag n then errNoValue o
      else if n.startsWith "--" then errUnknownLong c st (dropS ((n.splitOn "=").headD n) 2)
      else errUnexpected c ("-" ++ ((dropS n 1).toList.headD ' ').toString)
  | none => errNoValue o

/-- An option `o` that takes a value, whose value is `inline` (if seen in the same argument)
or the next argument. -/
def takeValue (c : Cmd) (st : St) (o : Opt) (inline : Option String) (rest : List String) : Step :=
  match inline with
  | some "" => .fail (errNoValue o)
  | some v => match record c st o (some v) with
    | .ok st => .next st rest
    | .error e => .fail e
  | none =>
    match rest with
    | v :: rest' =>
      if flagLike v then .fail (missingValue c st o (some v)) else
      match record c st o (some v) with
      | .ok st => .next st rest'
      | .error e => .fail e
    | [] => .fail (missingValue c st o none)

/-- A cluster of short flags (the characters after `-`). -/
def shorts (c : Cmd) (st : St) (rest : List String) : List Char → Step
  | [] => .next st rest
  | 'h' :: _ => .help false
  | ch :: cs =>
    match c.byShort ch with
    | none => .fail (errUnexpected c ("-" ++ ch.toString))
    | some o =>
      match o.value with
      | some _ =>
        let v := String.ofList cs
        let v := if v.startsWith "=" then dropS v 1 else v
        takeValue c st o (if cs.isEmpty then none else some v) rest
      | none =>
        match record c st o none with
        | .ok st => shorts c st rest cs
        | .error e => .fail e

/-- One argument. -/
def step (c : Cmd) (st : St) (a : String) (rest : List String) : Step :=
  if st.dashdash || !flagLike a then
    if st.input.isSome then
      if c.rest.isSome then .next { st with extra := st.extra ++ [a] } rest
      else .fail (errPositional c a)
    else .next { st with input := some a } rest
  else if a == "--" then .next { st with dashdash := true } rest
  else if a == "--help" then .help true
  else if a.startsWith "--" then
    let body := dropS a 2
    let (n, inline) := match body.splitOn "=" with
      | [n] => (n, none)
      | n :: vs => (n, some ("=".intercalate vs))
      | [] => (body, none)
    if n == "help" then .help true else
    match c.byLong n with
    | none => .fail (errUnknownLong c st n)
    | some o =>
      match o.value with
      | some _ => takeValue c st o inline rest
      | none =>
        match inline with
        | some v => .fail (errFlagValue c o v)
        | none => match record c st o none with
          | .ok st => .next st rest
          | .error e => .fail e
  else shorts c st rest (dropS a 1).toList

/-- The first argument, in command-line order, that conflicts with another seen argument. -/
def firstConflict (c : Cmd) (seen : List String) : Option (Opt × Opt) :=
  seen.findSome? fun k =>
    match c.opts.find? (·.key == k) with
    | none => none
    | some o => (o.conflicts.find? (seen.contains ·)).bind fun k' =>
        (c.opts.find? (·.key == k')).map (o, ·)

/-- **The argument parser.** `fuel` bounds the number of steps (one per argument). -/
def parseGo (c : Cmd) : Nat → St → List String → Except String Parsed
  | _, st, [] =>
    let seen := st.seen ++ st.extra.map fun a => (c.rest.getD "", some a)
    match firstConflict c (seen.map (·.1)) with
    | some (o, p) => .error (errConflict c o p (st.used c) st.input.isSome)
    | none => .ok (.ok seen st.input)
  | 0, _, _ :: _ => .error "too many arguments"
  | f + 1, st, a :: rest =>
    match step c st a rest with
    | .next st rest => parseGo c f st rest
    | .help l => .ok (.usage l)
    | .fail e => .error e

/-- Parse the arguments of a subcommand (after its name). -/
def parseArgs (c : Cmd) (args : List String) : Except String Parsed :=
  parseGo c (args.length + 1) {} args

/-- The value of an option (the last one seen). -/
def Parsed.get? (p : List (String × Option String)) (k : String) : Option String :=
  (p.filter (·.1 == k)).getLast?.bind (·.2)

/-- All values of a repeated option, in order. -/
def Parsed.getAll (p : List (String × Option String)) (k : String) : List String :=
  (p.filter (·.1 == k)).filterMap (·.2)

/-- Whether a flag was seen. -/
def Parsed.has (p : List (String × Option String)) (k : String) : Bool := p.any (·.1 == k)

/-! ## The options shared by these subcommands -/

/-- termcolor's `ColorChoice` parser. -/
def colorCheck (v : String) : Option String :=
  if v ∈ ["always", "always-ansi", "never", "auto"] then none
  else some ("unrecognized color choice '" ++ v ++ "': valid choices are: always, always-ansi, never, auto")

/-- `InputOutput`'s options: `-o`, `--output`; `-v`, `--verbose`, `--color`. -/
def ioOpts : List Opt :=
  [{ long := "output", short := some 'o', value := some "OUTPUT" },
   { long := "verbose", short := some 'v', repeats := true },
   { long := "color", value := some "COLOR", check := colorCheck }]

/-- `-t`, `--wat`. -/
def watOpt : Opt := { long := "wat", short := some 't' }

/-- `wasm-tools demangle`. -/
def demangleCmd : Cmd := { name := "wasm-tools demangle", opts := ioOpts ++ [watOpt] }

/-- `wasm-tools metadata show`. -/
def showCmd : Cmd := { name := "wasm-tools metadata show", opts := ioOpts ++ [{ long := "json" }] }

/-- `NAME=VERSION` (wasm-metadata's `parse_key_value`). -/
def kvCheck (v : String) : Option String :=
  if (v.splitOn "=").length ≥ 2 then none else some "expected KEY=VALUE"

/-- `--generate-dwarf`. -/
def dwarfCheck (v : String) : Option String :=
  if v == "lines" || v == "full" then none else some ("unknown `--generate-dwarf` setting: " ++ v)

/-- A `--x` and `--clear-x` pair of `AddMetadataOpts`. -/
def setClear (x : String) (check : String → Option String := fun _ => none) : List Opt :=
  [{ long := x, value := some "NAME", conflicts := ["clear-" ++ x], check := check },
   { long := "clear-" ++ x, conflicts := [x] }]

/-- `wasm-tools metadata add`, with a license-expression checker. -/
def addCmd (licenseCheck : String → Option String) : Cmd :=
  { name := "wasm-tools metadata add",
    opts :=
      [{ long := "generate-dwarf", value := some "lines|full", conflicts := ["-g"],
         check := dwarfCheck },
       { long := "", short := some 'g', conflicts := ["generate-dwarf"] }] ++ ioOpts ++
      setClear "name" ++
      [{ long := "language", value := some "NAME=VERSION", repeats := true, check := kvCheck },
       { long := "processed-by", value := some "NAME=VERSION", repeats := true, check := kvCheck },
       { long := "sdk", value := some "NAME=VERSION", repeats := true, check := kvCheck }] ++
      setClear "authors" ++ setClear "description" ++ setClear "licenses" licenseCheck ++
      setClear "source" ++ setClear "homepage" ++ setClear "revision" ++ setClear "version" ++
      [watOpt] }

/-- `wasm-tools addr2line`. -/
def addr2lineCmd : Cmd :=
  { name := "wasm-tools addr2line", rest := some "ADDRESSES",
    opts :=
      [{ long := "generate-dwarf", value := some "lines|full", conflicts := ["-g"], check := dwarfCheck },
       { long := "", short := some 'g', conflicts := ["generate-dwarf"] }] ++ ioOpts ++
      [{ long := "code-section-relative" }] }

end Silmaril.Wasm.Tools.Meta.Cli

end
