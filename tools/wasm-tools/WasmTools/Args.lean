/-!
# Argument grammars of `wasm-tools` subcommands, as data

A subcommand's command line is described by a `CmdSpec` (its options and positional
arguments); `parseArgs` reads `List String` against it with clap's conventions as upstream
1.262.0 uses them:

* `--long`, `--long=VALUE`, `--long VALUE`; `-s`, `-sVALUE`, `-s VALUE`, `-s=VALUE`, and
  clusters of flags `-tvv` (the first option in a cluster that takes a value takes the rest);
* a flag or valued option given twice is an error unless it is a counter (`-v…`);
* `--` ends option parsing; `-` alone is a positional;
* `-h` / `--help` print the short / long help (exit 0).

Errors are clap's messages and exit status 2. This module is deliberately minimal and local:
the general grammar-as-data library is `Silmaril.Cli` (workflow `cli-spec`); once it lands this
file is replaced by a `Silmaril.Cli` grammar with derived, proved parser and help (see
`tools/wasm-tools/README.md`, "CLI layer").
-/

namespace WasmTools.Args

/-- One option. `value = some NAME` for an option taking a value (shown as `<NAME>`). -/
structure OptSpec where
  long : Option String := none
  short : Option Char := none
  value : Option String := none
  /-- A counter (`-v`, `-vv`, …): may repeat. -/
  count : Bool := false
  /-- A valued option that may repeat (each occurrence adds a value). -/
  multiple : Bool := false
  /-- Allowed values, if restricted. -/
  choices : List String := []
  /-- Clap's name for error messages; default `--long <VALUE>` or `-s`. -/
  display : Option String := none
  deriving Inhabited

/-- The key under which an option's occurrences are recorded. -/
def OptSpec.key (o : OptSpec) : String :=
  match o.long, o.short with
  | some l, _ => l
  | none, some c => c.toString
  | none, none => ""

def OptSpec.name (o : OptSpec) : String :=
  match o.display with
  | some d => d
  | none =>
    let base := match o.long, o.short with
      | some l, _ => "--" ++ l
      | none, some c => "-" ++ c.toString
      | none, none => ""
    match o.value with
    | some v => s!"{base} <{v}>"
    | none => base

/-- A subcommand's grammar. -/
structure CmdSpec where
  /-- `wasm-tools parse` etc., as in usage lines. -/
  path : String
  opts : List OptSpec
  /-- Names of the positional arguments, in order (all optional here). -/
  positionals : List String := []
  /-- The usage line clap prints in error messages. -/
  usage : String
  shortHelp : String
  longHelp : String

/-- The result of a successful parse. -/
structure Parsed where
  /-- Occurrences, newest first: option key and its value (`""` for flags). -/
  occ : List (String × String) := []
  positionals : List String := []
  deriving Inhabited

def Parsed.flag (p : Parsed) (k : String) : Bool := p.occ.any (·.1 == k)
def Parsed.count (p : Parsed) (k : String) : Nat := (p.occ.filter (·.1 == k)).length
def Parsed.value? (p : Parsed) (k : String) : Option String := (p.occ.find? (·.1 == k)).map (·.2)
def Parsed.values (p : Parsed) (k : String) : List String :=
  ((p.occ.filter (·.1 == k)).map (·.2)).reverse

/-- What the arguments ask for. -/
inductive Outcome where
  | ok (p : Parsed)
  | help (text : String)
  /-- A usage error: the full stderr text (exit 2). -/
  | usageError (text : String)

def footer : String := "\nFor more information, try '--help'.\n"

def errWithUsage (spec : CmdSpec) (msg : String) : Outcome :=
  .usageError s!"error: {msg}\n\nUsage: {spec.usage}\n{footer}"

def errNoUsage (msg : String) : Outcome := .usageError s!"error: {msg}\n{footer}"

def unexpected (spec : CmdSpec) (a : String) : Outcome :=
  if a.startsWith "-" then
    errWithUsage spec s!"unexpected argument '{a}' found\n\n  tip: to pass '{a}' as a value, use '-- {a}'"
  else errWithUsage spec s!"unexpected argument '{a}' found"

/-- Record one occurrence, checking repetition and choices. -/
def record (spec : CmdSpec) (p : Parsed) (o : OptSpec) (v : String) : Except Outcome Parsed := do
  if !o.count && !o.multiple && p.flag o.key then
    throw (errWithUsage spec s!"the argument '{o.name}' cannot be used multiple times")
  if !o.choices.isEmpty && !o.choices.contains v then
    -- the value parsers' own messages (wasm-tools' `ColorChoice` and `GenerateDwarf`)
    let why := match o.long with
      | some "color" =>
        s!": unrecognized color choice '{v}': valid choices are: always, always-ansi, never, auto"
      | some "generate-dwarf" => s!": unknown `--generate-dwarf` setting: {v}"
      | _ => ""
    throw (errNoUsage s!"invalid value '{v}' for '{o.name}'{why}")
  pure { p with occ := (o.key, v) :: p.occ }

def go (spec : CmdSpec) (p : Parsed) (onlyPos : Bool) : List String → Except Outcome Parsed
  | [] => pure p
  | a :: rest =>
    let positional : Except Outcome Parsed :=
      if p.positionals.length < spec.positionals.length then
        go spec { p with positionals := p.positionals ++ [a] } onlyPos rest
      else throw (unexpected spec a)
    if onlyPos then positional
    else if a == "--" then go spec p true rest
    else if a == "-h" then throw (.help spec.shortHelp)
    else if a == "--help" then throw (.help spec.longHelp)
    else if a.startsWith "--" then do
      let body := a.drop 2 |>.toString
      let (name, inl) := match body.splitOn "=" with
        | [n] => (n, none)
        | n :: vs => (n, some ("=".intercalate vs))
        | [] => (body, none)
      match spec.opts.find? (·.long == some name) with
      | none => throw (unexpected spec a)
      | some o =>
        match o.value, inl with
        | none, some v =>
          throw (errWithUsage spec s!"unexpected value '{v}' for '--{name}' found; no more were expected")
        | none, none => go spec (← record spec p o "") onlyPos rest
        | some _, some v => go spec (← record spec p o v) onlyPos rest
        | some _, none =>
          match rest with
          | v :: rest' =>
            if v.startsWith "-" && v != "-" then
              throw (errNoUsage s!"a value is required for '{o.name}' but none was supplied")
            else go spec (← record spec p o v) onlyPos rest'
          | [] => throw (errNoUsage s!"a value is required for '{o.name}' but none was supplied")
    else if a.startsWith "-" && a.length > 1 then do
      -- a cluster of short options
      let rec cluster (p : Parsed) :
          List Char → Except Outcome (Parsed × {r : List String // r.length ≤ rest.length})
        | [] => pure (p, ⟨rest, Nat.le_refl _⟩)
        | c :: cs =>
          if c == 'h' then throw (.help spec.shortHelp) else
          match spec.opts.find? (·.short == some c) with
          | none => throw (unexpected spec ("-" ++ c.toString))
          | some o =>
            match o.value with
            | none => do cluster (← record spec p o "") cs
            | some _ =>
              let v := String.ofList (match cs with | '=' :: t => t | t => t)
              if cs.isEmpty then
                match rest with
                | v :: rest' =>
                  if v.startsWith "-" && v != "-" then
                    throw (errNoUsage s!"a value is required for '{o.name}' but none was supplied")
                  else do
                    pure ((← record spec p o v), ⟨rest', by simp⟩)
                | [] => throw (errNoUsage s!"a value is required for '{o.name}' but none was supplied")
              else do pure ((← record spec p o v), ⟨rest, Nat.le_refl _⟩)
      let (p', ⟨rest', hle⟩) ← cluster p (a.toList.drop 1)
      go spec p' onlyPos rest'
    else positional
termination_by args => args.length
decreasing_by all_goals simp_all <;> omega

def parseArgs (spec : CmdSpec) (args : List String) : Outcome :=
  match go spec {} false args with
  | .ok p => .ok p
  | .error o => o

/-! ## Options shared by most upstream subcommands -/

def generalOpts : List OptSpec :=
  [ { long := "verbose", short := 'v', count := true, display := "--verbose..." },
    { long := "color", value := "COLOR", choices := ["always", "always-ansi", "never", "auto"] } ]

def inputOpts : List OptSpec :=
  [ { long := "generate-dwarf", value := "lines|full", choices := ["lines", "full"],
      display := "--generate-dwarf <lines|full>" },
    { short := 'g' } ]

def outputOpts : List OptSpec := [ { long := "output", short := 'o', value := "OUTPUT" } ]

/-! ## Unit tests of the grammar reader -/

private def testSpec : CmdSpec :=
  { path := "wasm-tools parse", opts := inputOpts ++ outputOpts ++ generalOpts ++
      [{ long := "wat", short := 't' }], positionals := ["INPUT"],
    usage := "wasm-tools parse [OPTIONS] [INPUT]", shortHelp := "S", longHelp := "L" }

private def okKeys : Outcome → Option (List (String × String) × List String)
  | .ok p => some (p.occ.reverse, p.positionals)
  | _ => none

private def isUsage : Outcome → Bool
  | .usageError _ => true
  | _ => false

#guard okKeys (parseArgs testSpec ["-to-", "a.wat"]) = some ([("wat", ""), ("output", "-")], ["a.wat"])
#guard okKeys (parseArgs testSpec ["--output=x", "-vvv", "-"]) =
  some ([("output", "x"), ("verbose", ""), ("verbose", ""), ("verbose", "")], ["-"])
#guard okKeys (parseArgs testSpec ["--", "-t"]) = some ([], ["-t"])
#guard isUsage (parseArgs testSpec ["-t", "-t"])
#guard isUsage (parseArgs testSpec ["-o"])
#guard isUsage (parseArgs testSpec ["-o", "--wat"])
#guard isUsage (parseArgs testSpec ["a", "b"])
#guard isUsage (parseArgs testSpec ["--color=bad"])
#guard isUsage (parseArgs testSpec ["--wat=1"])
#guard isUsage (parseArgs testSpec ["-x"])
#guard (match parseArgs testSpec ["a", "--help"] with | .help "L" => true | _ => false)
#guard (match parseArgs testSpec ["-th"] with | .help "S" => true | _ => false)

end WasmTools.Args
