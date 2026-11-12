module

public import Init

/-!
# A specified subset of clap's argument parsing, for the component subcommands

`wasm-tools` 1.262.0 parses its arguments with clap 4. The component subcommands of this
track (`validate`, `print`, `parse` on components) use a small subset of clap's behaviour,
which `parse` implements as a pure function of a command description (`CmdSpec`) and the
arguments after the subcommand name:

* long options `--name`, `--name VALUE`, `--name=VALUE`; short options `-x`, `-x VALUE`,
  `-xVALUE`, `-x=VALUE` and clusters of flags `-vvg` (a value-taking short option ends the
  cluster and takes the rest, or the next argument);
* `--` ends the options; `-` alone is a positional (stdin);
* `-h` asks for the short help, `--help` for the long help (`Outcome.help`);
* errors with clap's messages and exit status 2 (`Outcome.usage`): an unknown option
  (`unexpected argument '…' found`, with clap's `tip` for arguments starting with `-`), too
  many positionals, a missing value (`a value is required for '--x <V>' but none was
  supplied`), a value given to a flag (`unexpected value '…' for '--x' found; no more were
  expected`), an option given twice that is not repeatable (`the argument '--x <V>' cannot be
  used multiple times`).

Values are not checked here (choices such as `--color` are checked by the subcommand).
`Thms` states the parser's laws (`parse_nil`, `parse_positional`, `parse_long_value`,
`parse_help_*`, …), each proved by evaluation in the kernel on a representative
`CmdSpec`, and `occurrences` lemmas.

Deviations from clap (documented in `tools/wasm-tools/README.md`): abbreviations of long options
are not accepted (clap does not accept them either by default); clap's `Usage:` line after a
conflict names the arguments used, here always the command's generic usage line.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.ValArgs

/-- One option. -/
structure OptSpec where
  long : String
  short : Option Char := none
  /-- The value name (`FEATURES` for `--features <FEATURES>`); `none` for a flag. -/
  value : Option String := none
  /-- May it occur several times (`Vec` values, counted flags such as `-v`)? -/
  multi : Bool := false
  /-- Is `--long` accepted (`false` for short-only options such as `-g`, whose `long` is only
  a key)? -/
  hasLong : Bool := true
  deriving Repr, DecidableEq

/-- A subcommand: its usage line (`wasm-tools validate [OPTIONS] [INPUT]`), its options and
the number of positionals it takes. -/
structure CmdSpec where
  usage : String
  opts : List OptSpec
  maxPos : Nat := 1
  deriving Repr

/-- The parsed arguments: every option occurrence (long name and value, `""` for a flag), in
order, and the positionals. -/
structure Parsed where
  occs : List (String × String) := []
  pos : List String := []
  deriving Repr, DecidableEq

/-- The result. -/
inductive Outcome where
  | ok (p : Parsed)
  /-- `-h` (`false`) or `--help` (`true`). -/
  | help (long : Bool)
  /-- A usage error: the whole message clap prints on stderr (exit status 2). -/
  | usage (msg : String)
  deriving Repr, DecidableEq

/-- How clap names an option in messages. -/
def OptSpec.display (o : OptSpec) : String :=
  if !o.hasLong then s!"-{o.long}" else
  match o.value with
  | some v => s!"--{o.long} <{v}>"
  | none => s!"--{o.long}"

/-- The trailer of an error with the usage line. -/
def withUsage (spec : CmdSpec) (msg : String) : String :=
  s!"error: {msg}\n\nUsage: {spec.usage}\n\nFor more information, try '--help'.\n"

/-- The trailer of an error without the usage line. -/
def noUsage (msg : String) : String := s!"error: {msg}\n\nFor more information, try '--help'.\n"

def unexpected (spec : CmdSpec) (a : String) : String :=
  if a.startsWith "-" then
    withUsage spec s!"unexpected argument '{a}' found\n\n  tip: to pass '{a}' as a value, use '-- {a}'"
  else withUsage spec s!"unexpected argument '{a}' found"

def missingValue (o : OptSpec) : String :=
  noUsage s!"a value is required for '{o.display}' but none was supplied"

/-- The subcommand part of the usage line (`wasm-tools validate`). -/
def cmdOf (spec : CmdSpec) : String := " ".intercalate ((spec.usage.splitOn " ").take 2)

def flagValue (spec : CmdSpec) (o : OptSpec) (v : String) : String :=
  s!"error: unexpected value '{v}' for '{o.display}' found; no more were expected\n\n" ++
    s!"Usage: {cmdOf spec} {o.display} [INPUT]\n\nFor more information, try '--help'.\n"

def repeated (spec : CmdSpec) (o : OptSpec) : String :=
  withUsage spec s!"the argument '{o.display}' cannot be used multiple times"

/-- Record an occurrence, refusing a second one of a non-repeatable option. -/
def Parsed.add (spec : CmdSpec) (p : Parsed) (o : OptSpec) (v : String) : Except String Parsed :=
  if !o.multi && p.occs.any (·.1 == o.long) then .error (repeated spec o)
  else .ok { p with occs := p.occs ++ [(o.long, v)] }

/-- Add a positional. -/
def Parsed.addPos (spec : CmdSpec) (p : Parsed) (a : String) : Except String Parsed :=
  if p.pos.length < spec.maxPos then .ok { p with pos := p.pos ++ [a] }
  else .error (unexpected spec a)

/-- The result of one step: go on with the rest of the arguments, or stop with help. -/
inductive Step where
  | next (p : Parsed) (rest : List String)
  | help (long : Bool)

/-- Record an occurrence and go on with `rest`. -/
def addNext (spec : CmdSpec) (p : Parsed) (o : OptSpec) (v : String) (rest : List String) :
    Except String Step :=
  match p.add spec o v with
  | .ok q => .ok (.next q rest)
  | .error e => .error e

/-- Does the argument look like an option (`-x…` or `--…`, not `-` alone)? -/
def hyphen (v : String) : Bool := v.startsWith "-" && v != "-"

/-- The error clap gives when the argument after a value-taking option looks like an option:
it parses that argument as an option; an unknown one is reported (a short cluster by its
first letter), a known one leaves the value missing. -/
def hyphenError (spec : CmdSpec) (o : OptSpec) (v : String) : String :=
  if v.startsWith "--" then
    let n := (((v.drop 2).toString.splitOn "=").headD "")
    if v == "--help" || spec.opts.any (fun o => o.hasLong && o.long == n) then missingValue o
    else unexpected spec v
  else match (v.drop 1).toString.toList with
    | c :: _ =>
      if c == 'h' || spec.opts.any (·.short == some c) then missingValue o
      else unexpected spec ("-" ++ String.ofList [c])
    | [] => missingValue o

/-- Take the next argument as the value of `o`. -/
def nextValue (spec : CmdSpec) (p : Parsed) (o : OptSpec) : List String → Except String Step
  | v :: rest => if hyphen v then .error (hyphenError spec o v) else addNext spec p o v rest
  | [] => .error (missingValue o)

/-- A value-taking short option whose cluster continues with `cs`: the rest of the cluster
(after an optional `=`) is the value, else the next argument. -/
def shortValue (spec : CmdSpec) (p : Parsed) (o : OptSpec) :
    List Char → List String → Except String Step
  | [], rest => nextValue spec p o rest
  | '=' :: v, rest => addNext spec p o (String.ofList v) rest
  | v, rest => addNext spec p o (String.ofList v) rest

/-- A cluster of short options `-abc` (the characters after `-`), then the remaining
arguments. -/
def shortCluster (spec : CmdSpec) (p : Parsed) (whole : String) :
    List Char → List String → Except String Step
  | [], rest => .ok (.next p rest)
  | c :: cs, rest =>
    if c == 'h' then .ok (.help false)
    else match spec.opts.find? (·.short == some c) with
      | none => .error (unexpected spec ("-" ++ String.ofList [c]))
      | some o =>
        match o.value with
        | none =>
          match p.add spec o "" with
          | .ok q => shortCluster spec q whole cs rest
          | .error e => .error e
        | some _ => shortValue spec p o cs rest

/-- The name of a long option `--name` or `--name=value`. -/
def longName (a : String) : String := (((a.drop 2).toString.splitOn "=").headD "")

/-- The inline value of `--name=value`. -/
def longInline (a : String) : Option String :=
  match (a.drop 2).toString.splitOn "=" with
  | _ :: v :: vs => some ("=".intercalate (v :: vs))
  | _ => none

/-- The value of a long option: inline, or the next argument. -/
def longValue (spec : CmdSpec) (p : Parsed) (o : OptSpec) (inl : Option String)
    (rest : List String) : Except String Step :=
  match o.value, inl with
  | none, none => addNext spec p o "" rest
  | none, some v => .error (flagValue spec o v)
  | some _, some v => addNext spec p o v rest
  | some _, none => nextValue spec p o rest

/-- One argument `a` (not after `--`), with the remaining arguments. -/
def step (spec : CmdSpec) (p : Parsed) (a : String) (rest : List String) : Except String Step :=
  if a == "--help" then .ok (.help true)
  else if a.startsWith "--" then
    match spec.opts.find? (fun o => o.hasLong && o.long == longName a) with
    | none => .error (unexpected spec a)
    | some o => longValue spec p o (longInline a) rest
  else if a.startsWith "-" && a != "-" then
    shortCluster spec p a (a.drop 1).toString.toList rest
  else match p.addPos spec a with
    | .ok q => .ok (.next q rest)
    | .error e => .error e

/-- Positionals after `--`. -/
def allPos (spec : CmdSpec) (p : Parsed) : List String → Except String Parsed
  | [] => .ok p
  | a :: as => do allPos spec (← p.addPos spec a) as

/-- The main loop (structural on the arguments' list via fuel = its length). -/
def go (spec : CmdSpec) : Nat → Parsed → List String → Outcome
  | _, p, [] => .ok p
  | 0, _, _ => .usage "error: internal: argument fuel exhausted\n"
  | n + 1, p, a :: rest =>
    if a == "--" then
      match allPos spec p rest with
      | .ok p => .ok p
      | .error e => .usage e
    else match step spec p a rest with
      | .error e => .usage e
      | .ok (.help l) => .help l
      | .ok (.next p rest') => go spec n p rest'

/-- **Parse the arguments of a subcommand.** -/
def parse (spec : CmdSpec) (args : List String) : Outcome := go spec (args.length + 1) {} args

/-! ## Reading the result -/

/-- The values of every occurrence of an option. -/
def Parsed.values (p : Parsed) (long : String) : List String :=
  p.occs.filterMap fun (n, v) => if n == long then some v else none

/-- The last value of an option. -/
def Parsed.value? (p : Parsed) (long : String) : Option String := (p.values long).getLast?

/-- Was a flag given? -/
def Parsed.flag (p : Parsed) (long : String) : Bool := p.occs.any (·.1 == long)

/-- The input (`-` or absent: stdin). -/
def Parsed.input? (p : Parsed) : Option String :=
  match p.pos.head? with
  | some "-" => none
  | x => x

/-! ## The options of upstream's subcommands -/

/-- Options shared by `validate`, `print`, `parse` (`GeneralOpts`, `GenerateDwarfArg`). -/
def common : List OptSpec :=
  [ { long := "generate-dwarf", value := some "lines|full" },
    { long := "g", short := some 'g', hasLong := false },
    { long := "verbose", short := some 'v', multi := true },
    { long := "color", value := some "COLOR" } ]

/-- `wasm-tools validate`. -/
def validateSpec : CmdSpec where
  usage := "wasm-tools validate [OPTIONS] [INPUT]"
  opts := common ++
    [ { long := "features", short := some 'f', value := some "FEATURES", multi := true },
      { long := "validate-custom" } ]

/-- `wasm-tools print`. -/
def printSpec : CmdSpec where
  usage := "wasm-tools print [OPTIONS] [INPUT]"
  opts := common ++
    [ { long := "output", short := some 'o', value := some "OUTPUT" },
      { long := "print-offsets", short := some 'p' }, { long := "skeleton" },
      { long := "name-unnamed" }, { long := "fold-instructions", short := some 'f' },
      { long := "print-operand-stack" }, { long := "indent-text", value := some "INDENT_TEXT" },
      { long := "indent", value := some "INDENT" } ]

/-- `wasm-tools parse`. -/
def parseSpec : CmdSpec where
  usage := "wasm-tools parse [OPTIONS] [INPUT]"
  opts := common ++
    [ { long := "output", short := some 'o', value := some "OUTPUT" },
      { long := "wat", short := some 't' } ]

/-- clap's check of a value against its choices. -/
def checkChoice (o : String) (v : String) (choices : List String) (what : String) :
    Except String Unit :=
  if choices.contains v then .ok ()
  else .error (noUsage s!"invalid value '{v}' for '{o}': unrecognized {what} '{v}': valid choices are: {", ".intercalate choices}")

/-- The checks of the common options: `--color` choices, `-g` against `--generate-dwarf`. -/
def checkCommon (spec : CmdSpec) (p : Parsed) : Except String Unit := do
  for v in p.values "color" do
    checkChoice "--color <COLOR>" v ["always", "always-ansi", "never", "auto"] "color choice"
  for v in p.values "generate-dwarf" do
    if !(v == "lines" || v == "full") then
      .error (noUsage s!"invalid value '{v}' for '--generate-dwarf <lines|full>': unknown `--generate-dwarf` setting: {v}")
  if p.flag "g" && p.flag "generate-dwarf" then
    .error (s!"error: the argument '-g' cannot be used with '--generate-dwarf <lines|full>'\n\n" ++
      s!"Usage: {cmdOf spec} -g <INPUT>\n\nFor more information, try '--help'.\n")

end Silmaril.Wasm.Tools.Component.ValArgs
