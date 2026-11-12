module

@[expose] public section

/-!
# Command-line argument grammars as data

A command line is specified by a `Command`: a tree of commands (nested subcommands, with
aliases), each with options (`Opt`: flags, counted flags, negatable flags, options with a typed
value that may be optional, a default, an environment variable, repetition, inheritance by the
subcommands) and positional arguments (`Pos`, with an arity). Everything a program needs to
handle its argument vector is *derived* from that one value:

* `scan c argv` parses `argv` into an `Invocation` (a list of `Frame`s, one per command level),
  `render c fs` prints an invocation back in normal form (`Silmaril.Cli.Args.Thms`: the parser is
  sound and complete for the inductive grammar `Scans c`, and `scan c (render c fs) = .ok fs`);
* `resolve c env fs` types the values, applies environment variables and defaults, binds
  positionals and gives `Matches`, which programs query (`m.flag`, `m.count`, `m.switch`,
  `m.str?`, `m.nat?`, …);
* `judge c env fs` adds the checks a grammar declares beyond types: `ValueCheck`s
  (`Command.checks`, in force at a command and below; integer widths, lists, `KEY=VALUE`, URLs,
  or undecided, left to the program) and `Rule`s between options (`Command.rules`: `requires`,
  `conflicts`);
* `interpret c env argv` is the whole front end: an `Outcome` (run, help, version or a usage
  error at a subcommand path), with its exit code (`Outcome.exitCode?`) and its text
  (`Outcome.text`);
* `Command.usage`, `Command.help` and `errorText` are functions of the grammar, so help cannot
  drift from what the parser accepts.

## Conventions (the documented dialect)

* `--name` is a long option or flag; `--name=VALUE` and `--name VALUE` give a value (the next
  token is taken verbatim, even if it starts with `-`). An option with an *optional* value
  (`Opt.valueOptional`) takes it only after `=`; given bare it means `Opt.missing` if set
  (clap's `default_missing_value`). A *negatable* flag also reads `--no-name`.
* `-x…` is a single-dash token. If `x…` is a declared single-dash name it is that option
  (exact tokens: one letter as in `-o`, or several as in Binaryen's `-O2` and `-all`); its value
  is the next token. Otherwise it is a **cluster** of one-letter names (of options not marked
  `Opt.exact`, whose names are exact tokens only, like Binaryen's `-O`): `-vvx` is `-v -v -x`, and
  the first letter that takes a value takes the rest of the token (`-ofile`, `-o=file`, and
  `-vofile` is `-v -o file`), or the next token when nothing follows it.
* `--` ends option parsing: every later token is a positional argument;
* `-` alone, and every token not starting with `-`, is a word: a subcommand name when the
  command has subcommands, else a positional argument. Options may appear between positionals.
* Options belong to the command level they appear at; an option marked `global` is also
  accepted at every level below its own (after the subcommand name), and resolved at its own.

The normal form printed by `render` uses the first long name of each option (else its first
single-dash name), passes values as separate tokens (`--name=VALUE` for optional values), writes
`--no-name` for a negated flag, puts options before positionals and writes `--` before the
positionals exactly when one of them is not a word or the command has subcommands.

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

namespace Silmaril.Cli

/-! ## Values -/

/-- The type of an option value or a positional argument. -/
inductive ArgType where
  /-- any string -/
  | str
  /-- a file system path (any string; the type documents intent) -/
  | path
  /-- a natural number in decimal digits -/
  | nat
  /-- an integer: decimal digits with an optional leading `-` -/
  | int
  /-- one of the given strings -/
  | enum (choices : List String)
  deriving DecidableEq, Repr, Inhabited

/-- A typed value. Flags have the value `flag` once per occurrence, and `off` for a negated
occurrence (`--no-x`). -/
inductive Value where
  | str (s : String)
  | nat (n : Nat)
  | int (i : Int)
  | flag
  | off
  deriving DecidableEq, Repr, Inhabited

/-- Decimal digits after an accumulator. -/
def ArgType.digitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs => if c.isDigit then ArgType.digitsAux (10 * acc + (c.toNat - '0'.toNat)) cs else none

/-- A non-empty string of decimal digits. -/
def ArgType.parseNat (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | cs => ArgType.digitsAux 0 cs

/-- Decimal digits with an optional leading `-`. -/
def ArgType.parseInt (s : String) : Option Int :=
  match s.toList with
  | [] => none
  | ['-'] => none
  | '-' :: cs => (ArgType.digitsAux 0 cs).map fun n => -(n : Int)
  | cs => (ArgType.digitsAux 0 cs).map fun n => (n : Int)

/-- Parse a value of a type. -/
def ArgType.parse : ArgType → String → Option Value
  | .str, s => some (.str s)
  | .path, s => some (.str s)
  | .nat, s => (ArgType.parseNat s).map .nat
  | .int, s => (ArgType.parseInt s).map .int
  | .enum cs, s => if cs.contains s then some (.str s) else none

/-- The canonical spelling of a value (`ArgType.parse_show`: it parses back). -/
def Value.show : Value → String
  | .str s => s
  | .nat n => toString n
  | .int i => toString i
  | .flag => ""
  | .off => ""

/-- The values of a type. -/
def ArgType.Has : ArgType → Value → Prop
  | .str, .str _ => True
  | .path, .str _ => True
  | .nat, .nat _ => True
  | .int, .int _ => True
  | .enum cs, .str s => s ∈ cs
  | _, _ => False

/-- The metavariable shown for a type when none is given. -/
def ArgType.metavar : ArgType → String
  | .str => "VALUE"
  | .path => "PATH"
  | .nat => "N"
  | .int => "INT"
  | .enum _ => "VALUE"

/-- A phrase for error messages. -/
def ArgType.describe : ArgType → String
  | .str => "a string"
  | .path => "a path"
  | .nat => "a natural number"
  | .int => "an integer"
  | .enum cs => "one of " ++ ", ".intercalate cs

/-! ## Value checks and rules

Checks beyond an `ArgType` (integer widths, comma-separated lists, `KEY=VALUE`, URLs), as
value parsers of clap do them, and relations between the options of a command. A check may
leave a value **undecided** (`ValueCheck.external`: a file that must be readable, an SPDX
expression): the front end then runs the program, which decides. -/

namespace ValueCheck

/-- Split a character list at every `sep`. -/
def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOn sep cs
    else match splitOn sep cs with
      | [] => [[c]]
      | p :: ps => (c :: p) :: ps

/-- ASCII white space. -/
def isSpace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- Drop white space at both ends. -/
def trim (cs : List Char) : List Char :=
  ((cs.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- Combine verdicts: a rejection wins, then an undecided part, else accepted. -/
def allOk (vs : List (Option Bool)) : Option Bool :=
  if vs.contains (some false) then some false
  else if vs.all (· == some true) then some true else none

/-- Whether a character list starts with a URL scheme and `:`. -/
def hasScheme : List Char → Bool
  | c :: cs => c.isAlpha && go cs
  | [] => false
where
  go : List Char → Bool
    | [] => false
    | ':' :: _ => true
    | c :: cs => (c.isAlphanum || c = '+' || c = '-' || c = '.') && go cs

end ValueCheck

/-- A value check, as a value parser of clap would do it. -/
inductive ValueCheck where
  /-- Rust's `uN::from_str`: an optional `+`, decimal digits, below `2 ^ bits`. -/
  | uint (bits : Nat)
  /-- one of the given words (not shown in help; case-insensitive when `ci`) -/
  | oneOf (choices : List String) (ci : Bool := false)
  /-- parts separated by `sep`, each passing the check; with `skipEmpty` the parts are
  trimmed and empty ones skipped (wasm-tools' `--features`) -/
  | listOf (sep : Char) (skipEmpty : Bool) (c : ValueCheck)
  /-- an optional leading `-` (a feature to disable), then the check -/
  | negatable (c : ValueCheck)
  /-- `KEY=VALUE`: some `=` (Rust's `split_once('=')`) -/
  | keyValue
  /-- exactly `n` parts separated by `sep` -/
  | tuple (n : Nat) (sep : Char) (c : ValueCheck)
  /-- an absolute URL: rejected without a scheme (`[A-Za-z][A-Za-z0-9+.-]*:`), otherwise left
  to the URL parser (undecided) -/
  | absUrl
  /-- decided outside the specification (a file to read, an SPDX expression) -/
  | external (what : String)
  deriving Repr, Inhabited, DecidableEq

/-- **The check**: `some true` accepted, `some false` rejected, `none` undecided. -/
def ValueCheck.eval : ValueCheck → List Char → Option Bool
  | .uint bits, cs =>
    let ds := match cs with
      | '+' :: r => r
      | r => r
    some (match ArgType.digitsAux 0 ds, ds with
      | _, [] => false
      | some n, _ => decide (n < 2 ^ bits)
      | none, _ => false)
  | .oneOf choices ci, cs =>
    some (choices.any fun w =>
      if ci then w.toList.map Char.toLower == cs.map Char.toLower else w.toList == cs)
  | .listOf sep skipEmpty c, cs =>
    let parts := (ValueCheck.splitOn sep cs).map (if skipEmpty then ValueCheck.trim else id)
    let parts := if skipEmpty then parts.filter (!·.isEmpty) else parts
    ValueCheck.allOk (parts.map c.eval)
  | .negatable c, '-' :: cs => c.eval cs
  | .negatable c, cs => c.eval cs
  | .keyValue, cs => some (cs.contains '=')
  | .tuple n sep c, cs =>
    let parts := ValueCheck.splitOn sep cs
    if parts.length = n then ValueCheck.allOk (parts.map c.eval) else some false
  | .absUrl, cs => if ValueCheck.hasScheme cs then none else some false
  | .external _, _ => none

/-- A relation between two options (by `id`) of one command. -/
inductive Rule where
  /-- giving `a` needs `b` (clap's `requires`) -/
  | requires (a b : String)
  /-- `a` and `b` exclude each other (clap's `conflicts_with`) -/
  | conflicts (a b : String)
  deriving Repr, Inhabited, DecidableEq

/-! ## Grammars -/

/-- An option or a flag. `id` names it in `Matches`; `long` are its `--` names (the first one is
canonical), `short` its single-dash names (one letter: clustered; several: an exact token).
`arg = none` makes a flag. -/
structure Opt where
  id : String
  long : List String := [id]
  short : List String := []
  arg : Option ArgType := none
  metavar : String := ""
  help : String := ""
  /-- used when the option is absent and the environment variable is unset -/
  default : Option String := none
  /-- an environment variable read when the option is absent -/
  env : Option String := none
  /-- absent, without environment variable or default, is an error -/
  required : Bool := false
  /-- may occur more than once (a counted flag, or a list of values) -/
  repeated : Bool := false
  /-- the value is optional and given only attached (`--name=V`, `-xV`) -/
  valueOptional : Bool := false
  /-- the value a bare occurrence of an optional value means (clap's
  `default_missing_value`); without it a bare occurrence resolves to `flag` -/
  missing : Option String := none
  /-- a flag that also reads `--no-NAME` (value `off`) -/
  negatable : Bool := false
  /-- also accepted at every level below (clap's global arguments) -/
  global : Bool := false
  /-- the single-dash names are exact tokens only, never letters of a cluster, even when one
  letter long (Binaryen's `-O`) -/
  exact : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Whether the option takes a value. -/
def Opt.takesValue (o : Opt) : Bool := o.arg.isSome

/-- How many positional arguments a `Pos` takes. -/
inductive Arity where
  | one
  | optional
  | many
  | atLeastOne
  deriving DecidableEq, Repr, Inhabited

/-- A positional argument. Positionals are bound left to right: `one` takes a word, `optional`
one if there is one, `many` and `atLeastOne` all remaining words. -/
structure Pos where
  id : String
  type : ArgType := .str
  arity : Arity := .one
  metavar : String := ""
  help : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- A command: options, positionals and subcommands. The root's `name` is the program name. -/
structure Command where
  name : String
  aliases : List String := []
  about : String := ""
  opts : List Opt := []
  pos : List Pos := []
  subs : List Command := []
  /-- a command with subcommands must be given one -/
  subRequired : Bool := true
  /-- documented exit codes (for help; their meaning is part of the behaviour specification) -/
  exits : List (Nat × String) := []
  /-- the version printed for `--version` (root only) -/
  version : Option String := none
  /-- value checks by option or positional `id`, in force here and below (the deepest
  command's check wins) -/
  checks : List (String × ValueCheck) := []
  /-- relations between the options of this command (`requires`, `conflicts`) -/
  rules : List Rule := []
  deriving Inhabited

/-- The words selecting a subcommand. -/
def Command.names (c : Command) : List String := c.name :: c.aliases

/-- The options `c` passes down to its subcommands. -/
def Command.globals (c : Command) : List Opt := c.opts.filter (·.global)

/-- `c` with the options `inh` (inherited from above) after its own. -/
def Command.inherit (c : Command) (inh : List Opt) : Command := { c with opts := c.opts ++ inh }

/-- **The subcommand `s` of `c` as the parser sees it**: its own options, then the global
options of `c` (its own and those `c` inherited). -/
def Command.child (c s : Command) : Command := s.inherit c.globals

/-! ## Lookup -/

/-- The first element of `l` with `k` among its keys. -/
def lookupKey {α : Type} (keys : α → List String) (l : List α) (k : String) : Option α :=
  l.find? fun a => (keys a).contains k

/-- The option with long name `n`. -/
def findLong (os : List Opt) (n : String) : Option Opt := lookupKey Opt.long os n

/-- The option with single-dash name `n`. -/
def findShort (os : List Opt) (n : String) : Option Opt := lookupKey Opt.short os n

/-- The options whose one-letter names may be letters of a cluster (not `exact`). -/
def clusterOpts (os : List Opt) : List Opt := os.filter (!·.exact)

/-- The option with identifier `k`. -/
def findId (os : List Opt) (k : String) : Option Opt := lookupKey (fun o => [o.id]) os k

/-- The subcommand named `w` (or with alias `w`). -/
def findSub (cs : List Command) (w : String) : Option Command := lookupKey Command.names cs w

/-- Follow subcommand words from a command (the commands as the parser sees them). -/
def Command.walk : Command → List String → Option Command
  | c, [] => some c
  | c, w :: ws => (findSub c.subs w).bind fun s => (c.child s).walk ws

/-! ## Tokens -/

/-- The lexical class of one argument. -/
inductive Tok where
  /-- `--` -/
  | dashdash
  /-- `--name` or `--name=value` -/
  | long (name : String) (value : Option String)
  /-- `-name` -/
  | short (name : String)
  /-- anything else, including `-` -/
  | word (s : String)
  deriving DecidableEq, Repr

/-- Split at the first `=`. -/
def splitEq : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | '=' :: r => ([], some r)
  | c :: r => match splitEq r with
    | (a, v) => (c :: a, v)

/-- Classify one argument. -/
def classify (s : String) : Tok :=
  match s.toList with
  | ['-', '-'] => .dashdash
  | '-' :: '-' :: n => match splitEq n with
    | (a, v) => .long (String.ofList a) (v.map String.ofList)
  | ['-'] => .word s
  | '-' :: n => .short (String.ofList n)
  | _ => .word s

/-- Whether an argument is a word (not `--`, not option-like). -/
def isWord (s : String) : Bool := classify s == .word s

/-- `n` without a leading `no-`. -/
def stripNo (n : String) : Option String :=
  match n.toList with
  | 'n' :: 'o' :: '-' :: m => some (String.ofList m)
  | _ => none

/-! ## Invocations: the parse tree -/

/-- What one occurrence of an option gave. -/
inductive Given where
  /-- a flag, or an option with an optional value given without one -/
  | on
  /-- a negated flag, `--no-name` -/
  | off
  /-- a value -/
  | val (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- What one command level of a command line said: the options in order of appearance (by
`id`, with what they gave) and the positional words. -/
structure Frame where
  cmd : String
  opts : List (String × Given) := []
  args : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- A parsed command line: the root's frame, then one frame per subcommand. -/
abbrev Invocation := List Frame

/-- Usage errors. -/
inductive ArgError where
  | unknownOption (token : String)
  | missingValue (token : String)
  | unexpectedValue (token : String)
  | unknownCommand (word : String)
  | missingCommand (cmd : String)
  | missingArgument (id : String)
  | extraArgument (word : String)
  | badValue (id : String) (value : String) (type : ArgType)
  | repeated (id : String)
  | missingOption (id : String)
  /-- a value its `ValueCheck` rejects -/
  | rejected (id : String) (value : String)
  /-- a broken `Rule.requires` -/
  | requires (id need : String)
  /-- a broken `Rule.conflicts` -/
  | conflicts (id other : String)
  deriving DecidableEq, Repr, Inhabited

/-- A usage error with the subcommand path (below the command at hand) where it was found. -/
abbrev Located := List String × ArgError

/-! ### Reading one option token -/

/-- What reading an option token gives: occurrences, and whether the next token was consumed
as a value. -/
abbrev Read := List (String × Given) × Bool

/-- A value-taking option given without an attached value: an optional value is absent, else
the next token is the value. -/
def valueFromNext (o : Opt) (t : String) (next : Option String) : Except ArgError Read :=
  if o.valueOptional then .ok ([(o.id, .on)], false) else
  match next with
  | some x => .ok ([(o.id, .val x)], true)
  | none => .error (.missingValue t)

/-- A long name `n` that is no option's: `--no-m` for a negatable flag `m`, else unknown. -/
def readNo (os : List Opt) (t n : String) (v : Option String) : Except ArgError Read :=
  match (stripNo n).bind (findLong os) with
  | some o =>
    if o.negatable && !o.takesValue then
      match v with
      | none => .ok ([(o.id, .off)], false)
      | some _ => .error (.unexpectedValue t)
    else .error (.unknownOption t)
  | none => .error (.unknownOption t)

/-- Read `--n` or `--n=v` (`t` the whole token, `next` the token after it). -/
def readLong (os : List Opt) (t n : String) (v : Option String) (next : Option String) :
    Except ArgError Read :=
  match findLong os n with
  | some o =>
    match o.takesValue, v with
    | false, none => .ok ([(o.id, .on)], false)
    | false, some _ => .error (.unexpectedValue t)
    | true, some x => .ok ([(o.id, .val x)], false)
    | true, none => valueFromNext o t next
  | none => readNo os t n v

/-- A value attached to a one-letter name in a cluster (`-ofile`, `-o=file`). -/
def attachedValue (o : Opt) : List Char → Read
  | '=' :: v => ([(o.id, .val (String.ofList v))], false)
  | v => ([(o.id, .val (String.ofList v))], false)

/-- Read a cluster of one-letter names (the characters after `-`; `exact` options are not
letters of clusters). -/
def readCluster (os : List Opt) (t : String) (next : Option String) :
    List Char → Except ArgError Read
  | [] => .ok ([], false)
  | ch :: r =>
    match findShort (clusterOpts os) (String.singleton ch) with
    | none => .error (.unknownOption t)
    | some o =>
      if o.takesValue then
        if r.isEmpty then valueFromNext o t next else .ok (attachedValue o r)
      else (readCluster os t next r).map fun p => ((o.id, .on) :: p.1, p.2)

/-- Read `-n`: an exact single-dash name, else a cluster. -/
def readShort (os : List Opt) (t n : String) (next : Option String) : Except ArgError Read :=
  match findShort os n with
  | some o => if o.takesValue then valueFromNext o t next else .ok ([(o.id, .on)], false)
  | none => readCluster os t next n.toList

/-- **Read an option token** `t`, followed by `next`, with the option table `os`. -/
def readOpt (os : List Opt) (t : String) (next : Option String) : Except ArgError Read :=
  match classify t with
  | .long n v => readLong os t n v next
  | .short n => readShort os t n next
  | _ => .error (.unknownOption t)

/-! ### The scanner -/

/-- Prepend option occurrences to the current frame of a result. -/
def consOpts (ps : List (String × Given)) :
    Except Located (Frame × Invocation) → Except Located (Frame × Invocation) :=
  Except.map fun r => ({ r.1 with opts := ps ++ r.1.opts }, r.2)

/-- Prepend a positional word to the current frame of a result. -/
def consArg (w : String) :
    Except Located (Frame × Invocation) → Except Located (Frame × Invocation) :=
  Except.map fun r => ({ r.1 with args := w :: r.1.args }, r.2)

/-- The result of the subcommand `s` as part of the result of `c`: a frame for `c`, errors
located below `s`. -/
def underSub (c : Command) (n : String) :
    Except Located (Frame × Invocation) → Except Located (Frame × Invocation)
  | .ok r => .ok ({ cmd := c.name }, r.1 :: r.2)
  | .error (p, e) => .error (n :: p, e)

/-- The scanner at command `c`: the frame of `c` and the frames below it. -/
def scanAux (c : Command) : List String → Except Located (Frame × Invocation)
  | [] => .ok ({ cmd := c.name }, [])
  | t :: rest =>
    match classify t with
    | .dashdash => .ok ({ cmd := c.name, args := rest }, [])
    | .word w =>
      match c.subs.isEmpty with
      | true => consArg w (scanAux c rest)
      | false =>
        match findSub c.subs w with
        | none => .error ([], .unknownCommand w)
        | some s => underSub c s.name (scanAux (c.child s) rest)
    | _ =>
      match readOpt c.opts t rest.head? with
      | .error e => .error ([], e)
      | .ok (ps, false) => consOpts ps (scanAux c rest)
      | .ok (ps, true) =>
        match rest with
        | [] => .error ([], .missingValue t)
        | _ :: rest' => consOpts ps (scanAux c rest')

/-- **The parser**: an argument vector (without the program name) to an invocation. -/
def scan (c : Command) (argv : List String) : Except Located Invocation :=
  (scanAux c argv).map fun r => r.1 :: r.2

/-! ## The grammar as an inductive relation

`Scans c argv (f, fs)`: one rule per convention, the reading of one option token by `readOpt`
(characterized in `Silmaril.Cli.Args.Thms`). `Silmaril.Cli.Args.Thms` proves
`scanAux c argv = .ok r ↔ Scans c argv r`. -/

/-- The grammar of command lines of `c`. -/
inductive Scans : Command → List String → Frame × Invocation → Prop where
  | nil (c) : Scans c [] ({ cmd := c.name }, [])
  | dashdash {c t rest} : classify t = .dashdash →
      Scans c (t :: rest) ({ cmd := c.name, args := rest }, [])
  | opt {c t rest ps f fs} : readOpt c.opts t rest.head? = .ok (ps, false) →
      Scans c rest (f, fs) → Scans c (t :: rest) ({ f with opts := ps ++ f.opts }, fs)
  | optNext {c t x rest ps f fs} : readOpt c.opts t (some x) = .ok (ps, true) →
      Scans c rest (f, fs) → Scans c (t :: x :: rest) ({ f with opts := ps ++ f.opts }, fs)
  | arg {c t w rest f fs} : classify t = .word w → c.subs.isEmpty = true → Scans c rest (f, fs) →
      Scans c (t :: rest) ({ f with args := w :: f.args }, fs)
  | sub {c t w s rest g gs} : classify t = .word w → c.subs.isEmpty = false →
      findSub c.subs w = some s → Scans (c.child s) rest (g, gs) →
      Scans c (t :: rest) ({ cmd := c.name }, g :: gs)

/-! ## Well-formed grammars -/

/-- A long name the scanner reads back: non-empty, without `=`. -/
def LongName (n : String) : Prop := n ≠ "" ∧ '=' ∉ n.toList

/-- A single-dash name the scanner reads back: non-empty, not starting with `-`. -/
def ShortName (n : String) : Prop := n ≠ "" ∧ n.toList.head? ≠ some '-'

instance (n : String) : Decidable (LongName n) := by unfold LongName; infer_instance
instance (n : String) : Decidable (ShortName n) := by unfold ShortName; infer_instance

/-- The conditions on one option of a level with option table `os`. -/
def Opt.LocalWF (os : List Opt) (o : Opt) : Prop :=
  o.long ++ o.short ≠ [] ∧ (∀ n ∈ o.long, LongName n) ∧ (∀ n ∈ o.short, ShortName n) ∧
    (o.valueOptional = true → o.takesValue = true ∧ o.long ≠ []) ∧
    (o.negatable = true → o.takesValue = false ∧ o.long ≠ [] ∧
      ∀ n ∈ o.long, findLong os ("no-" ++ n) = none)

instance (os : List Opt) (o : Opt) : Decidable (o.LocalWF os) := by
  unfold Opt.LocalWF; infer_instance

/-- The conditions on one level (as the parser sees it, inherited options included): distinct
identifiers and names, names that the scanner reads back, every option has a name, optional
values and negations can be rendered, subcommand names are words. -/
def Command.LocalWF (c : Command) : Prop :=
  (c.opts.map (·.id)).Nodup ∧ (c.opts.flatMap (·.long)).Nodup ∧
    (c.opts.flatMap (·.short)).Nodup ∧ (c.subs.flatMap Command.names).Nodup ∧
    (∀ o ∈ c.opts, o.LocalWF c.opts) ∧ (∀ s ∈ c.subs, classify s.name = .word s.name)

instance (c : Command) : Decidable c.LocalWF := by
  unfold Command.LocalWF; infer_instance

mutual
/-- Well-formedness at every level, below inherited options `inh` (decidable). -/
def Command.wfIn (inh : List Opt) : Command → Bool
  | c@⟨_, _, _, os, _, subs, _, _, _, _, _⟩ =>
    decide (c.inherit inh).LocalWF && Command.wfInAll ((os ++ inh).filter (·.global)) subs
/-- `wfIn` of every command of a list. -/
def Command.wfInAll (inh : List Opt) : List Command → Bool
  | [] => true
  | s :: ss => s.wfIn inh && Command.wfInAll inh ss
end

/-- A well-formed grammar (checked by `decide`). -/
def Command.WF (c : Command) : Prop := c.wfIn [] = true

instance (c : Command) : Decidable c.WF := by
  unfold Command.WF; infer_instance

/-- Well-formedness of the tree as the parser sees it (`Command.WF.good`). -/
inductive Command.Good : Command → Prop where
  | mk {c : Command} : c.LocalWF → (∀ s ∈ c.subs, (c.child s).Good) → c.Good

/-! ## Rendering: the normal form -/

/-- The canonical spelling: the first long name, else the first single-dash name. -/
def Opt.spelling (o : Opt) : String :=
  match o.long, o.short with
  | n :: _, _ => "--" ++ n
  | [], s :: _ => "-" ++ s
  | [], [] => "--" ++ o.id

/-- What one occurrence gave, in normal form. -/
def renderGiven (o : Opt) : Given → List String
  | .on => [o.spelling]
  | .off => ["--no-" ++ o.long.headD o.id]
  | .val s => if o.valueOptional then ["--" ++ o.long.headD o.id ++ "=" ++ s] else [o.spelling, s]

/-- One option occurrence, in normal form. -/
def renderOpt (os : List Opt) (p : String × Given) : List String :=
  match findId os p.1 with
  | some o => renderGiven o p.2
  | none => []

/-- The positional words, guarded by `--` when needed. -/
def renderArgs (c : Command) (args : List String) : List String :=
  if args.isEmpty then []
  else if !c.subs.isEmpty || !args.all isWord then "--" :: args else args

/-- **The renderer**: an invocation to an argument vector in normal form. -/
def render (c : Command) : Invocation → List String
  | [] => []
  | f :: rest => f.opts.flatMap (renderOpt c.opts) ++
    match rest with
    | [] => renderArgs c f.args
    | g :: _ =>
      match findSub c.subs g.cmd with
      | some s => g.cmd :: render (c.child s) rest
      | none => []

/-- The normal form of an argument vector (when it parses). -/
def normalize (c : Command) (argv : List String) : Except Located (List String) :=
  (scan c argv).map (render c)

/-- Whether an occurrence fits an option. -/
def Opt.accepts (o : Opt) : Given → Bool
  | .on => !o.takesValue || o.valueOptional
  | .off => !o.takesValue && o.negatable
  | .val _ => o.takesValue

/-- A frame that `c` could have produced. -/
def FrameOk (c : Command) (f : Frame) : Prop :=
  f.cmd = c.name ∧ ∀ p ∈ f.opts, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true

/-- Invocations of `c`: the frames follow subcommands, and only the last frame has positional
words. -/
def Valid : Command → Invocation → Prop
  | _, [] => False
  | c, f :: rest => FrameOk c f ∧
    match rest with
    | [] => True
    | g :: _ => f.args = [] ∧ ∃ s, findSub c.subs g.cmd = some s ∧ Valid (c.child s) rest

/-! ## Resolution: typed matches -/

/-- The typed result: the subcommand path below the root and the values of each option and
positional, by `id` (deepest level first). -/
structure Matches where
  path : List String := []
  values : List (String × List Value) := []
  deriving DecidableEq, Repr, Inhabited

namespace Matches

/-- All values bound to `id`, at every level. -/
def get (m : Matches) (id : String) : List Value :=
  (m.values.filter (·.1 == id)).flatMap (·.2)

/-- Whether a flag (or option) occurred. -/
def flag (m : Matches) (id : String) : Bool := !(m.get id).isEmpty

/-- How often a flag occurred (`-v -v`, `-vv`). -/
def count (m : Matches) (id : String) : Nat := (m.get id).length

/-- A negatable flag: the last of `--x` and `--no-x`, else `dflt`. -/
def switch (m : Matches) (id : String) (dflt : Bool) : Bool :=
  match (m.get id).getLast? with
  | some .off => false
  | some _ => true
  | none => dflt

/-- The string values of `id`. -/
def strs (m : Matches) (id : String) : List String :=
  (m.get id).filterMap fun | .str s => some s | _ => none

/-- The first string value of `id`. -/
def str? (m : Matches) (id : String) : Option String := (m.strs id).head?

/-- The first natural number value of `id`. -/
def nat? (m : Matches) (id : String) : Option Nat :=
  ((m.get id).filterMap fun | .nat n => some n | _ => none).head?

/-- The first integer value of `id`. -/
def int? (m : Matches) (id : String) : Option Int :=
  ((m.get id).filterMap fun | .int i => some i | _ => none).head?

end Matches

/-- Parse a value or fail with `badValue`. -/
def parseAs (id : String) (t : ArgType) (s : String) : Except ArgError Value :=
  match t.parse s with
  | some v => .ok v
  | none => .error (.badValue id s t)

/-- What the occurrences of a frame gave for the identifier `k`. -/
def occOf (f : Frame) (k : String) : List Given :=
  f.opts.filterMap fun p => if p.1 == k then some p.2 else none

/-- The occurrences of an option declared at the level of `f`: in `f`, and, for a global
option, in the frames below. -/
def occIn (o : Opt) (f : Frame) (rest : Invocation) : List Given :=
  occOf f o.id ++ if o.global then rest.flatMap (occOf · o.id) else []

/-- The value of one occurrence; a bare occurrence of an optional value means `missing`, if
given. -/
def givenValue (id : String) (t : ArgType) (missing : Option String := none) :
    Given → Except ArgError Value
  | .val s => parseAs id t s
  | .on => match missing with
    | some d => parseAs id t d
    | none => .ok .flag
  | .off => .ok .off

/-- The values of one option from its occurrences: command line, else environment, else
default. -/
def resolveOpt (env : String → Option String) (occ : List Given) (o : Opt) :
    Except ArgError (String × List Value) :=
  if !o.repeated && occ.length > 1 then .error (.repeated o.id) else
  match o.arg with
  | none => .ok (o.id, occ.map fun | .off => .off | _ => .flag)
  | some t =>
    if occ.isEmpty then
      match o.env.bind env, o.default with
      | some s, _ => (parseAs o.id t s).map fun v => (o.id, [v])
      | none, some s => (parseAs o.id t s).map fun v => (o.id, [v])
      | none, none => if o.required then .error (.missingOption o.id) else .ok (o.id, [])
    else (occ.mapM (givenValue o.id t o.missing)).map fun vs => (o.id, vs)

/-- Bind positional words to positionals, left to right. -/
def bindPos : List Pos → List String → Except ArgError (List (String × List Value))
  | [], [] => .ok []
  | [], w :: _ => .error (.extraArgument w)
  | p :: ps, ws =>
    match p.arity, ws with
    | .one, [] => .error (.missingArgument p.id)
    | .atLeastOne, [] => .error (.missingArgument p.id)
    | .one, w :: ws' => do
      let v ← parseAs p.id p.type w
      let r ← bindPos ps ws'
      pure ((p.id, [v]) :: r)
    | .optional, w :: ws' => do
      let v ← parseAs p.id p.type w
      let r ← bindPos ps ws'
      pure ((p.id, [v]) :: r)
    | .optional, [] => do
      let r ← bindPos ps []
      pure ((p.id, []) :: r)
    | .many, ws => do
      let vs ← ws.mapM (parseAs p.id p.type)
      let r ← bindPos ps []
      pure ((p.id, vs) :: r)
    | .atLeastOne, ws => do
      let vs ← ws.mapM (parseAs p.id p.type)
      let r ← bindPos ps []
      pure ((p.id, vs) :: r)

/-- Locate an error at this level. -/
def here {α : Type} : Except ArgError α → Except Located α
  | .ok a => .ok a
  | .error e => .error ([], e)

/-- Locate an error below the subcommand `n`. -/
def below {α : Type} (n : String) : Except Located α → Except Located α
  | .ok a => .ok a
  | .error (p, e) => .error (n :: p, e)

/-- Resolve the frames below command `c` (its own options; inherited ones are resolved where
they are declared). -/
def resolveAux (env : String → Option String) :
    Command → Invocation → Except Located Matches
  | _, [] => .ok {}
  | c, f :: rest => do
    let mine ← here (c.opts.mapM fun o => resolveOpt env (occIn o f rest) o)
    match rest with
    | [] =>
      if !c.subs.isEmpty && c.subRequired && f.args.isEmpty then
        .error ([], .missingCommand c.name)
      else
        let ps ← here (bindPos c.pos f.args)
        pure { path := [], values := ps ++ mine }
    | g :: _ =>
      match findSub c.subs g.cmd with
      | none => .error ([], .unknownCommand g.cmd)
      | some s => do
        let m ← below s.name (resolveAux env s rest)
        pure { path := g.cmd :: m.path, values := m.values ++ mine }

/-- **Resolution**: types, environment variables, defaults and positionals. -/
def resolve (c : Command) (env : String → Option String) (fs : Invocation) :
    Except Located Matches :=
  resolveAux env c fs

/-! ## Help, version and the outcome -/

/-- The conventional help flag (`id` `help`), added by `Command.withHelp` (global: every
subcommand accepts it). -/
def helpOpt : Opt := { id := "help", short := ["h"], help := "Print help", global := true }

/-- The conventional version flag (`id` `version`), added by `Command.withVersion`. -/
def versionOpt : Opt := { id := "version", short := ["V"], help := "Print version" }

/-- The path (root name first) to the first frame asking for help. -/
def helpPath : Invocation → List String → Option (List String)
  | [], _ => none
  | f :: rest, acc =>
    if f.opts.any (·.1 == "help") then some (acc ++ [f.cmd]) else helpPath rest (acc ++ [f.cmd])

/-- What a command line asks for. -/
inductive Outcome where
  /-- run the program with these matches -/
  | run (m : Matches)
  /-- print the help of the command at this path (root name first) and exit 0 -/
  | help (path : List String)
  /-- print the version and exit 0 -/
  | version (v : String)
  /-- print the error and the usage of the command at this path (root name first) to stderr
  and exit 2 -/
  | error (path : List String) (e : ArgError)
  deriving DecidableEq, Repr

/-- A located error as an outcome. -/
def Outcome.ofLocated (c : Command) : Located → Outcome
  | (p, e) => .error (c.name :: p) e

/-! ### Value checks and rules

After parsing, the front end checks (in clap's order) the value of every occurrence as it
is read (`badOccurrence`: its type, then its `ValueCheck`), resolves, then checks the rules
of the selected command and the checks of every resolved string value (defaults, environment
variables and positionals included). -/

/-- The value checks in force at the end of a subcommand path, deepest first. -/
def Command.scopeAt : Command → List String → List (String × ValueCheck)
  | c, [] => c.checks
  | c, w :: ws =>
    match findSub c.subs w with
    | some s => (c.child s).scopeAt ws ++ c.checks
    | none => c.checks

/-- The rules of the command at a subcommand path. -/
def Command.rulesAt (c : Command) (path : List String) : List Rule :=
  ((c.walk path).map (·.rules)).getD []

/-- Whether a value of `o` passes its type and the check of `o.id` in `scope`. -/
def valueOk (scope : List (String × ValueCheck)) (o : Opt) (x : String) : Bool :=
  (match o.arg with
    | some ty => (ty.parse x).isSome
    | none => true) &&
  (match scope.lookup o.id with
    | some ck => ck.eval x.toList != some false
    | none => true)

/-- The first occurrence value its type or its check rejects, in the order of the command line
(clap checks values as it reads them), with the subcommand path and the option. `scope`: the
checks in force above. -/
def badOccurrence (scope : List (String × ValueCheck)) :
    Command → Invocation → Option (List String × Opt × String)
  | _, [] => none
  | c, f :: rest =>
    let sc := c.checks ++ scope
    let bad := f.opts.findSome? fun (id, v) =>
      match v, findId c.opts id with
      | .val x, some o => if valueOk sc o x then none else some (o, x)
      | _, _ => none
    match bad with
    | some r => some ([], r)
    | none =>
      match rest with
      | [] => none
      | g :: _ =>
        match findSub c.subs g.cmd with
        | some s => (badOccurrence sc (c.child s) rest).map fun r => (g.cmd :: r.1, r.2)
        | none => none

/-- Whether option `id` occurs in an invocation. -/
def present (fs : Invocation) (id : String) : Bool := fs.any fun f => f.opts.any (·.1 == id)

/-- Whether an invocation breaks a rule. -/
def Rule.broken (fs : Invocation) : Rule → Bool
  | .requires a b => present fs a && !present fs b
  | .conflicts a b => present fs a && present fs b

/-- The usage error of a broken rule. -/
def Rule.error : Rule → ArgError
  | .requires a b => .requires a b
  | .conflicts a b => .conflicts a b

/-- The verdicts of the checks in force on the string values of the matches, with the `id`s
and the values. -/
def checkMatches (c : Command) (m : Matches) : List ((String × String) × Option Bool) :=
  let sc := c.scopeAt m.path
  m.values.flatMap fun (id, vs) =>
    match sc.lookup id with
    | none => []
    | some ck => vs.filterMap fun
      | .str s => some ((id, s), ck.eval s.toList)
      | _ => none

/-- What the checks say about a parsed invocation. -/
inductive Judgement where
  /-- an occurrence's value fails its type or its check -/
  | badValue (path : List String) (o : Opt) (x : String)
  /-- resolution fails -/
  | unresolved (l : Located)
  /-- a rule of the selected command is broken -/
  | broken (path : List String) (r : Rule)
  /-- a resolved value fails its check -/
  | rejected (path : List String) (id v : String)
  /-- runs, unless the program rejects the value of `id`, which the checks leave undecided -/
  | undecided (m : Matches) (id : String)
  /-- runs -/
  | ok (m : Matches)
  deriving Repr, DecidableEq

/-- **The checks after parsing**: occurrence values, resolution, rules, resolved values. -/
def judge (c : Command) (env : String → Option String) (fs : Invocation) : Judgement :=
  match badOccurrence [] c fs with
  | some (p, o, x) => .badValue p o x
  | none =>
    match resolve c env fs with
    | .error l => .unresolved l
    | .ok m =>
      match (c.rulesAt m.path).find? (·.broken fs) with
      | some r => .broken m.path r
      | none =>
        let vs := checkMatches c m
        match vs.find? (·.2 == some false) with
        | some ((id, v), _) => .rejected m.path id v
        | none =>
          match vs.find? (·.2 == none) with
          | some ((id, _), _) => .undecided m id
          | none => .ok m

/-- The usage error of a value its type or its check rejects. -/
def Opt.valueError (o : Opt) (x : String) : ArgError :=
  match o.arg with
  | some ty => if (ty.parse x).isSome then .rejected o.id x else .badValue o.id x ty
  | none => .rejected o.id x

/-- The checks after parsing, as an outcome: an undecided value runs (the program decides). -/
def resolveOutcome (c : Command) (env : String → Option String) (fs : Invocation) : Outcome :=
  match judge c env fs with
  | .badValue p o x => .error (c.name :: p) (o.valueError x)
  | .unresolved l => Outcome.ofLocated c l
  | .broken p r => .error (c.name :: p) r.error
  | .rejected p id v => .error (c.name :: p) (.rejected id v)
  | .undecided m _ => .run m
  | .ok m => .run m

/-- **The front end**: everything a program does with its arguments before its own work. -/
def interpret (c : Command) (env : String → Option String) (argv : List String) : Outcome :=
  match scan c argv with
  | .error l => Outcome.ofLocated c l
  | .ok fs =>
    match helpPath fs [] with
    | some p => .help p
    | none =>
      match c.version, fs with
      | some v, f :: _ =>
        if f.opts.any (·.1 == "version") then .version v else resolveOutcome c env fs
      | _, _ => resolveOutcome c env fs

/-- The exit code the front end decides: `none` when the program runs. Usage errors exit 2
(the convention of clap and getopt-based tools). -/
def Outcome.exitCode? : Outcome → Option Nat
  | .run _ => none
  | .help _ => some 0
  | .version _ => some 0
  | .error _ _ => some 2

/-! ### Text -/

/-- An aligned two-column table, each line `"  " ++ left ++ …`. -/
def helpTable (rows : List (String × String)) : List String :=
  let w := rows.foldl (fun m r => max m r.1.length) 0
  rows.map fun r => "  " ++ r.1 ++ (if r.2.isEmpty then "" else
    "".pushn ' ' (w - r.1.length) ++ "  " ++ r.2)

/-- A titled section, empty when there are no rows. -/
def helpSection (title : String) (rows : List (String × String)) : List String :=
  if rows.isEmpty then [] else ["", title] ++ helpTable rows

/-- The metavariable of an option. -/
def Opt.metavarOr (o : Opt) : String :=
  if o.metavar.isEmpty then (o.arg.map ArgType.metavar).getD "" else o.metavar

/-- `-o, --output <PATH>`, `--color[=<WHEN>]`, `--[no-]color` -/
def Opt.synopsis (o : Opt) : String :=
  ", ".intercalate (o.short.map ("-" ++ ·) ++
      o.long.map (fun n => (if o.negatable then "--[no-]" else "--") ++ n)) ++
    (if !o.takesValue then "" else if o.valueOptional then "[=<" ++ o.metavarOr ++ ">]"
      else " <" ++ o.metavarOr ++ ">")

/-- The bracketed notes after an option's help. -/
def Opt.notes (o : Opt) : String :=
  let ns := (match o.arg with
      | some (.enum cs) => ["[possible values: " ++ ", ".intercalate cs ++ "]"]
      | _ => []) ++
    (match o.default with | some d => ["[default: " ++ d ++ "]"] | none => []) ++
    (match o.env with | some e => ["[env: " ++ e ++ "]"] | none => []) ++
    (if o.required then ["[required]"] else []) ++
    (if o.repeated then ["[repeatable]"] else [])
  " ".intercalate ns

/-- The help column of an option. -/
def Opt.helpText (o : Opt) : String :=
  if o.notes.isEmpty then o.help else if o.help.isEmpty then o.notes else o.help ++ " " ++ o.notes

/-- The metavariable of a positional. -/
def Pos.metavarOr (p : Pos) : String := if p.metavar.isEmpty then p.id.toUpper else p.metavar

/-- `<IN>`, `[IN]`, `[IN]...`, `<IN>...` -/
def Pos.synopsis (p : Pos) : String :=
  match p.arity with
  | .one => "<" ++ p.metavarOr ++ ">"
  | .optional => "[" ++ p.metavarOr ++ "]"
  | .many => "[" ++ p.metavarOr ++ "]..."
  | .atLeastOne => "<" ++ p.metavarOr ++ ">..."

/-- The usage line of `c`, reached by `path` (root name first). -/
def Command.usage (c : Command) (path : List String) : String :=
  "Usage: " ++ " ".intercalate (path ++
    (if c.opts.isEmpty then [] else ["[OPTIONS]"]) ++
    (c.opts.filter (·.required)).map (fun o => o.spelling ++ " <" ++ o.metavarOr ++ ">") ++
    c.pos.map Pos.synopsis ++
    (if c.subs.isEmpty then [] else if c.subRequired then ["<COMMAND>"] else ["[COMMAND]"]))

/-- The help of `c` as lines. -/
def Command.helpLines (c : Command) (path : List String) : List String :=
  (if c.about.isEmpty then [] else [c.about, ""]) ++ [c.usage path] ++
    helpSection "Commands:" (c.subs.map fun s => (s.name, s.about)) ++
    helpSection "Arguments:" (c.pos.map fun p => (p.synopsis, p.help)) ++
    helpSection "Options:" (c.opts.map fun o => (o.synopsis, o.helpText)) ++
    helpSection "Exit status:" (c.exits.map fun e => (toString e.1, e.2))

/-- The help text of `c`. -/
def Command.help (c : Command) (path : List String) : String :=
  "\n".intercalate (c.helpLines path)

/-- The command at a path (root name first), as the parser sees it; the root if the path
leads nowhere. -/
def Command.at (c : Command) (path : List String) : Command :=
  (c.walk path.tail).getD c

/-- The message of a usage error. -/
def ArgError.message : ArgError → String
  | .unknownOption t => "unexpected argument '" ++ t ++ "' found"
  | .missingValue t => "a value is required for '" ++ t ++ "' but none was supplied"
  | .unexpectedValue t => "unexpected value in '" ++ t ++ "': the flag takes no value"
  | .unknownCommand w => "unrecognized subcommand '" ++ w ++ "'"
  | .missingCommand c => "'" ++ c ++ "' requires a subcommand but one was not provided"
  | .missingArgument p => "the required argument <" ++ p.toUpper ++ "> was not provided"
  | .extraArgument w => "unexpected argument '" ++ w ++ "' found"
  | .badValue p v t => "invalid value '" ++ v ++ "' for '" ++ p ++ "': expected " ++ t.describe
  | .repeated p => "the argument '" ++ p ++ "' cannot be used multiple times"
  | .missingOption p => "the required option '" ++ p ++ "' was not provided"
  | .rejected p v => "invalid value '" ++ v ++ "' for '" ++ p ++ "'"
  | .requires p q => "the argument '" ++ p ++ "' requires '" ++ q ++ "'"
  | .conflicts p q => "the argument '" ++ p ++ "' cannot be used with '" ++ q ++ "'"

/-- The text printed on a usage error found at `path` (root name first): the message and the
usage of the subcommand there. -/
def errorText (c : Command) (path : List String) (e : ArgError) : String :=
  "error: " ++ e.message ++ "\n\n" ++ (c.at path).usage path ++
    "\n\nFor more information, try '--help'."

/-- Where a text goes. -/
inductive Channel where
  | stdout
  | stderr
  deriving DecidableEq, Repr

/-- The text the front end prints, if any. -/
def Outcome.text (c : Command) : Outcome → Option (Channel × String)
  | .run _ => none
  | .help p => some (.stdout, (c.at p).help p)
  | .version v => some (.stdout, c.name ++ " " ++ v)
  | .error p e => some (.stderr, errorText c p e)

/-! ## Builders -/

/-- A flag. -/
def flag (id : String) (short : List String := []) (help : String := "") : Opt :=
  { id, short, help }

/-- An option with a value. -/
def opt (id : String) (type : ArgType := .str) (short : List String := [])
    (help : String := "") (metavar : String := "") : Opt :=
  { id, short, help, metavar, arg := some type }

/-- A positional argument. -/
def arg (id : String) (type : ArgType := .str) (arity : Arity := .one) (help : String := "") :
    Pos :=
  { id, type, arity, help }

namespace Opt
/-- Set the default value. -/
def withDefault (o : Opt) (d : String) : Opt := { o with default := some d }
/-- Read this environment variable when absent. -/
def withEnv (o : Opt) (e : String) : Opt := { o with env := some e }
/-- Make required. -/
def req (o : Opt) : Opt := { o with required := true }
/-- Allow repetition. -/
def many (o : Opt) : Opt := { o with repeated := true }
/-- A counted flag (`-vvv`; read with `Matches.count`). -/
def counted (o : Opt) : Opt := { o with repeated := true }
/-- A flag that also reads `--no-NAME`; the last occurrence wins (`Matches.switch`). -/
def withNo (o : Opt) : Opt := { o with negatable := true, repeated := true }
/-- The value is optional, given only attached (`--name=V`). -/
def optVal (o : Opt) : Opt := { o with valueOptional := true }
/-- The value is optional, given only attached; a bare `--name` means `d` (clap's
`default_missing_value`). -/
def optValOr (o : Opt) (d : String) : Opt := { o with valueOptional := true, missing := some d }
/-- The single-dash names are exact tokens, never cluster letters (`-O`). -/
def exactly (o : Opt) : Opt := { o with exact := true }
/-- Accepted at every level below its own. -/
def inherited (o : Opt) : Opt := { o with global := true }
/-- Add long aliases. -/
def alias (o : Opt) (ns : List String) : Opt := { o with long := o.long ++ ns }
/-- Add exact single-dash tokens (`-O2`, `-all`). -/
def tokens (o : Opt) (ts : List String) : Opt := { o with short := o.short ++ ts }
end Opt

namespace Command

/-- Append options to the options of `c` (old names keep their meaning: `extends_appendOpts`). -/
def appendOpts (c : Command) (os : List Opt) : Command := c.inherit os

/-- Add an option at the end. -/
def addOpt (c : Command) (o : Opt) : Command := c.appendOpts [o]

/-- Add a subcommand at the end. -/
def addSub (c : Command) (s : Command) : Command := { c with subs := c.subs ++ [s] }

/-- `-h, --help`, accepted at every level (a global option of the root). -/
def withHelp (c : Command) : Command := c.addOpt helpOpt

/-- Options accepted at every level (clap's global arguments). -/
def withGlobal (c : Command) (os : List Opt) : Command := c.appendOpts (os.map Opt.inherited)

/-- `-V, --version` on the root, printing `v`. -/
def withVersion (c : Command) (v : String) : Command :=
  { c.addOpt versionOpt with version := some v }

/-- Change the subcommand at a path (by name or alias; the command itself at `[]`). -/
def modifyAt : Command → List String → (Command → Command) → Command
  | c, [], f => f c
  | c, w :: ws, f =>
    { c with subs := c.subs.map fun s => if s.names.contains w then s.modifyAt ws f else s }

/-- Value checks in force at `c` and every level below. -/
def withChecks (c : Command) (cs : List (String × ValueCheck)) : Command :=
  { c with checks := c.checks ++ cs }

/-- Value checks of the subcommand at `path` and below (they come before the checks above). -/
def withChecksAt (c : Command) (path : List String) (cs : List (String × ValueCheck)) : Command :=
  c.modifyAt path (·.withChecks cs)

/-- Rules of the subcommand at `path`. -/
def withRulesAt (c : Command) (path : List String) (rs : List Rule) : Command :=
  c.modifyAt path fun d => { d with rules := d.rules ++ rs }

/-- Rules, each at its subcommand path. -/
def withRules (c : Command) (rs : List (List String × Rule)) : Command :=
  rs.foldl (fun c r => c.withRulesAt r.1 [r.2]) c

end Command

/-! ## Running a front end -/

mutual
/-- The environment variables a grammar reads. -/
def Command.envVars : Command → List String
  | ⟨_, _, _, os, _, subs, _, _, _, _, _⟩ => os.filterMap (·.env) ++ Command.envVarsAll subs
/-- `envVars` of a list. -/
def Command.envVarsAll : List Command → List String
  | [] => []
  | s :: ss => s.envVars ++ Command.envVarsAll ss
end

/-- What the front end needs from its host: the environment variables it reads, and a way to
print a line. `Command.main` uses `IO`; `Silmaril.Cli.Front` reads the same program in the
behaviour model. -/
structure Host (m : Type → Type) where
  /-- The values of these environment variables (`none`: unset), as a lookup function. -/
  getEnvs : List String → m (String → Option String)
  /-- Print a line (the text and a newline) on a channel. -/
  putLine : Channel → String → m Unit

/-- Print the front end's text, if any. -/
def Host.emit {m : Type → Type} [Monad m] (h : Host m) : Option (Channel × String) → m Unit
  | some (ch, s) => h.putLine ch s
  | none => pure ()

/-- What the program does with an outcome: run with the matches, or print the text of help,
version or a usage error and exit with its code. -/
def Command.finish {m : Type → Type} [Monad m] (h : Host m) (c : Command)
    (run : Matches → m UInt32) : Outcome → m UInt32
  | .run mt => run mt
  | out => h.emit (out.text c) >>= fun _ => pure (out.exitCode?.getD 0).toUInt32

/-- **A program behind the derived front end**, for any host: read the declared environment
variables, `interpret` the arguments, print help, version or usage errors (exit 0, 0, 2),
else call `run` with the matches. -/
def Command.mainWith {m : Type → Type} [Monad m] (h : Host m) (c : Command)
    (run : Matches → m UInt32) (argv : List String) : m UInt32 :=
  h.getEnvs c.envVars >>= fun env => c.finish h run (interpret c env argv)

/-- The `IO` host: `IO.getEnv`, `IO.println`, `IO.eprintln`. -/
def Host.io : Host IO where
  getEnvs vs := do
    let vals ← vs.mapM fun v => do pure (v, ← IO.getEnv v)
    pure fun v => (vals.lookup v).join
  putLine
    | .stdout, s => IO.println s
    | .stderr, s => IO.eprintln s

/-- Run a program behind the derived front end in `IO`. -/
def Command.main (c : Command) (run : Matches → IO UInt32) (argv : List String) : IO UInt32 :=
  c.mainWith Host.io run argv

/-! ## Grammar morphisms -/

/-- An option whose names cannot capture a command line that already parses: no long name
starts with `no-`, every single-dash name is one letter. Appending such options (at a level, or
as global options) is a morphism (`extends_appendOpts`). -/
def Opt.Plain (o : Opt) : Prop :=
  (∀ n ∈ o.long, stripNo n = none) ∧ ∀ n ∈ o.short, n.length = 1

instance (o : Opt) : Decidable o.Plain := by unfold Opt.Plain; infer_instance

mutual
/-- Every option declared anywhere in a grammar. -/
def Command.allOpts : Command → List Opt
  | ⟨_, _, _, os, _, subs, _, _, _, _, _⟩ => os ++ Command.allOptsAll subs
/-- `allOpts` of a list. -/
def Command.allOptsAll : List Command → List Opt
  | [] => []
  | s :: ss => s.allOpts ++ Command.allOptsAll ss
end

/-- An option that cannot capture a command line that already parses with an option table
`os`: no long name starts with `no-`, and every single-dash name is one letter or an exact
token whose first letter is not a cluster letter of `os` (Binaryen's `-O2`, `-all`).
`Opt.Plain` options are fresh in every table; appending fresh options is a morphism
(`extends_appendFresh`). -/
def Opt.FreshIn (os : List Opt) (o : Opt) : Prop :=
  (∀ n ∈ o.long, stripNo n = none) ∧ ∀ n ∈ o.short, n.length = 1 ∨
    n.toList.head?.any (fun ch => (findShort (clusterOpts os) (String.singleton ch)).isNone) = true

instance (os : List Opt) (o : Opt) : Decidable (o.FreshIn os) := by
  unfold Opt.FreshIn; infer_instance

/-- `d'` extends `d` at one level: same name, same kind (with or without subcommands), and
every option token `d` reads, `d'` reads the same way. -/
def LocalExt (d d' : Command) : Prop :=
  d'.name = d.name ∧ d'.subs.isEmpty = d.subs.isEmpty ∧
    ∀ t x r, readOpt d.opts t x = .ok r → readOpt d'.opts t x = .ok r

/-- **A grammar morphism** `c ⟶ c'`: every subcommand path of `c` is one of `c'`, with a local
extension there. Appending options (`extends_appendOpts`) and adding subcommands
(`extends_addSub`) are morphisms; every command line of `c` means the same in `c'`
(`scan_extends`). -/
def Extends (c c' : Command) : Prop :=
  ∀ ws d, c.walk ws = some d → ∃ d', c'.walk ws = some d' ∧ LocalExt d d'

@[inherit_doc] scoped infix:50 " ⊑ " => Extends

end Silmaril.Cli
