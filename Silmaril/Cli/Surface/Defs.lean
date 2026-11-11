module

/-!
# CLI surfaces: the declared command line of a tool, as data

A `Surface.Command` is the command line a tool declares: its subcommands, options
(`Opt`), positional arguments (`Pos`) and help texts, in the conventions of Rust's clap
(which `wasm-tools` uses) and of most POSIX-style tools:

* `--long`, `--long=VALUE`, `--long VALUE`; `-s`, `-sVALUE`, `-s=VALUE`, `-s VALUE`;
  switch clusters `-tg`;
* `--` ends the options: every later token is a positional argument;
* `-` alone is a positional argument (by convention, stdin or stdout);
* a command with subcommands takes the first positional word as the subcommand name;
  `help NAME…` and `-h`/`--help` print help, `-V`/`--version` the version.

Everything a user sees about the surface is a function of the data: the usage line
(`Command.usage`), the help text (`Command.help`, in clap's `-h` layout) and the
reference reading of an argument vector (`Command.parse`, into an `Outcome` with its exit
code, `Outcome.exit`). So help cannot drift from what is parsed. A normal form of
invocations is rendered by `Invocation.render`.

**Derived, not written by hand:** the CLIs of real tools are args grammars
(`Silmaril.Cli.Command`) in the clap dialect (`Silmaril.Cli.Clap.Tool`), and their surface is
computed from them (`Clap.Tool.surface`); it reproduces the earlier hand-written surfaces
exactly (help of every path, corpus, and this reading on the corpus; checked when they were
replaced). The surface keeps three jobs: clap's `-h` layout, the corpus of test vectors, and
`Command.parse` as the *reference reading* that `Clap.compare` sets beside the args-based
reading `Clap.Tool.read`. New tools should be written as `Clap.Tool`s, not as surfaces.
-/

@[expose] public section

namespace Silmaril.Cli.Surface

/-- How an option takes a value. -/
inductive Arg where
  /-- A switch: `--wat`. -/
  | switch
  /-- A counted switch, which may repeat: `-v, --verbose...`. -/
  | count
  /-- Exactly one value: `--output <OUTPUT>`, `--output=X`, `-o X`, `-oX`. -/
  | value (metavar : String)
  /-- An optional value, given only after `=`: `--validate[=<true|false>]`. -/
  | optValue (metavar : String)
  deriving DecidableEq, Repr, Inhabited

/-- One option of a command. -/
structure Opt where
  short : Option Char := none
  long : Option String := none
  arg : Arg := .switch
  /-- The one-line help (`-h`), without the `[default: …]` and `[possible values: …]`
  notes, which are rendered from `default` and `choices`. -/
  help : String := ""
  default : Option String := none
  /-- The accepted values; empty means any value. -/
  choices : List String := []
  /-- The option must be given (it then appears in the usage line). -/
  required : Bool := false
  /-- The option may be given more than once (a value list); otherwise a repetition is a
  usage error. Counted switches always repeat. -/
  multiple : Bool := false
  /-- Further exact spellings outside clap's conventions, e.g. Binaryen's `-O2` or `-all`
  (a token equal to one of them selects the option; it is not split as a short cluster). -/
  tokens : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- One positional argument. -/
structure Pos where
  metavar : String
  help : String := ""
  required : Bool := false
  /-- Takes every remaining positional token (`[ADDRESSES]...`). -/
  many : Bool := false
  default : Option String := none
  choices : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- A command: a leaf, or a group of subcommands (`subs ≠ []`). -/
structure Command where
  name : String
  /-- The summary line (first line of `-h`, and the row in the parent's command list). -/
  about : String := ""
  pos : List Pos := []
  opts : List Opt := []
  subs : List Command := []
  /-- Free text after the option table (clap's `after_help`: examples, exit status). -/
  after : String := ""
  /-- A group has clap's implicit `help NAME…` subcommand (`disable_help_subcommand` when
  false). -/
  helpSub : Bool := true

/-- What an exit code means. -/
structure Exit where
  code : Nat
  meaning : String
  deriving DecidableEq, Repr

/-- A tool: its root command (named as the program), its exit codes, and the exit code of
a usage error (2 by clap's convention; some tools use 1). -/
structure Tool where
  root : Command
  exits : List Exit := []
  usageExit : Nat := 2

/-! ## Builders -/

namespace Opt

/-- A switch with a long name. -/
def flag (long : String) (help : String := "") (short : Option Char := none) : Opt :=
  { long, short, help }

/-- An option with one value. -/
def val (long metavar : String) (help : String := "") (short : Option Char := none) : Opt :=
  { long, short, help, arg := .value metavar }

/-- The help switch `-h, --help` with a given text. -/
def helpWith (help : String) : Opt := { short := 'h', long := "help", help }

/-- The version switch `-V, --version`. -/
def version : Opt := { short := 'V', long := "version", help := "Print version" }

/-- A switch spelled by exact tokens only (`-O2`). -/
def token (t : String) (help : String := "") : Opt := { tokens := [t], help, multiple := true }

/-- The key under which an occurrence is recorded: the long name, else `-` and the short
name, else the first exact token. -/
def key (o : Opt) : String :=
  match o.long, o.short with
  | some l, _ => l
  | none, some c => "-" ++ c.toString
  | none, none => o.tokens.headD ""

/-- The help switch (`--help`, a switch: a `--help <X>` option is an ordinary option). -/
def isHelp (o : Opt) : Bool := o.long == some "help" && o.arg == .switch
/-- The version switch (`metadata add --version <NAME>` is an ordinary option). -/
def isVersion (o : Opt) : Bool := o.long == some "version" && o.arg == .switch

def takesValue (o : Opt) : Bool :=
  match o.arg with
  | .value _ | .optValue _ => true
  | _ => false

end Opt

/-! ## Rendering: usage and help as functions of the data -/

/-- The suffix of an option's left column: `...`, ` <M>`, `[=<M>]`. -/
def Arg.suffix : Arg → String
  | .switch => ""
  | .count => "..."
  | .value m => " <" ++ m ++ ">"
  | .optValue m => "[=<" ++ m ++ ">]"

/-- The left column of an option, as clap prints it (`-o, --output <OUTPUT>`; a long-only
option is indented by four spaces). -/
def Opt.spec (o : Opt) : String :=
  let names := match o.short, o.long with
    | some c, some l => "-" ++ c.toString ++ ", --" ++ l
    | some c, none => "-" ++ c.toString
    | none, some l => "    --" ++ l
    | none, none => ""
  ", ".intercalate ((if names.isEmpty then [] else [names]) ++ o.tokens) ++ o.arg.suffix

/-- Help text followed by the `[default: …]` and `[possible values: …]` notes. -/
def withNotes (help : String) (default : Option String) (choices : List String) : String :=
  let notes := (match default with | some d => ["[default: " ++ d ++ "]"] | none => []) ++
    (if choices.isEmpty then [] else ["[possible values: " ++ ", ".intercalate choices ++ "]"])
  " ".intercalate ((if help.isEmpty then [] else [help]) ++ notes)

def Opt.text (o : Opt) : String := withNotes o.help o.default o.choices

/-- A positional argument in usage and help: `<WIT>`, `[INPUT]`, `[ADDRESSES]...`. -/
def Pos.spec (p : Pos) : String :=
  (if p.required then "<" ++ p.metavar ++ ">" else "[" ++ p.metavar ++ "]") ++
    (if p.many then "..." else "")

def Pos.text (p : Pos) : String := withNotes p.help p.default p.choices

/-- The row of clap's implicit `help` subcommand. -/
def helpRow : String × String :=
  ("help", "Print this message or the help of the given subcommand(s)")

/-- The usage tail: `<COMMAND>` for a group; else `[OPTIONS]` (when some option is optional
and is not `-h`/`-V`), the required options and the positionals. -/
def Command.usageTail (c : Command) : String :=
  if !c.subs.isEmpty then "<COMMAND>" else
  let optional := c.opts.any fun o => !o.required && !o.isHelp && !o.isVersion
  let req := (c.opts.filter (·.required)).map fun o =>
    (match o.long with | some l => "--" ++ l | none => "-" ++ (o.short.map (·.toString)).getD "") ++
      o.arg.suffix
  " ".intercalate ((if optional then ["[OPTIONS]"] else []) ++ req ++ c.pos.map Pos.spec)

/-- `Usage: PROG SUB… TAIL`, where `path` is the program name and the subcommand path. -/
def Command.usage (path : List String) (c : Command) : String :=
  "Usage: " ++ " ".intercalate (path ++ [c.usageTail])

/-- A two-column table in clap's aligned layout. -/
def table (rows : List (String × String)) : String :=
  let w := rows.foldl (fun n r => max n r.1.length) 0
  "\n".intercalate (rows.map fun (l, r) =>
    let pad := String.ofList (List.replicate (w - l.length + 2) ' ')
    if r.isEmpty then "  " ++ l else "  " ++ l ++ pad ++ r)

/-- The `-h` help of a command at `path` (program name first), in clap's layout. Upstream
wraps long lines at 100 columns; the tests compare modulo whitespace. -/
def Command.help (path : List String) (c : Command) : String :=
  let sections : List String :=
    (if c.subs.isEmpty then [] else
      ["Commands:\n" ++ table (c.subs.map (fun s => (s.name, s.about)) ++
        (if c.helpSub then [helpRow] else []))]) ++
    (if c.pos.isEmpty then [] else ["Arguments:\n" ++ table (c.pos.map fun p => (p.spec, p.text))]) ++
    (if c.opts.isEmpty then [] else ["Options:\n" ++ table (c.opts.map fun o => (o.spec, o.text))]) ++
    (if c.after.isEmpty then [] else [c.after])
  "\n\n".intercalate ((if c.about.isEmpty then [] else [c.about]) ++ [c.usage path] ++ sections) ++
    "\n"

/-- The subcommand at a path. -/
def Command.find? (c : Command) : List String → Option Command
  | [] => some c
  | n :: p => (c.subs.find? (·.name == n)).bind (·.find? p)

/-- Every command path (without the program name), the root first, in help order. -/
partial def Command.paths (c : Command) : List (List String) :=
  [] :: c.subs.flatMap fun s => s.paths.map (s.name :: ·)

/-! ## The reference reading of an argument vector -/

/-- A parsed invocation: the subcommand path, the option occurrences (by `Opt.key`, in
order) and the positional arguments. -/
structure Invocation where
  path : List String := []
  opts : List (String × Option String) := []
  args : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- The result of reading an argument vector. -/
inductive Outcome where
  /-- Run the command. -/
  | run (inv : Invocation)
  /-- Print the help of the command at `path` on stdout. -/
  | help (path : List String)
  /-- Print the version on stdout. -/
  | version (path : List String)
  /-- A group was given no subcommand: its help on stderr. -/
  | needCommand (path : List String)
  /-- A usage error, with clap's first line. -/
  | error (msg : String)
  deriving DecidableEq, Repr, Inhabited

/-- The exit code an outcome fixes (`none`: the command decides). Usage errors and a missing
subcommand exit 2, help and version 0 (clap's conventions). -/
def Outcome.exit : Outcome → Option Nat
  | .run _ => none
  | .help _ | .version _ => some 0
  | .needCommand _ | .error _ => some 2

/-- The exit code a tool's reading fixes (`none`: the command decides). -/
def Tool.exitOf (t : Tool) : Outcome → Option Nat
  | .run _ => none
  | .help _ | .version _ => some 0
  | .needCommand _ | .error _ => some t.usageExit

def Outcome.isError : Outcome → Bool
  | .error _ | .needCommand _ => true
  | _ => false

namespace Parse

/-- The parsing state: the current command, the path so far, occurrences and positionals
(both reversed) and whether `--` was seen. -/
structure St where
  cmd : Command
  path : List String
  opts : List (String × Option String) := []
  args : List String := []
  dd : Bool := false

/-- A token that cannot be a value: it starts with `-` and is not `-` itself. -/
def optionLike (s : String) : Bool := s.startsWith "-" && s != "-"

def valueRequired (o : Opt) : String :=
  "a value is required for '" ++ o.spec.trimAscii.toString ++ "' but none was supplied"

/-- Record an occurrence, checking the value against the choices. -/
def add (st : St) (o : Opt) (v : Option String) : Except Outcome St :=
  match v with
  | some x =>
    if !o.choices.isEmpty && !o.choices.contains x then
      .error (.error ("invalid value '" ++ x ++ "' for '" ++ o.spec.trimAscii.toString ++ "'"))
    else .ok { st with opts := (o.key, v) :: st.opts }
  | none => .ok { st with opts := (o.key, v) :: st.opts }

/-- Read the characters of a short cluster `-abc`. Returns the new state and, when the last
option needs the next token as its value, that option. -/
def shorts (st : St) : List Char → Except Outcome (St × Option Opt)
  | [] => .ok (st, none)
  | ch :: cs =>
    match st.cmd.opts.find? (·.short == some ch) with
    | none => .error (.error ("unexpected argument '-" ++ ch.toString ++ "' found"))
    | some o =>
      if o.isHelp then .error (.help st.path)
      else if o.isVersion then .error (.version st.path)
      else match o.arg with
        | .switch | .count => do shorts (← add st o none) cs
        | .value _ | .optValue _ =>
          if cs.isEmpty then .ok (st, some o)
          else
            let v := String.ofList cs
            let v := if v.startsWith "=" then (v.drop 1).toString else v
            do return (← add st o (some v), none)

/-- Split `name=value`. -/
def splitEq (body : String) : String × Option String :=
  match body.splitOn "=" with
  | [] => (body, none)
  | [n] => (n, none)
  | n :: rest => (n, some ("=".intercalate rest))

/-- Checks after the last token: no missing subcommand, no forbidden repetition, every
required option, the number of positionals. -/
def finish (st : St) : Outcome :=
  let c := st.cmd
  let opts := st.opts.reverse
  let args := st.args.reverse
  if !c.subs.isEmpty then .needCommand st.path else
  match c.opts.find? (fun o => !o.multiple && o.arg != .count &&
      (opts.filter (·.1 == o.key)).length > 1) with
  | some o => .error ("the argument '" ++ o.spec.trimAscii.toString ++ "' cannot be used multiple times")
  | none =>
  match c.opts.find? (fun o => o.required && !opts.any (·.1 == o.key)) with
  | some _ => .error "the following required arguments were not provided"
  | none =>
  let nReq := (c.pos.filter (·.required)).length
  if args.length < nReq then .error "the following required arguments were not provided"
  else if !c.pos.any (·.many) && c.pos.length < args.length then
    .error ("unexpected argument '" ++ (args.drop c.pos.length).headD "" ++ "' found")
  else
    let bad := (args.zip c.pos).find? fun (a, p) => !p.choices.isEmpty && !p.choices.contains a
    match bad with
    | some (a, p) => .error ("invalid value '" ++ a ++ "' for '" ++ p.spec ++ "'")
    | none => .run { path := st.path.drop 1, opts, args }

/-- `help NAME…`: the help of the named subcommand. -/
def helpOf (st : St) (names : List String) : Outcome :=
  match st.cmd.find? names with
  | some _ => .help (st.path ++ names)
  | none => .error ("unrecognized subcommand '" ++ " ".intercalate names ++ "'")

/-- The main loop over the tokens. -/
def go : List String → St → Outcome
  | [], st => finish st
  | t :: ts, st =>
    if st.dd then go ts { st with args := t :: st.args }
    else if t == "--" then go ts { st with dd := true }
    else if let some o := st.cmd.opts.find? (·.tokens.contains t) then
      match o.arg with
      | .value _ =>
        match ts with
        | x :: ts' =>
          if optionLike x then .error (valueRequired o)
          else match add st o (some x) with
            | .ok st' => go ts' st'
            | .error e => e
        | [] => .error (valueRequired o)
      | _ =>
        match add st o none with
        | .ok st' => go ts st'
        | .error e => e
    else if t.startsWith "--" then
      let (name, v) := splitEq (t.drop 2).toString
      match st.cmd.opts.find? (·.long == some name) with
      | none => .error ("unexpected argument '" ++ t ++ "' found")
      | some o =>
        if o.isHelp then .help st.path
        else if o.isVersion then .version st.path
        else match o.arg, v with
          | .switch, some x | .count, some x =>
            .error ("unexpected value '" ++ x ++ "' for '--" ++ name ++ "' found")
          | .value _, none =>
            match ts with
            | x :: ts' =>
              if optionLike x then .error (valueRequired o)
              else match add st o (some x) with
                | .ok st' => go ts' st'
                | .error e => e
            | [] => .error (valueRequired o)
          | _, _ =>
            match add st o v with
            | .ok st' => go ts st'
            | .error e => e
    else if optionLike t then
      match shorts st (t.drop 1).toString.toList with
      | .error e => e
      | .ok (st', none) => go ts st'
      | .ok (st', some o) =>
        match ts with
        | x :: ts' =>
          if optionLike x then .error (valueRequired o)
          else match add st' o (some x) with
            | .ok st'' => go ts' st''
            | .error e => e
        | [] => .error (valueRequired o)
    else if !st.cmd.subs.isEmpty then
      if t == "help" && st.cmd.helpSub then helpOf st ts
      else match st.cmd.subs.find? (·.name == t) with
        | some c => go ts { st with cmd := c, path := st.path ++ [t] }
        | none => .error ("unrecognized subcommand '" ++ t ++ "'")
    else go ts { st with args := t :: st.args }

end Parse

/-- The reference reading of an argument vector (without the program name). -/
def Command.parse (c : Command) (argv : List String) : Outcome :=
  Parse.go argv { cmd := c, path := [c.name] }

/-! ## A corpus of argument vectors derived from a surface

Used to compare a surface with an implementation (`tools/cli-spec/tests`) and, for tools
written in Lean, inside Lean (`Silmaril.Wasm.Binaryen.DriverSpec`). -/

namespace Corpus

/-- A value: the first choice, the first alternative of a `a|b` value name, else `1`. -/
def sample (choices : List String) (metavar : String) : String :=
  match choices with
  | c :: _ => c
  | [] => if metavar.contains '|' then ((metavar.splitOn "|").headD "1") else "1"

def optSample (o : Opt) : String :=
  match o.arg with
  | .value m | .optValue m => sample o.choices m
  | _ => ""

/-- One use of an option: its long form, else its short form, else its first token. -/
def use (o : Opt) (v : Option String) : List String :=
  let flag := match o.long, o.short with
    | some l, _ => "--" ++ l
    | none, some c => "-" ++ c.toString
    | none, none => o.tokens.headD ""
  match o.arg, v with
  | .value _, some x => [flag, x]
  | .optValue _, some x => [flag ++ "=" ++ x]
  | _, _ => [flag]

/-- Positionals that satisfy the required ones (`file`, or the first choice). -/
def fill (c : Command) (file : String) : List String :=
  (c.pos.filter (·.required)).map fun p => sample p.choices file

/-- Uses of the required options other than the one with key `k`. -/
def required (c : Command) (k : String) : List String :=
  (c.opts.filter fun q => q.required && q.key != k).flatMap fun q => use q (some (optSample q))

/-- The argument vectors for one command path: help, unknown options, too many positionals,
`--`, and for every option a valid use, a repetition, a missing value and an unexpected
value. Positionals are `file`. -/
def at_ (file : String) (path : List String) (c : Command) : List (List String) :=
  let base := [path, path ++ ["-h"], path ++ ["--help"], path ++ ["--no-such-option-zz"],
    path ++ ["-Z"]]
  if !c.subs.isEmpty then base ++ [path ++ ["no-such-command-zz"], path ++ ["help"]] ++
    c.subs.map (fun s => ["help"] ++ path ++ [s.name])
  else
    let req := required c ""
    let extra := path ++ req ++ fill c file ++ (List.replicate (c.pos.length + 1) "extra-zz")
    base ++ [extra, path ++ req ++ ["--", "-t"] ++ fill c file] ++
    c.opts.flatMap fun o =>
      if o.isHelp || o.isVersion then [path ++ use o none] else
      let rq := required c o.key
      let ok := path ++ rq ++ use o (some (optSample o)) ++ fill c file
      let twice := path ++ rq ++ use o (some (optSample o)) ++ use o (some (optSample o)) ++
        fill c file
      match o.arg with
      | .value _ => [ok, twice, path ++ rq ++ fill c file ++ use o none,
          path ++ rq ++ use o none ++ ["-h"]]
      | .optValue _ => [ok, twice, path ++ rq ++ use o none ++ fill c file]
      | _ => [ok, twice] ++
        (if o.long.isSome || o.short.isSome then
          [path ++ rq ++ [(use o none).headD "" ++ "=1"] ++ fill c file] else [])

end Corpus

/-- The corpus of a surface: `Corpus.at_` for every command path, the root first. -/
def Command.corpus (root : Command) (file : String := "nonexistent-cli-spec.wasm") :
    List (List String) :=
  root.paths.flatMap fun p =>
    match root.find? p with
    | some c => Corpus.at_ file p c
    | none => []

/-- The value of an option in an invocation: the last occurrence, else the default. -/
def Invocation.value? (c : Command) (inv : Invocation) (key : String) : Option String :=
  match (inv.opts.filter (·.1 == key)).getLast? with
  | some (_, v) => v
  | none =>
    ((c.find? inv.path).bind fun c => c.opts.find? (·.key == key)).bind (·.default)

/-- How many times an option occurs (a counted switch's level). -/
def Invocation.count (inv : Invocation) (key : String) : Nat :=
  (inv.opts.filter (·.1 == key)).length

/-- The normal form of an invocation: the path, every occurrence as `--long` or
`--long=VALUE` (`-s`, `-s=VALUE` for short-only options), then `--` and the positionals.
`Command.parse` reads it back (checked on the pinned surfaces by examples; the general round
trip is the args track's). -/
def Invocation.render (inv : Invocation) : List String :=
  inv.path ++ inv.opts.map (fun (k, v) =>
    let flag := if k.startsWith "-" then k else "--" ++ k
    match v with
    | none => flag
    | some x => flag ++ "=" ++ x) ++
  (if inv.args.isEmpty then [] else "--" :: inv.args)

end Silmaril.Cli.Surface
