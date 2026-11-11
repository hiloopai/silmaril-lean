module

/-!
# The command-line grammar of `wasm-tools`

`wasm-tools` 1.262.0 parses its arguments with clap 4. This module is a specified,
executable model of the part of clap's grammar its subcommands use; every subcommand of the
Lean `wasm-tools` declares a `Spec` and calls `parse`.

* An argument `--` ends the options: every later argument is positional.
* `--NAME` is the option with long name `NAME`; `--NAME=V` gives it the value `V`
  (an error for a switch, `unexpectedValue`).
* `-` alone is a positional argument.
* `-abc` is a cluster of short options, read left to right: a switch or a counter takes no
  value and the cluster continues; the first option that takes a value takes the rest of the
  cluster (after one optional `=`) as its value, or, when nothing is left, the next argument.
* A value taken from the next argument must not look like an option (start with `-`, other
  than `-` itself); an empty value is an error (`valueRequired`).
* Any other argument is the next positional; the last positional of the spec may be
  `multiple` and then takes every later one.
* A switch or value option given twice is an error (`multipleUse`) unless `multiple`; a counter
  (`-v`, `-vv`, …) may repeat. A value outside an option's `choices` is `invalidValue`.
* `-h` (short help) and `--help` (long help) stop parsing at once, so an error *before* them
  wins and everything after them is ignored.
* Missing required positionals are reported after the last argument.

Errors are reported in argument order, as clap does. The laws proved in
`Silmaril.Wasm.Tools.Cli.Thms` reduce spellings to a normal form: `--` makes every later argument
positional (`go_dd`, `go_ddArg`), `-` is positional (`go_dash`), `--NAME=V` is `--NAME V` for a
value option (`go_long_eq`) and an error for a switch (`go_long_flag_eq`), `--help` asks for
the long help (`parse_help`). A round trip for the normal form (`render`) is not proved yet.
`parse` and `print` (`tools/wasm-tools/WasmTools/Core.lean`) and `completion` read their
arguments with this parser; `tools/wasm-tools/README.md` lists the clap features outside it.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Cli

/-- An argument, as a list of characters. -/
abbrev Arg := List Char

/-- What an option takes. -/
inductive Takes where
  /-- A switch: present or absent. -/
  | flag
  /-- A counter (`-v`, `-vv`, …): may repeat; `--NAME=V` is an error. -/
  | count
  /-- A value named `name` (for messages), restricted to `choices` when that is non-empty. -/
  | value (name : String) (choices : List String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One option of a subcommand. -/
structure Opt where
  key : String
  long : Option String := none
  short : Option Char := none
  takes : Takes := .flag
  /-- May be given more than once (value options collect their values). -/
  multiple : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One positional argument. -/
structure Pos where
  key : String
  /-- The name in messages, e.g. `INPUT`. -/
  name : String
  required : Bool := false
  /-- Takes every remaining positional argument (only meaningful for the last one). -/
  multiple : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A subcommand's command-line interface. -/
structure Spec where
  /-- The `Usage:` line of upstream's errors, e.g. `wasm-tools parse [OPTIONS] [INPUT]`. -/
  usage : String
  opts : List Opt
  pos : List Pos
  deriving Repr, Inhabited

/-- One parsed argument. -/
inductive Item where
  | opt (key : String) (value : Option String)
  | pos (key : String) (value : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A usage error. -/
inductive Err where
  | unexpectedArg (arg : String)
  /-- An extra positional after `--` (clap gives no tip then). -/
  | unexpectedPos (arg : String)
  | valueRequired (o : Opt)
  | invalidValue (o : Opt) (v : String)
  | multipleUse (o : Opt)
  | unexpectedValue (o : Opt) (v : String)
  | missingRequired (p : Pos)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The result of parsing. -/
inductive Outcome where
  | ok (items : List Item)
  /-- `-h` (`false`) or `--help` (`true`). -/
  | help (long : Bool)
  | err (e : Err)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Put an item in front of a successful outcome. -/
def Outcome.cons (i : Item) : Outcome → Outcome
  | .ok is => .ok (i :: is)
  | o => o

/-! ## Parsing -/

/-- The parser's state: after `--`, the number of positionals read, the keys of the
non-repeatable options already given. -/
structure St where
  dd : Bool := false
  npos : Nat := 0
  seen : List String := []
  deriving Repr, Inhabited

def Spec.findLong (s : Spec) (n : Arg) : Option Opt :=
  s.opts.find? (fun o => o.long.map String.toList == some n)

def Spec.findShort (s : Spec) (c : Char) : Option Opt :=
  s.opts.find? (fun o => o.short == some c)

/-- The positional that the `n`-th positional argument fills. -/
def Spec.posFor (s : Spec) (n : Nat) : Option Pos :=
  match s.pos[n]? with
  | some p => some p
  | none => s.pos.getLast?.filter (·.multiple)

/-- Split `NAME=V` at its first `=`. -/
def splitEq : Arg → Arg × Option Arg
  | [] => ([], none)
  | '=' :: v => ([], some v)
  | c :: cs => let (n, v) := splitEq cs; (c :: n, v)

/-- Does the argument look like an option (`-x…` or `--…`, not `-` alone)? -/
def optionLike : Arg → Bool
  | '-' :: _ :: _ => true
  | _ => false

/-- Is the option-like argument `a` an option of `s`? (A missing value followed by an
unknown option is reported as that unknown argument, by clap.) -/
def Spec.knows (s : Spec) (a : Arg) : Bool :=
  match a with
  | '-' :: '-' :: name => (s.findLong (splitEq name).1).isSome || name == "help".toList
  | ['-', c] => (s.findShort c).isSome || c == 'h'
  | '-' :: c :: _ => (s.findShort c).isSome || c == 'h'
  | _ => false

/-- The error for an option `o` whose value is missing because `v` looks like an option. -/
def missingValue (s : Spec) (o : Opt) (v : Arg) : Err :=
  if s.knows v then .valueRequired o else .unexpectedArg (String.ofList v)

def Opt.takesValue (o : Opt) : Bool :=
  match o.takes with
  | .value .. => true
  | _ => false

/-- Record one occurrence of `o` with value `v`: the repetition and choice checks, then the
item. -/
def record (st : St) (o : Opt) (v : Option String) : Except Err (St × Item) :=
  if !o.multiple && o.takes != .count && st.seen.contains o.key then .error (.multipleUse o)
  else
    match o.takes, v with
    | .value _ cs, some v =>
      if cs.isEmpty || cs.contains v then .ok ({ st with seen := o.key :: st.seen }, .opt o.key (some v))
      else .error (.invalidValue o v)
    | _, _ => .ok ({ st with seen := o.key :: st.seen }, .opt o.key v)

/-- The positionals still missing at the end. -/
def missing (s : Spec) (st : St) : Option Pos :=
  (s.pos.drop st.npos).find? (·.required)

mutual

/-- Parse the arguments. -/
def go (s : Spec) (st : St) : List Arg → Outcome
  | [] =>
    match missing s st with
    | some p => .err (.missingRequired p)
    | none => .ok []
  | a :: rest =>
    if st.dd then positional s st a rest
    else
      match a with
      | ['-', '-'] => go s { st with dd := true } rest
      | '-' :: '-' :: name =>
        if name == "help".toList && (s.findLong name).isNone then .help true
        else
          let (n, v) := splitEq name
          match s.findLong n with
          | none => .err (.unexpectedArg (String.ofList a))
          | some o =>
            if o.takesValue then
              match v with
              | some [] => .err (.valueRequired o)
              | some v => withOpt s st o (some (String.ofList v)) rest
              | none =>
                match rest with
                | v :: rest' =>
                  if v.isEmpty then .err (.valueRequired o)
                  else if optionLike v then .err (missingValue s o v)
                  else withOpt s st o (some (String.ofList v)) rest'
                | [] => .err (.valueRequired o)
            else
              match v with
              | some v => .err (.unexpectedValue o (String.ofList v))
              | none => withOpt s st o none rest
      | '-' :: c :: cs => short s st (c :: cs) rest
      | _ => positional s st a rest
termination_by args => (args.length, 1, 0)

/-- A cluster of short options (`cs` non-empty), then the remaining arguments. -/
def short (s : Spec) (st : St) (cs : Arg) (rest : List Arg) : Outcome :=
  match cs with
  | [] => go s st rest
  | c :: cs' =>
    match s.findShort c with
    | none =>
      if c == 'h' then .help false
      else .err (.unexpectedArg (String.ofList ['-', c]))
    | some o =>
      if o.takesValue then
        let v := match cs' with
          | '=' :: v => v
          | v => v
        if !v.isEmpty then withOpt s st o (some (String.ofList v)) rest
        else if !cs'.isEmpty then .err (.valueRequired o)
        else
          match rest with
          | v :: rest' =>
            if v.isEmpty then .err (.valueRequired o)
            else if optionLike v then .err (missingValue s o v)
            else withOpt s st o (some (String.ofList v)) rest'
          | [] => .err (.valueRequired o)
      else
        match record st o none with
        | .error e => .err e
        | .ok (st', i) => (short s st' cs' rest).cons i
termination_by (rest.length, 2, cs.length)

/-- Record an option, then continue with the remaining arguments. -/
def withOpt (s : Spec) (st : St) (o : Opt) (v : Option String) (rest : List Arg) : Outcome :=
  match record st o v with
  | .error e => .err e
  | .ok (st', i) => (go s st' rest).cons i
termination_by (rest.length, 1, 1)

/-- A positional argument. -/
def positional (s : Spec) (st : St) (a : Arg) (rest : List Arg) : Outcome :=
  match s.posFor st.npos with
  | none => .err (if st.dd then .unexpectedPos (String.ofList a) else .unexpectedArg (String.ofList a))
  | some p => (go s { st with npos := st.npos + 1 } rest).cons (.pos p.key (String.ofList a))
termination_by (rest.length, 1, 1)

end

/-- Parse a subcommand's arguments. -/
def parse (s : Spec) (args : List String) : Outcome :=
  go s {} (args.map String.toList)

/-! ## Reading the parsed items -/

/-- Is the switch given? -/
def flag (is : List Item) (key : String) : Bool :=
  is.any fun | .opt k _ => k == key | _ => false

/-- How often is the counter given? -/
def count (is : List Item) (key : String) : Nat :=
  (is.filter fun | .opt k _ => k == key | _ => false).length

/-- The values of an option, in order. -/
def values (is : List Item) (key : String) : List String :=
  is.filterMap fun | .opt k (some v) => if k == key then some v else none | _ => none

/-- The (last) value of an option. -/
def value? (is : List Item) (key : String) : Option String :=
  (values is key).getLast?

/-- The positionals of a key, in order. -/
def positionals (is : List Item) (key : String) : List String :=
  is.filterMap fun | .pos k v => if k == key then some v else none | _ => none

/-! ## Messages (clap's wording) -/

/-- How clap names an option in messages: `--output <OUTPUT>`, `--verbose...`, `--wat`,
`-g`. -/
def Opt.display (o : Opt) : String :=
  let base := match o.long with
    | some l => "--" ++ l
    | none => match o.short with
      | some c => String.ofList ['-', c]
      | none => o.key
  match o.takes with
  | .flag => base
  | .count => base ++ "..."
  | .value n cs =>
    if o.long.isNone && !cs.isEmpty then base ++ " <" ++ "|".intercalate cs ++ ">"
    else base ++ " <" ++ n ++ ">"

/-- The text clap writes on stderr for a usage error (exit status 2). -/
def Err.render (s : Spec) : Err → String
  | .unexpectedArg a =>
    let tip := if optionLike a.toList then
        s!"\n  tip: to pass '{a}' as a value, use '-- {a}'\n" else ""
    s!"error: unexpected argument '{a}' found\n{tip}\nUsage: {s.usage}\n\n" ++
      "For more information, try '--help'.\n"
  | .unexpectedPos a =>
    s!"error: unexpected argument '{a}' found\n\nUsage: {s.usage}\n\n" ++
      "For more information, try '--help'.\n"
  | .valueRequired o =>
    s!"error: a value is required for '{o.display}' but none was supplied\n\n" ++
      "For more information, try '--help'.\n"
  | .invalidValue o v =>
    let cs := match o.takes with | .value _ cs => ", ".intercalate cs | _ => ""
    -- wasm-tools' own value parsers (`ColorChoice`, `GenerateDwarf`) word their errors
    match o.long with
    | some "color" =>
      s!"error: invalid value '{v}' for '{o.display}': unrecognized color choice '{v}': " ++
        "valid choices are: always, always-ansi, never, auto\n\nFor more information, try '--help'.\n"
    | some "generate-dwarf" =>
      s!"error: invalid value '{v}' for '{o.display}': unknown `--generate-dwarf` setting: {v}" ++
        "\n\nFor more information, try '--help'.\n"
    | _ =>
      s!"error: invalid value '{v}' for '{o.display}'\n  [possible values: {cs}]\n\n" ++
        "For more information, try '--help'.\n"
  | .multipleUse o =>
    s!"error: the argument '{o.display}' cannot be used multiple times\n\nUsage: {s.usage}\n\n" ++
      "For more information, try '--help'.\n"
  | .unexpectedValue o v =>
    -- clap's usage line names the offending switch in place of `[OPTIONS]`
    let usage := s.usage.replace "[OPTIONS]" (o.display.replace "..." "")
    s!"error: unexpected value '{v}' for '{o.display}' found; no more were expected\n\n" ++
      s!"Usage: {usage}\n\nFor more information, try '--help'.\n"
  | .missingRequired p =>
    s!"error: the following required arguments were not provided:\n  <{p.name}>\n\n" ++
      s!"Usage: {s.usage}\n\nFor more information, try '--help'.\n"

/-! ## The normal form -/

/-- The normal spelling of one option item: `--NAME=V` or `--NAME` (or `-c`, `-cV` for a
short-only option). -/
def Opt.renderNF (o : Opt) (v : Option String) : String :=
  match o.long, v with
  | some l, some v => "--" ++ l ++ "=" ++ v
  | some l, none => "--" ++ l
  | none, some v => String.ofList ['-', o.short.getD '?'] ++ v
  | none, none => String.ofList ['-', o.short.getD '?']

/-- Render items in normal form: the options first, then `--` and the positionals. -/
def render (s : Spec) (is : List Item) : List String :=
  let opts := is.filterMap fun
    | .opt k v => (s.opts.find? (·.key == k)).map (·.renderNF v)
    | .pos .. => none
  let poss := is.filterMap fun | .pos _ v => some v | .opt .. => none
  opts ++ (if poss.isEmpty then [] else "--" :: poss)

end Silmaril.Wasm.Tools.Cli
