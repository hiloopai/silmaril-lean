module

/-!
# The command-line grammar of `wasm-tools component …`

`wasm-tools` 1.262.0 parses its arguments with clap 4. This module is an executable model of
the part of clap the `component` subcommands (`new`, `wit`, `embed`, `targets`, `unbundle`)
use, as data (`Spec`) and one parser (`parse`). Besides what every subcommand has (switches,
valued options, counters, optional positionals), they use three features of clap that the
core subcommands do not:

* **optional booleans with `require_equals`** (`--validate[=<true|false>]`): `--validate` is
  `true`, `--validate=false` is `false`, and the next argument is never taken as the value;
* **conflicts** (`--dummy` with `--dummy-names`, `--wasm` with `--wat`, …) and
  **requirements** (`--async-callback` requires `--dummy-names`);
* **required** positionals and options (`<WIT>`, `--module-dir <PATH>`).

Lexical rules (clap's):

* `--` ends the options: every later argument is positional; `-` alone is positional.
* `--NAME=V` gives `V` to the option `NAME`; a switch given a value is an error.
* `--NAME` of a valued option takes the next argument as its value; that argument must not
  start with `-` (other than `-` itself). An optional boolean never takes the next argument.
* `-abc` is a cluster read left to right; the first option of the cluster that takes a value
  takes the rest of the cluster (after one optional `=`) or, when nothing is left, the next
  argument.
* `-h` (short help) and `--help` (long help) stop at once.
* An option given twice is an error unless it is `multiple` or a counter.

After the arguments are read (`scan`), `finish` checks, in clap's order, the conflicts and
then the required arguments and requirements. The specification theorems are in
`Silmaril.Wasm.Tools.Component.Args.Thms`: a successful parse names only declared arguments,
has no conflicting pair, has every required argument and requirement, and long and short
spellings, `--NAME=V` and `--NAME V`, and clusters agree.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Args

/-- What an option takes. -/
inductive Takes where
  /-- A switch. -/
  | flag
  /-- A counter (`-v`, `-vv`): may repeat. -/
  | count
  /-- A value, named `name` in messages, restricted to `choices` when non-empty. -/
  | value (name : String) (choices : List String)
  /-- `--NAME[=<true|false>]` (clap's `Option<Option<bool>>` with `require_equals`). -/
  | optBool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One option. -/
structure Opt where
  key : String
  long : Option String := none
  short : Option Char := none
  takes : Takes := .flag
  /-- May be given more than once (each occurrence is an item). -/
  multiple : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One positional argument. -/
structure Pos where
  key : String
  /-- The name in messages, e.g. `INPUT`. -/
  name : String
  required : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A subcommand's command line. -/
structure Spec where
  /-- The `Usage:` line of upstream's errors. -/
  usage : String
  opts : List Opt
  pos : List Pos
  /-- Pairs of keys that may not both be present. -/
  conflicts : List (String × String) := []
  /-- `(a, b)`: when `a` is present, `b` must be. -/
  requires : List (String × String) := []
  /-- Keys of required options. -/
  required : List String := []
  deriving Repr, Inhabited

/-- One parsed argument. -/
inductive Item where
  | opt (key : String) (value : Option String)
  | pos (key : String) (value : String)
  deriving Repr, BEq, DecidableEq, Inhabited

def Item.key : Item → String
  | .opt k _ => k
  | .pos k _ => k

/-- A usage error. -/
inductive Err where
  /-- An unknown option or an extra positional. -/
  | unexpectedArg (arg : String)
  | valueRequired (o : Opt)
  | invalidValue (o : Opt) (v : String)
  | multipleUse (o : Opt)
  | unexpectedValue (o : Opt) (v : String)
  | conflict (a b : String)
  | missing (names : List String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The result of parsing. -/
inductive Outcome where
  | ok (items : List Item)
  /-- `-h` (`false`) or `--help` (`true`). -/
  | help (long : Bool)
  | err (e : Err)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Lookup -/

def Spec.findLong (s : Spec) (n : String) : Option Opt :=
  s.opts.find? (fun o => o.long == some n)

def Spec.findShort (s : Spec) (c : Char) : Option Opt :=
  s.opts.find? (fun o => o.short == some c)

def Spec.findKey (s : Spec) (k : String) : Option Opt :=
  s.opts.find? (fun o => o.key == k)

/-- Does the value satisfy the option's restriction? -/
def Opt.accepts (o : Opt) (v : String) : Bool :=
  match o.takes with
  | .value _ cs => cs.isEmpty || cs.contains v
  | .optBool => v == "true" || v == "false"
  | _ => false

def Opt.takesValue (o : Opt) : Bool :=
  match o.takes with
  | .value .. => true
  | _ => false

/-! ## Reading the arguments -/

/-- The parser's state: after `--`, positionals read, keys of non-repeatable options given. -/
structure St where
  dd : Bool := false
  npos : Nat := 0
  seen : List String := []
  deriving Repr, Inhabited

/-- Record one occurrence of `o` with value `v`: a second use is an error unless allowed. -/
def St.use (st : St) (o : Opt) (v : Option String) : Except Err (St × Item) :=
  if o.multiple || o.takes == .count then .ok (st, .opt o.key v)
  else if st.seen.contains o.key then .error (.multipleUse o)
  else .ok ({ st with seen := o.key :: st.seen }, .opt o.key v)

/-- A value given to `o` (by `=` or as the next argument): check its restriction. -/
def St.useValue (st : St) (o : Opt) (v : String) : Except Err (St × Item) :=
  if v.isEmpty && o.takesValue then .error (.valueRequired o)
  else if o.accepts v then st.use o (some v) else .error (.invalidValue o v)

/-- Does an argument look like an option (and so cannot be a value)? -/
def looksLikeOpt (a : String) : Bool := a.startsWith "-" && a != "-"

/-- The positional at index `st.npos`, or an error. -/
def St.positional (s : Spec) (st : St) (a : String) : Except Err (St × Item) :=
  match s.pos[st.npos]? with
  | some p => .ok ({ st with npos := st.npos + 1 }, .pos p.key a)
  | none => .error (.unexpectedArg a)

/-- One step of `scan` in the middle of a short cluster: the option `o` named by a short
letter, followed by the rest `cs` of the cluster. Returns the item, the new state, the rest
of the cluster still to read, and whether the next argument was consumed. -/
def shortStep (st : St) (o : Opt) (cs : List Char) (next : Option String) :
    Except Err (St × Item × List Char × Bool) :=
  match o.takes with
  | .value .. =>
    match cs with
    | '=' :: v => (st.useValue o (String.ofList v)).map fun (st', i) => (st', i, [], false)
    | [] =>
      match next with
      | some v =>
        if looksLikeOpt v then .error (.valueRequired o)
        else (st.useValue o v).map fun (st', i) => (st', i, [], true)
      | none => .error (.valueRequired o)
    | v => (st.useValue o (String.ofList v)).map fun (st', i) => (st', i, [], false)
  | .optBool =>
    match cs with
    | '=' :: v => (st.useValue o (String.ofList v)).map fun (st', i) => (st', i, [], false)
    | _ => (st.use o none).map fun (st', i) => (st', i, cs, false)
  | _ => (st.use o none).map fun (st', i) => (st', i, cs, false)

/-- Read a short cluster (the characters after `-`). `fuel` bounds the cluster's length. -/
def scanCluster (s : Spec) : Nat → St → List Char → Option String →
    Except (Option Err) (St × List Item × Bool)
  | 0, st, _, _ => .ok (st, [], false)
  | _ + 1, st, [], _ => .ok (st, [], false)
  | f + 1, st, c :: cs, next =>
    if c == 'h' then .error none
    else match s.findShort c with
      | none => .error (some (.unexpectedArg ("-" ++ String.ofList (c :: cs))))
      | some o =>
        match shortStep st o cs next with
        | .error e => .error (some e)
        | .ok (st', i, rest, used) =>
          if used then .ok (st', [i], true)
          else match scanCluster s f st' rest next with
            | .ok (st'', is, u) => .ok (st'', i :: is, u)
            | .error e => .error e

/-- `NAME` and the value after the first `=`, if any. -/
def splitName (body : String) : String × Option String :=
  match body.splitOn "=" with
  | [n] => (n, none)
  | n :: rest => (n, some ("=".intercalate rest))
  | [] => (body, none)

/-- Read a long option `--n` or `--n=v` (`body` is what follows `--`). -/
def scanLong (s : Spec) (st : St) (body : String) (next : Option String) :
    Except Err (St × Item × Bool) :=
  match s.findLong (splitName body).1 with
  | none => .error (.unexpectedArg ("--" ++ body))
  | some o =>
    match o.takes, (splitName body).2 with
    | .value .., some v => (st.useValue o v).map fun (st', i) => (st', i, false)
    | .value .., none =>
      match next with
      | some w =>
        if looksLikeOpt w then .error (.valueRequired o)
        else (st.useValue o w).map fun (st', i) => (st', i, true)
      | none => .error (.valueRequired o)
    | .optBool, some v => (st.useValue o v).map fun (st', i) => (st', i, false)
    | _, some v => .error (.unexpectedValue o v)
    | _, none => (st.use o none).map fun (st', i) => (st', i, false)

/-- Put an item in front of a successful outcome. -/
def Outcome.cons (i : Item) : Outcome → Outcome
  | .ok is => .ok (i :: is)
  | o => o

/-- Put items in front of a successful outcome. -/
def Outcome.prepend (is : List Item) : Outcome → Outcome
  | .ok js => .ok (is ++ js)
  | o => o

/-- The arguments after a step that may have consumed the next one. -/
def after (used : Bool) (rest : List String) : List String := if used then rest.drop 1 else rest

theorem after_length_le (used : Bool) (rest : List String) : (after used rest).length ≤ rest.length := by
  cases used <;> simp [after]

/-- The letters of a short cluster `-abc`. -/
def clusterChars (a : String) : List Char := (a.drop 1).toString.toList

/-- Read all arguments, left to right. -/
def scan (s : Spec) : St → List String → Outcome
  | _, [] => .ok []
  | st, a :: rest =>
    if st.dd then
      match st.positional s a with
      | .ok (st', i) => (scan s st' rest).cons i
      | .error e => .err e
    else if a == "--" then scan s { st with dd := true } rest
    else if a == "--help" then .help true
    else if a.startsWith "--" then
      match scanLong s st (a.drop 2).toString rest.head? with
      | .error e => .err e
      | .ok (st', i, used) => (scan s st' (after used rest)).cons i
    else if looksLikeOpt a then
      match scanCluster s (clusterChars a).length st (clusterChars a) rest.head? with
      | .error none => .help false
      | .error (some e) => .err e
      | .ok (st', is, used) => (scan s st' (after used rest)).prepend is
    else
      match st.positional s a with
      | .ok (st', i) => (scan s st' rest).cons i
      | .error e => .err e
termination_by _ as => as.length
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := after_length_le used rest; omega)

/-! ## Conflicts and requirements -/

def present (is : List Item) (k : String) : Bool := is.any (·.key == k)

/-- The first conflicting pair present. -/
def firstConflict (s : Spec) (is : List Item) : Option (String × String) :=
  s.conflicts.find? fun (a, b) => present is a && present is b

/-- Does a present argument conflict with `b`? clap does not enforce a requirement on `b`
then (`component embed --dummy --async-callback` passes the requirement of
`--async-callback` on `--dummy-names`, which conflicts with `--dummy`). -/
def conflictsWithPresent (s : Spec) (is : List Item) (b : String) : Bool :=
  s.conflicts.any fun (x, y) => (x == b && present is y) || (y == b && present is x)

/-- The names of the required arguments that are absent, in clap's order: requirements of
present options (unless a present argument conflicts with the required one), required options,
then required positionals. -/
def missingNames (s : Spec) (is : List Item) : List String :=
  let disp (k : String) : String :=
    match s.findKey k with
    | some o => match o.long, o.takes with
      | some l, .value n _ => s!"--{l} <{n}>"
      | some l, _ => s!"--{l}"
      | none, _ => match o.short with | some c => s!"-{c}" | none => k
    | none => k
  (s.requires.filterMap fun (a, b) =>
      if present is a && !present is b && !conflictsWithPresent s is b then some (disp b)
      else none) ++
  (s.required.filterMap fun k => if present is k then none else some (disp k)) ++
  (s.pos.filterMap fun p => if p.required && !present is p.key then some s!"<{p.name}>" else none)

/-- Check conflicts, then required arguments. -/
def finish (s : Spec) (is : List Item) : Outcome :=
  match firstConflict s is with
  | some (a, b) => .err (.conflict a b)
  | none =>
    match missingNames s is with
    | [] => .ok is
    | ms => .err (.missing ms.eraseDups)

/-- **The parser.** -/
def parse (s : Spec) (args : List String) : Outcome :=
  match scan s {} args with
  | .ok is => finish s is
  | o => o

/-! ## Reading a parse -/

/-- Is the option or positional present? -/
def flag (is : List Item) (k : String) : Bool := present is k

/-- The number of occurrences (counters). -/
def count (is : List Item) (k : String) : Nat := (is.filter (·.key == k)).length

/-- The value of an option or positional (the first occurrence). -/
def value? (is : List Item) (k : String) : Option String :=
  is.findSome? fun
    | .opt k' v => if k' == k then v else none
    | .pos k' v => if k' == k then some v else none

/-- Every value of a repeatable option, in order. -/
def values (is : List Item) (k : String) : List String :=
  is.filterMap fun
    | .opt k' (some v) => if k' == k then some v else none
    | _ => none

/-- An optional boolean (`--x[=<true|false>]`): absent is `dflt`, `--x` is `true`. -/
def optBool (is : List Item) (k : String) (dflt : Bool) : Bool :=
  match is.find? (·.key == k) with
  | none => dflt
  | some (.opt _ (some v)) => v == "true"
  | some _ => true

/-! ## Messages (clap's) -/

/-- How clap names an option in messages. -/
def Opt.display (o : Opt) : String :=
  match o.long, o.takes with
  | some l, .value n _ => s!"--{l} <{n}>"
  | some l, .optBool => s!"--{l}[=<true|false>]"
  | some l, .count => s!"--{l}..."
  | some l, _ => s!"--{l}"
  | none, .value n _ => match o.short with | some c => s!"-{c} <{n}>" | none => o.key
  | none, _ => match o.short with | some c => s!"-{c}" | none => o.key

def possible (o : Opt) : String :=
  match o.takes with
  | .value _ cs@(_ :: _) => "\n  [possible values: " ++ String.intercalate ", " cs ++ "]"
  | .optBool => "\n  [possible values: true, false]"
  | _ => ""

def keyDisplay (s : Spec) (k : String) : String :=
  match s.findKey k with
  | some o => o.display
  | none => match s.pos.find? (·.key == k) with
    | some p => s!"<{p.name}>"
    | none => k

def moreInfo : String := "For more information, try '--help'.\n"

/-- The text clap prints on stderr for a usage error (exit status 2). The `Usage:` line is the
spec's static one; clap specializes it for conflicts and missing arguments (documented). -/
def render (s : Spec) : Err → String
  | .unexpectedArg a =>
    let tip := if looksLikeOpt a then "\n  tip: to pass '" ++ a ++ "' as a value, use '-- " ++ a ++ "'\n" else ""
    s!"error: unexpected argument '{a}' found\n{tip}\nUsage: {s.usage}\n\n{moreInfo}"
  | .valueRequired o =>
    s!"error: a value is required for '{o.display}' but none was supplied{possible o}\n\n{moreInfo}"
  | .invalidValue o v =>
    s!"error: invalid value '{v}' for '{o.display}'{possible o}\n\n{moreInfo}"
  | .multipleUse o =>
    s!"error: the argument '{o.display}' cannot be used multiple times\n\nUsage: {s.usage}\n\n{moreInfo}"
  | .unexpectedValue o v =>
    s!"error: unexpected value '{v}' for '{o.display}' found; no more were expected\n\nUsage: {s.usage}\n\n{moreInfo}"
  | .conflict a b =>
    s!"error: the argument '{keyDisplay s a}' cannot be used with '{keyDisplay s b}'\n\nUsage: {s.usage}\n\n{moreInfo}"
  | .missing ns =>
    "error: the following required arguments were not provided:\n" ++
      String.join (ns.map fun n => "  " ++ n ++ "\n") ++ s!"\nUsage: {s.usage}\n\n{moreInfo}"

/-! ## Options shared by the subcommands (upstream's `GeneralOpts`, `InputOutput`, …) -/

def verbose : Opt := { key := "verbose", long := some "verbose", short := some 'v', takes := .count }
def color : Opt := { key := "color", long := some "color", takes := .value "COLOR" ["auto", "never", "always", "always-ansi"] }
def output : Opt := { key := "output", long := some "output", short := some 'o', takes := .value "OUTPUT" [] }
def generateDwarf : Opt := { key := "generate-dwarf", long := some "generate-dwarf", takes := .value "lines|full" ["lines", "full"] }
def g : Opt := { key := "g", short := some 'g' }
def wat : Opt := { key := "wat", long := some "wat", short := some 't' }
def features : Opt := { key := "features", long := some "features", takes := .value "FEATURES" [], multiple := true }
def allFeatures : Opt := { key := "all-features", long := some "all-features" }
def general : List Opt := [verbose, color]
def input : Pos := { key := "input", name := "INPUT" }
def wit : Pos := { key := "wit", name := "WIT", required := true }

end Silmaril.Wasm.Tools.Component.Args
