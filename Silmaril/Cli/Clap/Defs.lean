module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Cli.Surface.Defs

/-!
# The clap dialect of argument grammars

Real tools (`wasm-tools`, written with Rust's clap, and the Binaryen toolkit) are specified by
args `Command`s (`Silmaril.Cli.Args`): the grammar holds everything clap's conventions need
(optional values with the value a bare occurrence means, `Opt.valueOptional` and
`Opt.missing`; exact single-dash tokens, `Opt.exact`; value checks, `Command.checks`; and
`requires` / `conflicts_with`, `Command.rules`). A `Clap.Tool` adds only what concerns clap's
presentation: the text after the option table (`after`), whether groups have clap's implicit
`help NAME…` subcommand (`helpSub`), and the exit code of a usage error (`usageExit`).

**The reading** `Tool.read` is the args front end behind a clap *pre-pass*: `pre` walks the
command line as clap does and stops early with help, the version or one of clap's usage
errors (a value that looks like an option, `-o --stats`; an unknown `--no-x`; …); otherwise
the args parser `scan` (proved sound and complete, `Silmaril.Cli.Args.Thms`) reads the very same
argument vector, clusters (`-tg`) and attached values (`-ofile`, `-o=file`) included, and
`judge` (types, checks, resolution, rules) decides. `Silmaril.Cli.Clap.Thms`: when the pre-pass
passes, the reading agrees with the args front end `interpret` (`read_agrees`).

A tool's clap view (`Tool.surface`, a `Silmaril.Cli.Surface.Tool`) is *derived* from the same
data: the `-h` help in clap's layout, usage lines and the test corpus are functions of it, so
they cannot drift from the grammar. `compare` sets the reading beside the surface's reference
reading (`Surface.Command.parse`) on one argument vector.

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

@[expose] public section

namespace Silmaril.Cli.Clap

open Silmaril.Cli

/-! ## Tools -/

/-- The value checks of clap (now part of the args grammar, `Silmaril.Cli.ValueCheck`). -/
abbrev Check := ValueCheck

/-- **A tool in the clap dialect**: an args grammar and clap's presentation. -/
structure Tool where
  grammar : Command
  /-- the text after the option table, by command path (below the root) -/
  after : List (List String × String) := []
  /-- groups have clap's implicit `help NAME…` subcommand -/
  helpSub : Bool := true
  /-- the exit code of a usage error -/
  usageExit : Nat := 2
  deriving Inhabited

/-! ## The clap view (derived) -/

/-- The clap view of an option: the first one-letter single-dash name is its short name, the
longer single-dash names (and all of them for an `exact` option) are exact tokens (`-O2`,
`-all`); a repeatable flag with a one-letter name is counted (`-v...`), other repeatable flags
are switches that may repeat. -/
def surfaceOpt (o : Opt) : Surface.Opt :=
  let one := if o.exact then [] else o.short.filter (·.length == 1)
  let multi := if o.exact then o.short else o.short.filter (·.length != 1)
  let mv := if o.metavar.isEmpty then o.id.toUpper else o.metavar
  { short := (one.head?.bind fun s => s.toList.head?)
    long := o.long.head?
    arg := match o.arg with
      | none => if o.repeated && !one.isEmpty then .count else .switch
      | some _ => if o.valueOptional then .optValue mv else .value mv
    help := o.help
    default := o.default
    choices := match o.arg with
      | some (.enum cs) => cs
      | _ => []
    required := o.required
    multiple := o.repeated
    tokens := multi.map ("-" ++ ·) }

/-- The clap view of a positional. -/
def surfacePos (p : Pos) : Surface.Pos :=
  { metavar := p.metavarOr
    help := p.help
    required := p.arity == .one || p.arity == .atLeastOne
    many := p.arity == .many || p.arity == .atLeastOne
    choices := match p.type with
      | .enum cs => cs
      | _ => [] }

mutual
/-- The clap view of the command at `path` (below the root). -/
def surfaceCmd (t : Tool) (path : List String) : Command → Surface.Command
  | ⟨n, _, ab, os, ps, subs, _, _, _, _, _⟩ =>
    { name := n, about := ab, pos := ps.map surfacePos, opts := os.map surfaceOpt,
      subs := surfaceCmds t path subs, after := (t.after.lookup path).getD "",
      helpSub := t.helpSub }
/-- `surfaceCmd` of the subcommands of the command at `path`. -/
def surfaceCmds (t : Tool) (path : List String) : List Command → List Surface.Command
  | [] => []
  | s :: ss => surfaceCmd t (path ++ [s.name]) s :: surfaceCmds t path ss
end

/-- **The clap view of a tool**: help, usage, paths and corpus come from here. -/
def Tool.surface (t : Tool) : Surface.Tool where
  root := surfaceCmd t [] t.grammar
  exits := t.grammar.exits.map fun e => ⟨e.1, e.2⟩
  usageExit := t.usageExit

/-! ## The pre-pass: where clap stops before the args reading -/

/-- Why the pre-pass stopped early. -/
inductive Early where
  | help (path : List String)
  | version
  | error (msg : String)
  deriving Repr, DecidableEq

/-- A token that cannot be a value: `-` and at least one more character. -/
def optionLike (s : String) : Bool :=
  match s.toList with
  | '-' :: _ :: _ => true
  | _ => false

/-- The help flag (a `--help` option with a value is an ordinary option). -/
def isHelpOpt (o : Opt) : Bool := o.id == "help" && o.arg.isNone

/-- The version flag (`metadata add --version <V>` is an ordinary option). -/
def isVersionOpt (o : Opt) : Bool := o.id == "version" && o.arg.isNone

/-- How clap names an option in messages: `--output <OUTPUT>`, `-g`, `--validate[=<M>]`. -/
def display (o : Opt) : String :=
  let so := surfaceOpt o
  let name := match so.long, so.short with
    | some l, _ => "--" ++ l
    | none, some c => "-" ++ String.singleton c
    | none, none => so.tokens.headD ""
  name ++ (match so.arg with
    | .value m => " <" ++ m ++ ">"
    | .optValue m => "[=<" ++ m ++ ">]"
    | .count => "..."
    | .switch => "")

/-- How clap names a positional in messages: `<SHELL>`, `[INPUT]`, `[ADDRESSES]...`. -/
def displayPos (p : Pos) : String := (surfacePos p).spec

/-- `a value is required for …`. -/
def valueRequired (o : Opt) : String :=
  "a value is required for '" ++ display o ++ "' but none was supplied"

/-- What one token does in the pre-pass. -/
inductive Step where
  /-- go on with the next token -/
  | next
  /-- the next token is the value of `o` -/
  | value (o : Opt)
  /-- this token selects the subcommand `s` (as the parser sees it) -/
  | enter (s : Command)
  /-- `--`: the rest are positionals -/
  | stop
  /-- stop early -/
  | early (e : Early)

/-- `help NAME…` in a group. -/
def helpOf (c : Command) (path rest : List String) : Early :=
  match c.walk rest with
  | some _ => .help (path ++ rest)
  | none => .error ("unrecognized subcommand '" ++ " ".intercalate rest ++ "'")

/-- One option occurrence, with an attached value `v` (after `=`). -/
def optStep (path : List String) (o : Opt) (v : Option String) : Step :=
  if isHelpOpt o then .early (.help path)
  else if isVersionOpt o then .early .version
  else match o.arg, v with
    | none, none => .next
    | none, some x =>
      .early (.error ("unexpected value '" ++ x ++ "' for '" ++ display o ++
        "' found; no more were expected"))
    | some _, some _ => .next
    | some _, none => if o.valueOptional then .next else .value o

/-- A short cluster `-abc` (letters of `clusterOpts`): the option that needs the next token as
its value, if any. -/
def cluster (c : Command) (path : List String) : List Char → Except Early (Option Opt)
  | [] => .ok none
  | ch :: cs =>
    let name := String.singleton ch
    match findShort (clusterOpts c.opts) name with
    | none => .error (.error ("unexpected argument '-" ++ name ++ "' found"))
    | some o =>
      if isHelpOpt o then .error (.help path)
      else if isVersionOpt o then .error .version
      else match o.arg with
        | none => cluster c path cs
        | some _ => if cs.isEmpty && !o.valueOptional then .ok (some o) else .ok none

/-- What the token `tok` does at command `c` (reached by `path`, root name first). The token
is classified as the args dialect does (`classify`). -/
def step (t : Tool) (c : Command) (path : List String) (tok : String) (rest : List String) :
    Step :=
  match classify tok with
  | .dashdash => .stop
  | .long n v =>
    match findLong c.opts n with
    | none => .early (.error ("unexpected argument '" ++ tok ++ "' found"))
    | some o => optStep path o v
  | .short n =>
    match findShort c.opts n with
    | some o => optStep path o none
    | none =>
      match cluster c path n.toList with
      | .error e => .early e
      | .ok none => .next
      | .ok (some o) => .value o
  | .word _ =>
    if c.subs.isEmpty then .next
    else if t.helpSub && tok == "help" then .early (helpOf c path rest)
    else match findSub c.subs tok with
      | some s => .enter (c.child s)
      | none => .early (.error ("unrecognized subcommand '" ++ tok ++ "'"))

/-- **The pre-pass**: where clap stops early on a command line (`none`: it reads it as the
args dialect does). -/
def pre (t : Tool) : Command → List String → List String → Option Early
  | _, _, [] => none
  | c, path, tok :: rest =>
    match step t c path tok rest with
    | .early e => some e
    | .stop => none
    | .next => pre t c path rest
    | .enter s => pre t s (path ++ [s.name]) rest
    | .value o =>
      match rest with
      | [] => some (.error (valueRequired o))
      | x :: rest' => if optionLike x then some (.error (valueRequired o)) else pre t c path rest'

/-! ## The reading -/

/-- What a command line asks for, in the clap dialect. -/
inductive Outcome where
  /-- run with this invocation and these matches -/
  | run (fs : Invocation) (m : Matches)
  /-- run, unless a value the specification leaves undecided is rejected (a usage error) -/
  | undecided (fs : Invocation) (m : Matches) (why : String)
  /-- the help of the command at this path, on stdout, exit 0 -/
  | help (path : List String)
  /-- the version, on stdout, exit 0 -/
  | version
  /-- a group without a subcommand: its help on stderr, a usage error -/
  | needCommand (path : List String)
  /-- a usage error -/
  | error (msg : String)
  deriving Repr, DecidableEq

/-- The exit code the reading fixes (`none`: the program decides). -/
def Outcome.exit (t : Tool) : Outcome → Option Nat
  | .run _ _ | .undecided _ _ _ => none
  | .help _ | .version => some 0
  | .needCommand _ | .error _ => some t.usageExit

/-- The exit class, as the tests print it: `0`, the usage exit, `run`, or `run|2` when a run
may still be refused. -/
def Outcome.cls (t : Tool) : Outcome → String
  | .run _ _ => "run"
  | .undecided _ _ _ => "run|" ++ toString t.usageExit
  | o => toString ((o.exit t).getD 0)

/-- The commands of an invocation's frames, the root first. -/
def frameCommands : Command → Invocation → List Command
  | _, [] => []
  | c, _ :: rest => c ::
    match rest with
    | [] => []
    | g :: _ =>
      match findSub c.subs g.cmd with
      | some s => frameCommands (c.child s) rest
      | none => []

/-- The clap name of the option or positional `id` of an invocation (deepest level first). -/
def nameOf (t : Tool) (fs : Invocation) (id : String) : String :=
  let cs := (frameCommands t.grammar fs).reverse
  match cs.findSome? (fun c => findId c.opts id) with
  | some o => display o
  | none =>
    match cs.findSome? (fun c => c.pos.find? (·.id == id)) with
    | some p => displayPos p
    | none => id

/-- The message of a broken rule, naming options with `name`. -/
def ruleMessage (name : String → String) : Rule → String
  | .requires _ b => "the following required arguments were not provided:\n  " ++ name b
  | .conflicts a b => "the argument '" ++ name a ++ "' cannot be used with '" ++ name b ++ "'"

/-- A usage error of the args front end, in clap's words. -/
def Tool.message (t : Tool) (fs : Invocation) : ArgError → String
  | .repeated id => "the argument '" ++ nameOf t fs id ++ "' cannot be used multiple times"
  | .missingOption id | .missingArgument id =>
    "the following required arguments were not provided:\n  " ++ nameOf t fs id
  | .badValue id v (.enum cs) => "invalid value '" ++ v ++ "' for '" ++ nameOf t fs id ++
      "'\n  [possible values: " ++ ", ".intercalate cs ++ "]"
  | .badValue id v _ => "invalid value '" ++ v ++ "' for '" ++ nameOf t fs id ++ "'"
  | e => e.message

/-- What an invocation (as the args parser returns it) asks for: the args checks (`judge`:
values of the occurrences in order, resolution, rules, resolved values), in clap's words. -/
def Tool.readInv (t : Tool) (env : String → Option String) (fs : Invocation) : Outcome :=
  match judge t.grammar env fs with
  | .badValue _ o x =>
    .error ("invalid value '" ++ x ++ "' for '" ++ display o ++ "'" ++
      match o.arg with
      | some (.enum cs) => "\n  [possible values: " ++ ", ".intercalate cs ++ "]"
      | _ => "")
  | .unresolved (_, .missingCommand _) => .needCommand (fs.map (·.cmd))
  | .unresolved (_, e) => .error (t.message fs e)
  | .broken _ r => .error (ruleMessage (nameOf t fs) r)
  | .rejected _ id v => .error ("invalid value '" ++ v ++ "' for '" ++ nameOf t fs id ++ "'")
  | .undecided m id =>
    .undecided fs m ("the value of '" ++ nameOf t fs id ++ "' is checked by the program")
  | .ok m => .run fs m

/-- **The reading** of an argument vector (without the program name) in the environment
`env`: the pre-pass, then the args parser `scan` on the same vector, then `readInv`. -/
def Tool.read (t : Tool) (env : String → Option String) (argv : List String) : Outcome :=
  match pre t t.grammar [t.grammar.name] argv with
  | some (.help p) => .help p
  | some .version => .version
  | some (.error msg) => .error msg
  | none =>
    match scan t.grammar argv with
    | .error (_, e) => .error e.message
    | .ok fs => t.readInv env fs

/-! ## Invocations the pre-pass passes

The args normal form (`render`) passes the pre-pass when nothing in it means something else
in clap's dialect: no help or version flag, no value that looks like an option, no subcommand
named `help` where groups have the implicit `help` subcommand, and no negation `--no-x`.
`Silmaril.Cli.Clap.Thms`: `pre_render`, `read_render`. -/

/-- An occurrence the pre-pass passes in normal form. -/
def PlainOcc (c : Command) (p : String × Given) : Prop :=
  ∀ o, findId c.opts p.1 = some o → isHelpOpt o = false ∧ isVersionOpt o = false ∧
    p.2 ≠ .off ∧ ∀ x, p.2 = .val x → optionLike x = false

/-- An invocation whose normal form the pre-pass passes. -/
def Plain (t : Tool) : Command → Invocation → Prop
  | _, [] => True
  | c, f :: rest => (∀ p ∈ f.opts, PlainOcc c p) ∧
    match rest with
    | [] => True
    | g :: _ => (t.helpSub = true → g.cmd ≠ "help") ∧
      ∀ s, findSub c.subs g.cmd = some s → Plain t (c.child s) rest

/-- Help and version are flags: no option named `help` takes a value anywhere, and no root
option named `version` does (decidable). Then a command line the pre-pass passes asks the
args front end for neither help nor the version (`read_agrees`). -/
def HelpFlags (c : Command) : Prop :=
  (∀ o ∈ c.allOpts, o.id = "help" → o.arg = none) ∧ ∀ o ∈ c.opts, o.id = "version" → o.arg = none

instance (c : Command) : Decidable (HelpFlags c) := by unfold HelpFlags; infer_instance

/-- The clap reading and the args front end agree: the same run (the clap reading may leave a
value to the program), help and version; usage errors on both sides. -/
def Outcome.Agrees : Outcome → Silmaril.Cli.Outcome → Prop
  | .run _ m, .run m' => m = m'
  | .undecided _ m _, .run m' => m = m'
  | .help p, .help q => p = q
  | .version, .version _ => True
  | .needCommand _, .error _ _ => True
  | .error _, .error _ _ => True
  | _, _ => False

/-! ## Beside the surface's reference reading -/

/-- The clap view's key of the option `id` of command `c`. -/
def keyOf (c : Command) (id : String) : String :=
  match findId c.opts id with
  | some o => (surfaceOpt o).key
  | none => id

/-- The value an occurrence of `o` gives, as the clap view records it: a bare occurrence of
an optional value gives its missing value. -/
def givenValue? (o : Option Opt) : Given → Option String
  | .val x => some x
  | .on => o.bind fun o => if o.arg.isSome then o.missing else none
  | .off => none

/-- The occurrences of an invocation, keyed as in the clap view. -/
def occurrences : Command → Invocation → List (String × Option String)
  | _, [] => []
  | c, f :: rest => f.opts.map (fun p => (keyOf c p.1, givenValue? (findId c.opts p.1) p.2)) ++
    match rest with
    | [] => []
    | g :: _ =>
      match findSub c.subs g.cmd with
      | some s => occurrences (c.child s) rest
      | none => []

/-- An invocation as the clap view records it. -/
def toSurfaceInv (t : Tool) (fs : Invocation) : Surface.Invocation :=
  { path := (fs.drop 1).map (·.cmd), opts := occurrences t.grammar fs,
    args := (fs.getLast?.map (·.args)).getD [] }

/-- The surface's record of a bare optional-value occurrence, with the value it means. -/
def normalizeInv (t : Tool) (inv : Surface.Invocation) : Surface.Invocation :=
  { inv with opts := inv.opts.map fun (k, v) =>
      match v with
      | some x => (k, some x)
      | none =>
        match (t.grammar.walk inv.path).bind (fun c => findLong c.opts k) with
        | some o => if o.arg.isSome then (k, o.missing) else (k, none)
        | none => (k, none) }

/-- The two readings of one vector, compared. -/
inductive Verdict where
  /-- the same outcome (usage errors and a missing subcommand count as one class) -/
  | same
  /-- the reading refuses with a value type or rule the surface does not model -/
  | stricter (msg : String)
  /-- the surface runs; the reading allows the run but leaves a value to the program -/
  | undecided
  /-- anything else -/
  | differ
  deriving Repr, DecidableEq

/-- Compare `Tool.read` with the reference reading of the derived surface. -/
def compare (t : Tool) (argv : List String) : Verdict :=
  match t.read (fun _ => none) argv, t.surface.root.parse argv with
  | .help p, .help q => if p == q then .same else .differ
  | .version, .version _ => .same
  | .error _, .error _ | .error _, .needCommand _ => .same
  | .needCommand _, .error _ | .needCommand _, .needCommand _ => .same
  | .run fs _, .run inv =>
    if toSurfaceInv t fs == normalizeInv t inv then .same else .differ
  | .undecided fs _ _, .run inv =>
    if toSurfaceInv t fs == normalizeInv t inv then .undecided else .differ
  | .error msg, .run _ => .stricter msg
  | _, _ => .differ

/-- The vectors of the clap view's corpus on which the readings are not `same`. -/
def disagreements (t : Tool) (file : String := "nonexistent-cli-spec.wasm") :
    List (List String × Verdict) :=
  (t.surface.root.corpus file).filterMap fun v =>
    match compare t v with
    | .same => none
    | r => some (v, r)

end Silmaril.Cli.Clap
