module

public import Silmaril.Cli.Institution.Defs
public import Silmaril.Cli.Io.Command.Defs
public import Silmaril.Cli.Clap.Main.Defs

/-!
# Standard problems: `--help` works, `--version` works

Two conventions nearly every command-line program follows, stated once for every model of the
CLI institution (`Silmaril.Cli.Institution`): Lean programs (`Silmaril.Cli.Io.Prog`), programs
behind a derived front end (`Command.spec`, `Clap.Tool.spec`), and any other program semantics
with a reduct to the full interface `L3` (a WASI component, an ELF process model).

The problems do not pin the help text. A **variant** says what triggers the request, what
the answer must look like, and whether the run must leave everything else alone:

* `HelpVariant`: which spellings trigger help (`--help`, `-h`, a `help` subcommand word), at
  which subcommand paths (`tool sub --help`), what `--help` followed by more arguments must do
  (`Extra`: no claim, help wins, help wins over operands, a usage error, help or a usage error),
  the reply (`Reply`: exit code `0` or any, the text on stdout or on stdout or stderr, non-empty,
  required substrings such as the program name or `Usage:`), optional exact texts per path, and
  `quiet` (no file read or changed, no stdin consumed);
* `VersionVariant`: `--version`, `-V`, the reply, an optional version string the text must
  contain, `quiet`.

Each variant gives a sentence at `L2` (`sen2`: program name, arguments and stdin to stdout,
stderr and exit code) and at `L3` (`sen`, a `Silmaril.Cli.Spec`: `sen2` on the projections, and
`quiet` on the full observation). Both are **safety** sentences: they constrain only the
invocations that ask for help or the version, so they are a first check one can make of a very
complicated binary before specifying anything else.

Named variants (`HelpVariant.named`, `VersionVariant.named`) carry stable string ids such as
`cli.help.basic`; `Silmaril.Project.Shapes.Cli` registers them as standard problem shapes.

**Front ends.** `Command.helpTriggers`, `Clap.Tool.helpTriggers` and the version forms are
decidable conditions under which a derived front end answers exactly the requests a variant
names; `Silmaril.Cli.Info.Thms` proves that the front end's spec then refines the variant's
sentence, and that every grammar built with `withHelp`, `withVersion` or `helpEverywhere`
meets them.

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

@[expose] public section

namespace Silmaril.Cli.Info

open Silmaril.Cli Silmaril.Cli.Institution

/-! ## Replies -/

/-- The exit code a help or version run may end with. -/
inductive ExitReq where
  /-- exit `0` -/
  | zero
  /-- any exit code -/
  | any
deriving DecidableEq, Repr, Inhabited

/-- The exit code `c` is allowed. -/
def ExitReq.Ok : ExitReq → ExitCode → Prop
  | .zero, c => c = 0
  | .any, _ => True

/-- Where the text goes. -/
inductive Dest where
  /-- on stdout, nothing on stderr -/
  | stdout
  /-- on stdout or stderr (the text is both streams, stdout first) -/
  | either
deriving DecidableEq, Repr, Inhabited

/-- The streams are used as `d` says. -/
def Dest.Ok : Dest → Spec.Out → Prop
  | .stdout, o => o.stderr = []
  | .either, _ => True

/-- The text of the reply. -/
def Dest.text : Dest → Spec.Out → Bytes
  | .stdout, o => o.stdout
  | .either, o => o.stdout ++ o.stderr

/-- **What the answer to a help or version request looks like.** -/
structure Reply where
  /-- the exit code -/
  exit : ExitReq := .zero
  /-- where the text goes -/
  dest : Dest := .stdout
  /-- the text is not empty -/
  nonEmpty : Bool := true
  /-- strings the text contains (the program name, `Usage:`, …) -/
  mentions : List String := []
deriving DecidableEq, Repr, Inhabited

/-- The text satisfies the reply's conditions on it. -/
def Reply.TextOk (r : Reply) (text : Bytes) : Prop :=
  (r.nonEmpty = true → text ≠ []) ∧ ∀ m ∈ r.mentions, utf8 m <:+: text

instance (r : Reply) (text : Bytes) : Decidable (r.TextOk text) :=
  haveI : ∀ a b : Bytes, Decidable (a <:+: b) := fun a b =>
    decidable_of_iff (a.isInfixOf_internal b = true) List.isInfixOf_internal_iff_isInfix
  by unfold Reply.TextOk; infer_instance

/-- An observation shows the reply. -/
def Reply.Shows (r : Reply) (o : Spec.Out) : Prop :=
  r.exit.Ok o.exit ∧ r.dest.Ok o ∧ r.TextOk (r.dest.text o)

/-- **A loose usage error** at `L2`: a nonzero exit and nothing on stdout. -/
def UsageErr (o : Spec.Out) : Prop := o.exit ≠ 0 ∧ o.stdout = []

/-- **Nothing else happens** (`L3`): no file changed, read or logged, no stdin consumed. -/
def Quiet (i : Input) (o : Obs) : Prop :=
  o.fs = i.fs ∧ o.reads = [] ∧ o.consumed = 0 ∧ o.log = []

/-! ## Help -/

/-- What `--help` followed by more arguments must do. -/
inductive Extra where
  /-- no claim -/
  | ignore
  /-- help wins over anything that follows (clap's pre-pass) -/
  | wins
  /-- help wins over following operands (words not starting with `-`) -/
  | winsOperands
  /-- a usage error -/
  | error
  /-- help or a usage error (a derived args front end: help unless the rest does not parse) -/
  | either
deriving DecidableEq, Repr, Inhabited

/-- An operand word: it does not start with `-`. -/
def Operand (w : String) : Prop := w.toList.head? ≠ some '-'

instance (w : String) : Decidable (Operand w) := by unfold Operand; infer_instance

/-- The arguments after `--help` about which `e` makes a claim. -/
def Extra.Covers : Extra → List String → Prop
  | .ignore, _ => False
  | .winsOperands, rest => ∀ w ∈ rest, Operand w
  | _, _ => True

/-- The claim of `e` about the arguments `rest` after `--help`, given what showing help (`h`)
and a usage error (`u`) are. -/
def Extra.Claim : Extra → List String → Prop → Prop → Prop
  | .ignore, _, _, _ => True
  | .wins, _, h, _ => h
  | .winsOperands, rest, h, _ => (∀ w ∈ rest, Operand w) → h
  | .error, _, _, u => u
  | .either, _, h, u => h ∨ u

/-- **A variant of "`--help` works".** -/
structure HelpVariant where
  /-- `--help` triggers help -/
  long : Bool := true
  /-- `-h` triggers help -/
  short : Bool := false
  /-- the subcommand word `help` triggers help: `tool help`, `tool help sub` -/
  word : Bool := false
  /-- subcommand paths besides the root where the spellings must work (`tool sub --help`) -/
  paths : List (List String) := []
  /-- what more arguments after the spelling must give -/
  extra : Extra := .ignore
  /-- the reply -/
  reply : Reply := {}
  /-- exact texts, by subcommand path (the words before the spelling) -/
  texts : List (List String × String) := []
  /-- nothing else happens: no file changed or read, no stdin consumed -/
  quiet : Bool := true
deriving DecidableEq, Repr, Inhabited

namespace HelpVariant

variable (v : HelpVariant)

/-- The subcommand paths where help must work: the root and `paths`. -/
def roots : List (List String) := [] :: v.paths

/-- The spellings that trigger help. -/
def tokens : List String :=
  (if v.long then ["--help"] else []) ++ (if v.short then ["-h"] else [])

/-- The text fits the variant at the path `p`. -/
def Fits (p : List String) (text : Bytes) : Prop :=
  v.reply.TextOk text ∧ ∀ q ∈ v.texts, q.1 = p → text = utf8 q.2

instance (p : List String) (text : Bytes) : Decidable (v.Fits p text) := by
  unfold Fits; infer_instance

/-- The observation shows help for the path `p`. -/
def Shows (p : List String) (o : Spec.Out) : Prop :=
  v.reply.Shows o ∧ ∀ q ∈ v.texts, q.1 = p → v.reply.dest.text o = utf8 q.2

/-- **The variant as an `L2` sentence**: at each path `p`, `p ++ [t]` for a spelling `t`
shows help, `help :: p` too when `word` is set, and `p ++ t :: rest` does what `extra`
says. -/
def sen2 : Sen Level.command.sig := fun (a : In2) (o : Spec.Out) =>
  ∀ p ∈ v.roots,
    (∀ t ∈ v.tokens, a.args = p ++ [t] → v.Shows p o) ∧
    (v.word = true → a.args = "help" :: p → v.Shows p o) ∧
    (∀ t ∈ v.tokens, ∀ rest, rest ≠ [] → a.args = p ++ t :: rest →
      v.extra.Claim rest (v.Shows p o) (UsageErr o))

/-- The argument vectors the variant makes a claim about. -/
def Asked (args : List String) : Prop :=
  ∃ p ∈ v.roots,
    (∃ t ∈ v.tokens, args = p ++ [t] ∨ ∃ rest, rest ≠ [] ∧ args = p ++ t :: rest ∧
      v.extra.Covers rest) ∨
    (v.word = true ∧ args = "help" :: p)

/-- **The variant as an `L3` sentence** (a `Spec`): `sen2` on what `L2` sees, and, when
`quiet`, nothing else happens on the invocations it asks about. -/
def sen : Spec := fun (i : Input) (o : Obs) =>
  v.sen2 (Level.command.inProj i) (Level.command.outProj o) ∧
    (v.quiet = true → v.Asked i.args → Quiet i o)

/-! ### Named variants -/

/-- `--help` at the root: exit 0, non-empty text on stdout, nothing on stderr, nothing else. -/
def basic : HelpVariant := {}

/-- `--help` and `-h` at the root. -/
def basicShort : HelpVariant := { short := true }

/-- `--help` at the root, any exit code, the text on stdout or stderr. -/
def loose : HelpVariant := { reply := { exit := .any, dest := .either } }

/-- `--help` and `-h` at the root and after each of the subcommand paths `ps`. -/
def subcommands (ps : List (List String)) : HelpVariant := { short := true, paths := ps }

/-- `--help` and `-h`, and help wins over everything after them (clap). -/
def wins : HelpVariant := { short := true, extra := .wins }

/-- `--help` and `-h`; after them, help or a usage error (a derived args front end). -/
def either : HelpVariant := { short := true, extra := .either }

/-- The named variants, with their ids (`cli.help.subcommands` takes its paths as a parameter
and is not listed). -/
def named : List (String × HelpVariant) :=
  [("cli.help.basic", basic), ("cli.help.short", basicShort), ("cli.help.loose", loose),
   ("cli.help.wins", wins), ("cli.help.either", either)]

end HelpVariant

/-! ## Version -/

/-- **A variant of "`--version` works".** -/
structure VersionVariant where
  /-- `--version` triggers it -/
  long : Bool := true
  /-- `-V` triggers it -/
  short : Bool := false
  /-- the reply -/
  reply : Reply := {}
  /-- a version string the text contains -/
  version? : Option String := none
  /-- nothing else happens -/
  quiet : Bool := true
deriving DecidableEq, Repr, Inhabited

namespace VersionVariant

variable (v : VersionVariant)

/-- The spellings. -/
def tokens : List String :=
  (if v.long then ["--version"] else []) ++ (if v.short then ["-V"] else [])

/-- The text fits the variant. -/
def Fits (text : Bytes) : Prop :=
  v.reply.TextOk text ∧ ∀ ver ∈ v.version?, utf8 ver <:+: text

instance (text : Bytes) : Decidable (v.Fits text) :=
  haveI : ∀ a b : Bytes, Decidable (a <:+: b) := fun a b =>
    decidable_of_iff (a.isInfixOf_internal b = true) List.isInfixOf_internal_iff_isInfix
  by unfold Fits; infer_instance

/-- The observation shows the version. -/
def Shows (o : Spec.Out) : Prop :=
  v.reply.Shows o ∧ ∀ ver ∈ v.version?, utf8 ver <:+: v.reply.dest.text o

/-- **The variant as an `L2` sentence.** -/
def sen2 : Sen Level.command.sig := fun (a : In2) (o : Spec.Out) =>
  ∀ t ∈ v.tokens, a.args = [t] → v.Shows o

/-- **The variant as an `L3` sentence.** -/
def sen : Spec := fun (i : Input) (o : Obs) =>
  v.sen2 (Level.command.inProj i) (Level.command.outProj o) ∧
    (v.quiet = true → ∀ t ∈ v.tokens, i.args = [t] → Quiet i o)

/-- `--version`: exit 0, non-empty text on stdout, nothing on stderr, nothing else. -/
def basic : VersionVariant := {}

/-- `--version` and `-V`. -/
def basicShort : VersionVariant := { short := true }

/-- `--version`, and the text contains `ver`. -/
def pinned (ver : String) : VersionVariant := { version? := some ver }

/-- The named variants with their ids (`cli.version.pinned` takes the version). -/
def named : List (String × VersionVariant) :=
  [("cli.version.basic", basic), ("cli.version.short", basicShort)]

end VersionVariant

/-! ## Stricter and looser variants -/

/-- `a` is at least as strict as `b`. -/
def ExitReq.Le (a b : ExitReq) : Prop := b = .any ∨ a = b

/-- `a` is at least as strict as `b`. -/
def Dest.Le (a b : Dest) : Prop := b = .either ∨ a = b

/-- `a` claims at least what `b` claims. -/
def Extra.Le (a b : Extra) : Prop :=
  b = .ignore ∨ a = b ∨ (a = .wins ∧ (b = .winsOperands ∨ b = .either)) ∨
    (a = .error ∧ b = .either)

/-- `r` is at least as strict as `s`. -/
def Reply.Le (r s : Reply) : Prop :=
  r.exit.Le s.exit ∧ r.dest.Le s.dest ∧ (s.nonEmpty = true → r.nonEmpty = true) ∧
    s.mentions ⊆ r.mentions

/-- **`v` is at least as strict as `w`**: it claims at every request `w` claims at, and
claims more. -/
def HelpVariant.Le (v w : HelpVariant) : Prop :=
  (w.long = true → v.long = true) ∧ (w.short = true → v.short = true) ∧
    (w.word = true → v.word = true) ∧ w.paths ⊆ v.paths ∧ v.extra.Le w.extra ∧
    v.reply.Le w.reply ∧ w.texts ⊆ v.texts ∧ (w.quiet = true → v.quiet = true)

/-- **`v` is at least as strict as `w`.** -/
def VersionVariant.Le (v w : VersionVariant) : Prop :=
  (w.long = true → v.long = true) ∧ (w.short = true → v.short = true) ∧
    v.reply.Le w.reply ∧ (∀ ver ∈ w.version?, v.version? = some ver) ∧
    (w.quiet = true → v.quiet = true)

instance (a b : ExitReq) : Decidable (a.Le b) := by unfold ExitReq.Le; infer_instance
instance (a b : Dest) : Decidable (a.Le b) := by unfold Dest.Le; infer_instance
instance (a b : Extra) : Decidable (a.Le b) := by unfold Extra.Le; infer_instance
instance (a b : Reply) : Decidable (a.Le b) := by unfold Reply.Le; infer_instance
instance (v w : HelpVariant) : Decidable (v.Le w) := by unfold HelpVariant.Le; infer_instance
instance (v w : VersionVariant) : Decidable (v.Le w) := by
  unfold VersionVariant.Le; infer_instance

/-! ## Models -/

/-- **A Lean program as a model** of the full interface: its one observation per input. -/
def _root_.Silmaril.Cli.Io.Prog.model (p : Io.Prog ExitCode) : Model Level.full.sig :=
  ⟨fun i o => o = p.obs i⟩

/-- **A specification as a model**: the program semantics whose runs are the observations it
allows (for instance `Beh.toSpec (c.modelMain run)`, the model of `Command.main`). -/
def ofSpec (S : Spec) : Model Level.full.sig := ⟨S⟩

/-! ## Derived front ends: when they answer a variant -/

/-- The level the args parser reaches through the subcommand words `p`. -/
def _root_.Silmaril.Cli.Command.pathLevel : Command → List String → Option Command
  | c, [] => some c
  | c, w :: ws =>
    if isWord w && !c.subs.isEmpty then
      match findSub c.subs w with
      | some s => (c.child s).pathLevel ws
      | none => none
    else none

/-- The names of the subcommands the words `p` select (below `c`). -/
def _root_.Silmaril.Cli.Command.subNames : Command → List String → List String
  | _, [] => []
  | c, w :: ws =>
    match findSub c.subs w with
    | some s => (c.child s).name :: (c.child s).subNames ws
    | none => []

/-- The help path (root name first) of the words `p`. -/
def _root_.Silmaril.Cli.Command.pathNames (c : Command) (p : List String) : List String :=
  c.name :: c.subNames p

/-- The token `t` reads, in the option table `os`, as one flag occurrence of the option `id`. -/
def readsAs (os : List Opt) (id t : String) : Bool :=
  match classify t with
  | .long n none => (findLong os n).any fun o => o.id == id && !o.takesValue
  | .short n => (findShort os n).any fun o => o.id == id && !o.takesValue
  | _ => false

/-- The claims about extra arguments an args front end meets. -/
def argsExtra : Extra → Bool
  | .ignore | .winsOperands | .either => true
  | .wins | .error => false

/-- **The derived args front end of `c` answers the help requests of `v`**: no `help` word,
an extra-argument claim it meets, and at every path of `v` the words select a level where
every spelling reads as the help flag (a level without subcommands for `winsOperands`). -/
def _root_.Silmaril.Cli.Command.helpTriggers (c : Command) (v : HelpVariant) : Bool :=
  !v.word && argsExtra v.extra && v.roots.all fun p =>
    match c.pathLevel p with
    | none => false
    | some d => v.tokens.all (readsAs d.opts "help") &&
        (v.extra != .winsOperands || d.subs.isEmpty)

/-- The bytes the args front end prints for help after the words `p`. -/
def _root_.Silmaril.Cli.Command.helpBytes (c : Command) (p : List String) : Bytes :=
  utf8 ((c.at (c.pathNames p)).help (c.pathNames p) ++ "\n")

/-- **The derived args front end of `c` answers the version requests of `v`.** -/
def _root_.Silmaril.Cli.Command.versionTriggers (c : Command) (v : VersionVariant) : Bool :=
  c.version.isSome && v.tokens.all (readsAs c.opts "version")

/-- The bytes the args front end prints for the version. -/
def _root_.Silmaril.Cli.Command.versionBytes (c : Command) : Bytes :=
  utf8 (c.name ++ " " ++ c.version.getD "" ++ "\n")

namespace Clap

open Silmaril.Cli.Clap

/-- The token `t` is, in the pre-pass at a level with options `os`, an option `f` accepts
(a long name, possibly with a value, or a single-dash name). -/
def stepsAs (os : List Opt) (f : Opt → Bool) (t : String) : Bool :=
  match classify t with
  | .long n _ => (findLong os n).any f
  | .short n => (findShort os n).any f
  | _ => false

/-- The level clap's pre-pass reaches through the subcommand words `p`. -/
def pathLevel (t : Tool) : Command → List String → Option Command
  | c, [] => some c
  | c, w :: ws =>
    if isWord w && !c.subs.isEmpty && !(t.helpSub && w == "help") then
      match findSub c.subs w with
      | some s => pathLevel t (c.child s) ws
      | none => none
    else none

/-- The version flag, not shadowed by the help flag. -/
def versionFlag (o : Opt) : Bool := !isHelpOpt o && isVersionOpt o

/-- **A clap front end answers the help requests of `v`**: no claim of a usage error; a
`help` word only where groups have clap's `help` subcommand; at every path, the words select
a level where every spelling is the help flag, and `help p` names a command. -/
def helpTriggers (t : Tool) (v : HelpVariant) : Bool :=
  v.extra != .error && (!v.word || (t.helpSub && !t.grammar.subs.isEmpty)) &&
    v.roots.all fun p =>
      (match pathLevel t t.grammar p with
       | none => false
       | some d => v.tokens.all (stepsAs d.opts isHelpOpt)) &&
      (!v.word || (t.grammar.walk p).isSome)

/-- The bytes a clap front end prints for help at the command path `q` (root name first). -/
def helpBytes (t : Tool) (q : List String) : Bytes := utf8 (t.helpText q ++ "\n")

/-- **A clap front end answers the version requests of `v`.** -/
def versionTriggers (t : Tool) (v : VersionVariant) : Bool :=
  v.tokens.all (stepsAs t.grammar.opts versionFlag)

/-- The bytes a clap front end prints for the version. -/
def versionBytes (t : Tool) : Bytes :=
  utf8 (t.grammar.name ++ " " ++ t.grammar.version.getD "" ++ "\n")

end Clap

end Silmaril.Cli.Info
