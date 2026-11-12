module

public import Silmaril.Cli.Args.Defs

/-!
# The getopt dialect of argument grammars

Most C programs read their arguments with `getopt(3)` (POSIX, the Utility Syntax Guidelines) or
GNU's `getopt_long(3)`. This file models both as data and as a reading of argument vectors, and
relates them to the args grammars of `Silmaril.Cli.Args` the way the clap dialect
(`Silmaril.Cli.Clap`) does: a **pre-pass** decides where the two readings may differ, and where
it passes, the getopt reading agrees with the args front end `interpret`.

## The tables

A getopt table (`Table`) is what a C program passes to the library: the *optstring* (`shorts`:
one character each, with `HasArg`: none, required `x:`, or optional `x::`; a leading `+`,
`Table.plus`; GNU's `W;`, `Table.wLong`) and, for `getopt_long`, the *longopts* array (`longs`:
a name, `HasArg`, and the key the option reports). `Table.ofOptstring` reads an optstring,
`Table.optstring` prints one. `Table.ofCommand` **derives** the table from an args `Command`:
every one-letter single-dash name is an optstring character, every long name a longopts entry,
with the option's `id` as the key.

## The reading (`parse`)

The conventions, one token at a time (`readTok`, then the loop `parse`):

* `-abc` is a cluster of option characters (`-a -b -c`); a character with a required argument
  takes the rest of the token (`-n5`) or else the next token, verbatim even when it starts with
  `-` (`-n 5`, `-n -5`); with an optional argument (`x::`) only the rest of the token (`-n5`;
  `-n` alone means no argument);
* `--name`, `--name=value`, `--name value` (required arguments only; an optional argument is
  given only as `--name=value`); `--name` may be shortened to any prefix that is unambiguous
  (`resolveLong`: an exact name wins; prefixes of several entries are ambiguous unless all of them
  mean the same option, as GNU grep's `--color` and `--colour`);
* with `W;` in the optstring, `-W name` and `-Wname` read as `--name` (an argument is given as
  `-W name=value`, or for `-Wname` in the next token; `-W name value` is not modelled);
* with `Table.longOnly` (`getopt_long_only`), a single-dash token that is not one optstring
  character is first read as a long name (`-name`, prefixes included), and as a cluster when
  no long name has it as a prefix (`readLongOnly`);
* `--` ends the options: every later token is an operand;
* `-` alone, and every token not starting with `-`, is an operand (by convention `-` means
  standard input).

**Ordering** (`Order`): POSIX `getopt` stops at the first operand (`requireOrder`): every later
token is an operand, even `-x`. GNU `getopt` and `getopt_long` *permute* by default: options may
follow operands (`permute`), unless the optstring starts with `+` or the environment variable
`POSIXLY_CORRECT` is set. So **the reading is a function of the argument vector and the
environment** (`Tool.order`, `Tool.read`); `Silmaril.Cli.Getopt.Front` reads both from a full
invocation (`Silmaril.Cli.Input`). GNU's third ordering (an optstring starting with `-`, operands
reported in order as options) is the in-order reading `parseInOrder` of
`Silmaril.Cli.Getopt.Stream`.

The result (`Parsed`) is the option occurrences in order (with the `Given` of the args dialect:
`on`, or `val x`), the operands, and the option tokens in order (`front`): the arguments glibc
moves to the front when it permutes. `Parsed.permuted` is the permuted argument vector;
`Silmaril.Cli.Getopt.Thms` proves that the GNU reading is the POSIX reading of it
(`parse_permuted`).

The first usage error ends the reading (`Error`): an unknown option character or name, a
missing argument, an argument given to a long option without one, or an ambiguous prefix.
(`getopt` itself reports the error and goes on; programs conventionally print their usage and
exit 2, which is what the args front end does. `Silmaril.Cli.Getopt.Stream` models the loop
that goes on: `parseAll`.)

## The relation to the args dialect

A `Tool` is an args grammar read by getopt: `Tool.read` parses with the derived table (`parse`)
and hands the one-frame invocation to the same checks as `interpret` (`afterScan`: help,
version, types, defaults, environment variables, positionals, value checks, rules). The
pre-pass `pre` finds the tokens on which the getopt and args readings may differ (`Diverge`):
an abbreviated long name, `-W`, a value `-o=x` (getopt: `=x`; args: `x`), and, in POSIX order,
an option-like token after the first operand. The theorem `read_agrees`
(`Silmaril.Cli.Getopt.Thms`) says that for grammars getopt can express (`Fits`) and argument
vectors the pre-pass passes, the getopt reading and `interpret` agree (the same outcome, or a
usage error on both sides).

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-! ## Tables -/

/-- Whether an option takes an argument (`has_arg` of `struct option`; in an optstring: `x`,
`x:`, `x::`). -/
inductive HasArg where
  | none
  | required
  | optional
  deriving DecidableEq, Repr, Inhabited

/-- An optstring character: the character, its argument, and the key it reports. -/
structure Short where
  ch : Char
  arg : HasArg := .none
  key : String := String.singleton ch
  deriving DecidableEq, Repr, Inhabited

/-- A longopts entry (`struct option`): the name, its argument, and the key it reports. -/
structure Long where
  name : String
  arg : HasArg := .none
  key : String := name
  deriving DecidableEq, Repr, Inhabited

/-- What a long entry means: two entries with the same target are the same option (a prefix of
both is not ambiguous). -/
def Long.target (l : Long) : HasArg × String := (l.arg, l.key)

/-- **A getopt table**: the optstring and the longopts array. -/
structure Table where
  shorts : List Short := []
  longs : List Long := []
  /-- the optstring starts with `+`: stop at the first operand -/
  plus : Bool := false
  /-- the optstring contains `W;`: `-W name` means `--name` -/
  wLong : Bool := false
  /-- read by `getopt_long_only`: a single-dash token may name a long option (`-name`) -/
  longOnly : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The argument suffix of an optstring character. -/
def HasArg.suffix : HasArg → String
  | .none => ""
  | .required => ":"
  | .optional => "::"

/-- The optstring of a table. -/
def Table.optstring (t : Table) : String :=
  (if t.plus then "+" else "") ++
    String.join (t.shorts.map fun s => String.singleton s.ch ++ s.arg.suffix) ++
    (if t.wLong then "W;" else "")

/-- The characters of an optstring after a leading `+` (and `:`). -/
def ofOptChars : List Char → List Short × Bool
  | [] => ([], false)
  | 'W' :: ';' :: r => ((ofOptChars r).1, true)
  | c :: ':' :: ':' :: r =>
    (⟨c, .optional, String.singleton c⟩ :: (ofOptChars r).1, (ofOptChars r).2)
  | c :: ':' :: r => (⟨c, .required, String.singleton c⟩ :: (ofOptChars r).1, (ofOptChars r).2)
  | c :: r => (⟨c, .none, String.singleton c⟩ :: (ofOptChars r).1, (ofOptChars r).2)

/-- **Read an optstring** (`"+n:c:qv"`): keys are the characters. A leading `:` (quiet error
reporting) is accepted and ignored. -/
def Table.ofOptstring (s : String) (longs : List Long := []) : Table :=
  let (plus, cs) := match s.toList with
    | '+' :: r => (true, r)
    | r => (false, r)
  let cs := match cs with
    | ':' :: r => r
    | r => r
  { shorts := (ofOptChars cs).1, longs, plus, wLong := (ofOptChars cs).2 }

/-! ## Reading one option token -/

/-- Usage errors of getopt (each with the whole token). -/
inductive Error where
  /-- an unknown option character or long name -/
  | unknown (tok : String)
  /-- an option without its required argument -/
  | missing (tok : String)
  /-- `--name=value` for a long option without an argument -/
  | unexpected (tok : String)
  /-- a prefix of several long names that mean different options -/
  | ambiguous (tok : String) (candidates : List String)
  deriving DecidableEq, Repr, Inhabited

/-- The usage error of the args dialect a getopt error reports as. -/
def Error.toArgError : Error → ArgError
  | .unknown t => .unknownOption t
  | .missing t => .missingValue t
  | .unexpected t => .unexpectedValue t
  | .ambiguous t _ => .unknownOption t

/-- `n` is a prefix of the name `m` (as character lists). -/
def prefixOf (n m : String) : Bool := n.toList.isPrefixOf m.toList

/-- **Resolve a long name**: an exact name, else the unique option of which `n` is a prefix
(entries with the same target count once). The error lists the candidates: none (unknown) or
several (ambiguous). -/
def resolveLong (ls : List Long) (n : String) : Except (List Long) Long :=
  match ls.find? (·.name == n) with
  | some l => .ok l
  | none =>
    match ls.filter (fun l => prefixOf n l.name) with
    | [] => .error []
    | l :: rest => if rest.all (·.target == l.target) then .ok l else .error (l :: rest)

/-- Read `--n` or `--n=v` (`tok` the whole token, `next` the token after it). -/
def readLong (t : Table) (tok n : String) (v next : Option String) : Except Error Read :=
  match resolveLong t.longs n with
  | .error [] => .error (.unknown tok)
  | .error cs => .error (.ambiguous tok (cs.map (·.name)))
  | .ok l =>
    match l.arg, v with
    | .none, none => .ok ([(l.key, .on)], false)
    | .none, some _ => .error (.unexpected tok)
    | .optional, none => .ok ([(l.key, .on)], false)
    | _, some x => .ok ([(l.key, .val x)], false)
    | .required, none =>
      match next with
      | some x => .ok ([(l.key, .val x)], true)
      | none => .error (.missing tok)

/-- The optstring character `ch`. -/
def findChar (t : Table) (ch : Char) : Option Short := t.shorts.find? (·.ch == ch)

/-- `-W name[=value]` (with `W;`): the argument `a` read as a long option. `consumed`: the name
came from the next token; `next`: the token that may hold a required argument (`-Wname value`;
for `-W name value` the model gives none). -/
def readW (t : Table) (tok : String) (a : List Char) (consumed : Bool) (next : Option String) :
    Except Error Read :=
  match splitEq a with
  | (n, v) => (readLong t tok (String.ofList n) (v.map String.ofList) next).map
      fun p => (p.1, consumed || p.2)

/-- Read a cluster of option characters (the characters after `-`). -/
def readCluster (t : Table) (tok : String) (next : Option String) :
    List Char → Except Error Read
  | [] => .ok ([], false)
  | ch :: r =>
    if t.wLong && ch == 'W' then
      match r, next with
      | [], some x => readW t tok x.toList true none
      | [], none => .error (.missing tok)
      | _, _ => readW t tok r false next
    else
    match findChar t ch with
    | none => .error (.unknown tok)
    | some s =>
      match s.arg, r with
      | .none, _ => (readCluster t tok next r).map fun p => ((s.key, .on) :: p.1, p.2)
      | .optional, [] => .ok ([(s.key, .on)], false)
      | .required, [] =>
        match next with
        | some x => .ok ([(s.key, .val x)], true)
        | none => .error (.missing tok)
      | _, _ => .ok ([(s.key, .val (String.ofList r))], false)

/-- The characters after `-` are one optstring character. -/
def oneShort (t : Table) : List Char → Bool
  | [ch] => (findChar t ch).isSome
  | _ => false

/-- `getopt_long_only` on a single-dash token (`cs`: the characters after `-`). A token that is
one optstring character is that short option (so `-f` stays reachable); otherwise the token is
first read as a long name (`-name`, `-name=value`, unambiguous prefixes included), and when no
long name has it as a prefix, as a cluster (glibc falls back to the optstring, or reports an
unknown option). -/
def readLongOnly (t : Table) (tok : String) (next : Option String) (cs : List Char) :
    Except Error Read :=
  if oneShort t cs then readCluster t tok next cs else
  match resolveLong t.longs (String.ofList (splitEq cs).1) with
  | .error [] => readCluster t tok next cs
  | _ => readLong t tok (String.ofList (splitEq cs).1) ((splitEq cs).2.map String.ofList) next

/-- **Read an option token** `tok`, followed by `next`: occurrences, and whether `next` was
taken as an argument. -/
def readTok (t : Table) (tok : String) (next : Option String) : Except Error Read :=
  match classify tok with
  | .long n v => readLong t tok n v next
  | .short n => if t.longOnly then readLongOnly t tok next n.toList else
      readCluster t tok next n.toList
  | _ => .error (.unknown tok)

/-! ## The reading -/

/-- The argument orderings of glibc's getopt (the third, `-` in the optstring, is
`Silmaril.Cli.Getopt.parseInOrder`). -/
inductive Order where
  /-- options may follow operands (GNU's default) -/
  | permute
  /-- the first operand ends the options (POSIX; `+`; `POSIXLY_CORRECT`) -/
  | requireOrder
  deriving DecidableEq, Repr, Inhabited

/-- What getopt read from an argument vector. -/
structure Parsed where
  /-- the option occurrences, in order (by key) -/
  opts : List (String × Given) := []
  /-- the operands, in order -/
  operands : List String := []
  /-- the option tokens and the arguments they took from the next token, in order -/
  front : List String := []
  /-- `--` ended the options -/
  dashdash : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- **The getopt reading** of an argument vector (without the program name). -/
def parse (t : Table) (ord : Order) : List String → Except Error Parsed
  | [] => .ok {}
  | tok :: rest =>
    match classify tok with
    | .dashdash => .ok { operands := rest, dashdash := true }
    | .word _ =>
      match ord with
      | .requireOrder => .ok { operands := tok :: rest }
      | .permute => (parse t ord rest).map fun p => { p with operands := tok :: p.operands }
    | _ =>
      match readTok t tok rest.head? with
      | .error e => .error e
      | .ok (ps, false) =>
        (parse t ord rest).map fun p => { p with opts := ps ++ p.opts, front := tok :: p.front }
      | .ok (ps, true) =>
        match rest with
        | [] => .error (.missing tok)
        | x :: rest' =>
          (parse t ord rest').map fun p =>
            { p with opts := ps ++ p.opts, front := tok :: x :: p.front }

/-- **The permuted argument vector**: the option tokens first, then `--` if one ended the
options, then the operands (what glibc leaves in `argv` when it is done). -/
def Parsed.permuted (p : Parsed) : List String :=
  p.front ++ (if p.dashdash then "--" :: p.operands else p.operands)

/-! ## Tables from args grammars -/

/-- The argument of an args option, as getopt sees it. -/
def hasArgOf (o : Opt) : HasArg :=
  match o.arg with
  | none => .none
  | some _ => if o.valueOptional then .optional else .required

/-- The optstring character of a one-letter single-dash name `s` of `o`. -/
def shortOf (o : Opt) (s : String) : Option Short :=
  match s.toList with
  | [ch] => some { ch, arg := hasArgOf o, key := o.id }
  | _ => none

/-- The optstring characters of an option: its one-letter single-dash names (none for an
`exact` option). -/
def shortsOf (o : Opt) : List Short := if o.exact then [] else o.short.filterMap (shortOf o)

/-- The longopts entries of an option: its long names. -/
def longsOf (o : Opt) : List Long :=
  o.long.map fun n => { name := n, arg := hasArgOf o, key := o.id }

/-- **The getopt table of an args command** (keys: option `id`s). -/
def Table.ofCommand (c : Command) (plus wLong : Bool := false) : Table where
  shorts := c.opts.flatMap shortsOf
  longs := c.opts.flatMap longsOf
  plus := plus
  wLong := wLong

/-- **A grammar getopt can express**: no subcommands, and every option has one-letter
single-dash names that may cluster and no `--no-NAME` negation (decidable). -/
def Fits (c : Command) : Prop :=
  c.subs = [] ∧ ∀ o ∈ c.opts, o.exact = false ∧ o.negatable = false ∧
    ∀ s ∈ o.short, s.toList.length = 1

instance (c : Command) : Decidable (Fits c) := by unfold Fits; infer_instance

/-! ## Tools -/

/-- **A tool in the getopt dialect**: an args grammar (without subcommands) read by getopt. -/
structure Tool where
  grammar : Command
  /-- GNU getopt (permutes unless told not to); `false`: POSIX getopt, which never permutes -/
  gnu : Bool := true
  /-- the optstring starts with `+` -/
  plus : Bool := false
  /-- the optstring contains `W;` -/
  wLong : Bool := false
  deriving Inhabited

/-- The getopt table of a tool. -/
def Tool.table (t : Tool) : Table := Table.ofCommand t.grammar t.plus t.wLong

/-- **The ordering in an environment**: POSIX getopt, a leading `+` and a set `POSIXLY_CORRECT`
(any value) stop at the first operand. -/
def Tool.order (t : Tool) (env : String → Option String) : Order :=
  if !t.gnu || t.plus || (env "POSIXLY_CORRECT").isSome then .requireOrder else .permute

/-- The getopt reading of a tool, in an environment. -/
def Tool.parse (t : Tool) (env : String → Option String) (argv : List String) :
    Except Error Parsed :=
  Getopt.parse t.table (t.order env) argv

/-- What getopt read, as an args invocation: one frame. -/
def Tool.invocation (t : Tool) (p : Parsed) : Invocation :=
  [{ cmd := t.grammar.name, opts := p.opts, args := p.operands }]

/-- What `interpret` does after parsing: help, version, then the checks (`resolveOutcome`). -/
def afterScan (c : Command) (env : String → Option String) (fs : Invocation) : Outcome :=
  match helpPath fs [] with
  | some p => .help p
  | none =>
    match c.version, fs with
    | some v, f :: _ =>
      if f.opts.any (·.1 == "version") then .version v else resolveOutcome c env fs
    | _, _ => resolveOutcome c env fs

/-- **The reading** of an argument vector (without the program name) in the environment
`env`: getopt (`Tool.parse`; the environment decides the ordering), then the checks of the
args front end on the invocation it read (`afterScan`). `env` is the whole environment: it is
read for `POSIXLY_CORRECT` and for the grammar's environment variables. -/
def Tool.read (t : Tool) (env : String → Option String) (argv : List String) : Outcome :=
  match t.parse env argv with
  | .error e => .error [t.grammar.name] e.toArgError
  | .ok p => afterScan t.grammar env (t.invocation p)

/-! ## The pre-pass: where the getopt and args readings may differ -/

/-- Why the two readings may differ on a token. -/
inductive Diverge where
  /-- a long name given as a prefix (getopt resolves it, args does not) -/
  | abbrev (tok full : String)
  /-- `-W name` -/
  | wLong (tok : String)
  /-- an attached argument starting with `=` (`-o=x`: getopt reads `=x`, args `x`) -/
  | attachedEq (tok : String)
  /-- in POSIX order, a token after the first operand that the args dialect reads as an option
  or as `--` -/
  | afterOperand (tok : String)
  deriving DecidableEq, Repr, Inhabited

/-- Where a cluster may differ. -/
def clusterDiverge (t : Table) (tok : String) : List Char → Option Diverge
  | [] => none
  | ch :: r =>
    if t.wLong && ch == 'W' then some (.wLong tok) else
    match findChar t ch with
    | none => none
    | some s =>
      match s.arg with
      | .none => clusterDiverge t tok r
      | _ => if r.head? == some '=' then some (.attachedEq tok) else none

/-- Where an option token may differ. -/
def tokDiverge (t : Table) (tok : String) : Option Diverge :=
  match classify tok with
  | .long n _ =>
    match resolveLong t.longs n with
    | .ok l => if l.name == n then none else some (.abbrev tok l.name)
    | .error _ => none
  | .short n => clusterDiverge t tok n.toList
  | _ => none

/-- **The pre-pass**: the first place where the getopt reading (with table `t`, ordering
`ord`) and the args reading may differ (`none`: they agree). -/
def pre (t : Table) (ord : Order) : List String → Option Diverge
  | [] => none
  | tok :: rest =>
    match classify tok with
    | .dashdash => none
    | .word _ =>
      match ord with
      | .requireOrder => (rest.find? (!isWord ·)).map .afterOperand
      | .permute => pre t ord rest
    | _ =>
      match tokDiverge t tok with
      | some d => some d
      | none =>
        match readTok t tok rest.head? with
        | .error _ => none
        | .ok (_, false) => pre t ord rest
        | .ok (_, true) =>
          match rest with
          | [] => none
          | _ :: rest' => pre t ord rest'

/-- The pre-pass of a tool in an environment. -/
def Tool.pre (t : Tool) (env : String → Option String) (argv : List String) : Option Diverge :=
  Getopt.pre t.table (t.order env) argv

/-- Two outcomes of the args front end agree: equal, or usage errors on both sides (the
messages may differ). -/
def Agrees : Outcome → Outcome → Prop
  | .error _ _, .error _ _ => True
  | a, b => a = b

end Silmaril.Cli.Getopt
