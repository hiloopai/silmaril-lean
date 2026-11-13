module

public import Silmaril.Cli.Clap.Help.Defs
public import Silmaril.Cli.Clap.Suggest.Defs
public import Silmaril.Cli.Clap.Main.Defs

/-!
# clap's exact texts for the outcomes that do not run

What a clap 4.6 program prints when the reading `Tool.read` does not run it, byte for byte,
derived from the grammar and its presentation data (the help layout is
`Silmaril.Cli.Clap.Help`):

* **help** (`-h`, `--help`, `help NAME…`): the short help for `-h`, the long help for `--help`
  and the `help` subcommand (`wantsLong`: the token at which the pre-pass stopped with help);
  on stdout, exit 0;
* **a group without a subcommand**: its short help on stderr (exit: the usage exit);
* **a usage error**: `error: MSG`, then clap's tail (`Tail`): either nothing more than
  `For more information, try '--help'.` (a missing value, an invalid value, with clap's
  "a similar value exists" tip for possible values), or tips and a usage line first.

**The usage line of an error** (`usageLine`, clap's `create_usage_with_title`): when no argument
is "used", the usage line of the help; otherwise clap's *smart usage*: the command path, the
required options and the used ones, each once, in that order (clap's `required` graph unrolled
through `requires`, then the used ids), then every positional, `<X>` when required or used,
`[X]` otherwise, then `<COMMAND>` for a group. Which arguments count as used depends on the
error, as in clap's parser and validator (`clap_builder` 4.6, `parser/{parser,validator}.rs`):

* an unknown long option: the arguments given before it, then the suggested one (clap adds it
  to the matches); tip "a similar argument exists" (the most similar long name above clap's
  threshold, `Suggest.didYouMean`) or, with no suggestion and positionals, "to pass … as a
  value, use '-- …'";
* an unknown short option: the help's usage line, with the `--` tip when there are positionals;
* a value given to a flag (`--wat=1`): the arguments given before it that are not required,
  then the flag;
* a missing required argument or a broken `requires`: the arguments given, then the missing
  ones, with the requirements of the given arguments among the required;
* a conflict: the arguments given except the one conflicting with the first;
* a repetition, an extra positional: the help's usage line; an unknown subcommand: its tip
  ("a similar subcommand exists", or "some similar subcommands exist" with all of them, none
  after `help`) and the group's usage line.

Where the error comes from the clap pre-pass, its kind is read off the message (`Early.error`
carries only the text; its forms are fixed in `Silmaril.Cli.Clap.Defs`), and the arguments given
before the failing token are those the args parser reads from the tokens before it.

`Tool.exact` is the presentation function a tool installs as `Tool.present` (so that
`Tool.text`, `Tool.main` and `Tool.spec` of `Silmaril.Cli.Clap.Main` use these texts);
`tools/cli-spec/tests/wasm-tools-surface.sh` compares them with the pinned `wasm-tools` on the
derived corpus.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Clap.Exact

open Silmaril.Cli Silmaril.Cli.Clap

/-- The text between the first two quotes of a message (`'--x'`). -/
def quoted (msg : String) : String := (msg.splitOn "'").getD 1 ""

/-- The first occurrence of every element, in order. -/
def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- `s` without its final newlines. -/
def chompS (s : String) : String := String.ofList (s.toList.reverse.dropWhile (· == '\n')).reverse

/-! ## Help -/

/-- The token at which the pre-pass stops with help: the first `k` such that the pre-pass
already stops with help on the first `k + 1` tokens. -/
def helpToken (t : Tool) (argv : List String) : Option String :=
  ((List.range argv.length).find? fun k =>
    match pre t t.grammar [t.grammar.name] (argv.take (k + 1)) with
    | some (.help _) => true
    | _ => false).bind fun k => argv[k]?

/-- The help asked for is the long one: `--help`, or the `help` subcommand. -/
def wantsLong (t : Tool) (argv : List String) : Bool :=
  match helpToken t argv with
  | some tok => tok == "--help" || tok == "help"
  | none => false

/-! ## The usage line of an error -/

/-- The targets of the `requires` rules of `id` in `c`. -/
def requiresOf (c : Command) (id : String) : List String :=
  c.rules.filterMap fun
    | .requires a b => if a == id then some b else none
    | _ => none

/-- clap's `required` graph of `c` unrolled through `requires`: every required option preceded
by what it requires; with `seen` (the arguments given), also their requirements arguments. -/
def reqIds (c : Command) (seen : List String) : List String :=
  (c.opts.filter fun o => o.required).flatMap (fun o => requiresOf c o.id ++ [o.id]) ++
    seen.flatMap (requiresOf c)

/-- A positional in a usage line: `<X>` when required or used, else `[X]`. -/
def posUsage (used : List String) (p : Pos) : String :=
  let s := surfacePos p
  Surface.Pos.spec { s with required := s.required || used.contains p.id }

/-- **clap's smart usage**: the path, the required and the used options (each once, by their
clap names), every positional, `<COMMAND>` for a group. -/
def smartUsage (c : Command) (path reqs used : List String) : String :=
  let ids := reqs ++ used
  let opts := dedup (ids.filterMap fun id => (findId c.opts id).map display)
  "Usage: " ++ " ".intercalate (path ++ opts ++ c.pos.map (posUsage ids) ++
    (if c.subs.isEmpty then [] else ["<COMMAND>"]))

/-- The usage line of the help of `c` at `path` (program name first). -/
def helpUsage (t : Tool) (c : Command) (path : List String) : String :=
  (surfaceCmd t path.tail c).usage path

/-- clap's `create_usage_with_title`: the help's usage line when nothing is used, else the smart
usage. -/
def usageLine (t : Tool) (c : Command) (path reqs used : List String) : String :=
  if used.isEmpty then helpUsage t c path else smartUsage c path reqs used

/-- The ids an invocation's last frame uses: its options (first occurrences, in order), then the
positionals that received a word. -/
def frameUsed (c : Command) (f : Frame) : List String :=
  dedup (f.opts.map (·.1)) ++
    ((c.pos.zipIdx.filter fun (_, i) => i < f.args.length).map (·.1.id))

/-! ## The tail of a usage error -/

/-- What clap prints between `error: MSG` and `For more information, try '--help'.`: tips (one
paragraph each) and, unless `none`, a usage line. -/
structure Tail where
  /-- the message instead of the reading's (clap names the refused part of a delimited value) -/
  msg : Option String := none
  /-- text right after the message (a value parser's reason, clap's possible values) -/
  more : String := ""
  tips : List String := []
  usage : Option String := none
  /-- ends with `For more information, try '--help'.` (not in clap's implicit `help`
  subcommand, which has no help flag) -/
  moreInfo : Bool := true
  deriving Inhabited, DecidableEq, Repr

/-- clap's tip for an unknown subcommand (`similar`: clap's `did_you_mean`, most similar last). -/
def subTip (similar : List String) : List String :=
  match similar with
  | [] => []
  | [s] => ["a similar subcommand exists: '" ++ s ++ "'"]
  | ss => ["some similar subcommands exist: " ++ ", ".intercalate (ss.map fun s => "'" ++ s ++ "'")]

/-- The subcommand words of a group, as clap's suggestions list them (with aliases, `help`
last when the group has the implicit `help` subcommand). -/
def subWords (t : Tool) (c : Command) : List String :=
  c.subs.flatMap Command.names ++ (if t.helpSub then ["help"] else [])

/-- The long names of a command, in definition order (clap's keymap). -/
def longNames (c : Command) : List String := c.opts.flatMap Opt.long

/-- The first `k` with the pre-pass stopping on the first `k + 1` tokens with the message
`msg`: the failing token. -/
def failingIndex (t : Tool) (argv : List String) (msg : String) : Option Nat :=
  (List.range argv.length).find? fun k =>
    pre t t.grammar [t.grammar.name] (argv.take (k + 1)) == some (.error msg)

/-- The ids the tokens before the failing one use at the command `c` (the last frame of what
the args parser reads from them). -/
def usedBefore (t : Tool) (c : Command) (argv : List String) (k : Nat) : List String :=
  -- the token before the failing one may be an option still waiting for its value: it is
  -- not used yet (clap records an argument when its value comes)
  let read (n : Nat) : Option (List String) :=
    match scan t.grammar (argv.take n) with
    | .ok fs => some ((fs.getLast?.map (frameUsed c)).getD [])
    | .error _ => none
  ((read k).orElse fun _ => read (k - 1)).getD []

/-- The possible values the tool lists for a delimited option (`Tool.choices`). -/
def choicesOf (t : Tool) (path : List String) (id : String) : List String :=
  ((t.choices.find? fun (q, i, _) => q == path && i == id).map (·.2.2)).getD []

/-- The tail of an unknown long option `--name` at command `c`, used ids `used` before it. -/
def unknownLongTail (t : Tool) (c : Command) (path : List String) (tok : String)
    (used : List String) : Tail :=
  let name := ((String.ofList (tok.toList.drop 2)).splitOn "=").headD ""
  let tok := "--" ++ name
  match Suggest.didYouMean name (longNames c) with
  | some s =>
    let used := used ++ (match findLong c.opts s with
      | some o => if used.contains o.id then [] else [o.id]
      | none => [])
    { tips := ["a similar argument exists: '--" ++ s ++ "'"],
      usage := some (usageLine t c path (reqIds c []) used) }
  | none =>
    { tips := if c.pos.isEmpty then [] else
        ["to pass '" ++ tok ++ "' as a value, use '-- " ++ tok ++ "'"],
      usage := some (usageLine t c path (reqIds c []) used) }

/-- The tail of an error of the pre-pass (message `msg`). -/
def preTail (t : Tool) (argv : List String) (msg : String) : Tail :=
  let path := wordsPath t.grammar [t.grammar.name] argv
  let c := (t.grammar.walk path.tail).getD t.grammar
  let k := (failingIndex t argv msg).getD 0
  let tok := argv.getD k ""
  let used := usedBefore t c argv k
  if msg.startsWith "a value is required" then
    match c.opts.find? (fun o => valueRequired o == msg) with
    | some o =>
      match o.arg, choicesOf t path.tail o.id with
      | some (.enum cs), _ | _, cs@(_ :: _) =>
        { more := "\n  [possible values: " ++ ", ".intercalate cs ++ "]" }
      | _, _ => {}
    | none => {}
  else if msg.startsWith "unexpected value" then
    let id := match classify tok with
      | .long n _ => ((findLong c.opts n).map (·.id)).getD n
      | _ => tok
    let reqs := reqIds c []
    { usage := some (usageLine t c path reqs ((used.filter (!reqs.contains ·)) ++ [id])) }
  else if msg.startsWith "unrecognized subcommand" then
    match (argv.take k).idxOf? "help" with
    | some i =>
      -- `help NAME…`: the usage of the command the words reach (clap's implicit `help`
      -- subcommand has no help flag, so no "For more information" line)
      let reached := match helpWalk c [] ((argv.drop (i + 1)).take (k - i - 1)) with
        | .ok q => q
        | .error _ => []
      let rpath := path ++ reached
      match t.helpCmd? rpath.tail with
      | some r =>
        { usage := some (helpUsage t r rpath), moreInfo := reached.getLast? != some "help" }
      | none => { usage := some (helpUsage t c path) }
    | none =>
      { tips := subTip (Suggest.didYouMeanAll tok (subWords t c)),
        usage := some (helpUsage t c path) }
  else if tok.startsWith "--" then unknownLongTail t c path tok used
  else if tok.startsWith "-" then
    let ch := quoted msg
    { tips := if c.pos.isEmpty then [] else
        ["to pass '" ++ ch ++ "' as a value, use '-- " ++ ch ++ "'"],
      usage := some (helpUsage t c path) }
  else { usage := some (helpUsage t c path) }

/-- The tail of an error of the args parser at the subcommand path `p` (below the root). -/
def scanTail (t : Tool) (argv : List String) (p : List String) (e : ArgError) : Tail :=
  let path := t.grammar.name :: p
  let c := (t.grammar.walk p).getD t.grammar
  match e with
  | .missingValue _ => {}
  | .unknownCommand w =>
    { tips := subTip (Suggest.didYouMeanAll w (subWords t c)), usage := some (helpUsage t c path) }
  | .unknownOption tok =>
    if tok.startsWith "--" then
      let k := (argv.findIdx? (· == tok)).getD argv.length
      unknownLongTail t c path tok (usedBefore t c argv k)
    else { usage := some (helpUsage t c path) }
  | _ => { usage := some (helpUsage t c path) }

/-- The reason clap's own value parsers give (`value_parser!(uN)`): Rust's `ParseIntError`, and
for widths below 64 bits (clap's `RangedI64ValueParser`, which parses an `i64` first, so a
leading `-` is a sign there) the range of a value that fits an `i64`. A lone `+` or `-` is an
invalid digit, as in Rust's `from_str`. -/
def checkReason : ValueCheck → String → Option String
  | .uint bits, v =>
    let range (s : String) := some (s ++ " is not in 0..=" ++ toString (2 ^ bits - 1))
    let (neg, ds) := match v.toList with
      | '+' :: r => (false, r)
      | '-' :: r => (bits < 64, if bits < 64 then r else '-' :: r)
      | r => (false, r)
    if v.isEmpty then some "cannot parse integer from empty string"
    else if ds.isEmpty || !ds.all Char.isDigit then some "invalid digit found in string"
    else
      let n := (ArgType.digitsAux 0 ds).getD 0
      if neg then
        if n ≤ 2 ^ 63 then range ("-" ++ toString n)
        else some "number too small to fit in target type"
      else if bits < 64 && n < 2 ^ 63 then range (toString n)
      else some "number too large to fit in target type"
  | _, _ => none

/-- The reason for refusing the value `v` of `id` at the subcommand path `p`: clap's own for
the grammar's check, else the tool's (`reason`). -/
def refusal (t : Tool) (reason : String → String → Option String) (p : List String)
    (id v : String) : String :=
  let own := ((t.grammar.scopeAt p).lookup id).bind fun ck => checkReason ck v
  (((own.orElse fun _ => reason id v)).map (": " ++ ·)).getD ""

/-- How clap lists a missing argument: an option by its clap name, a positional `<X>`. -/
def missingName (c : Command) (id : String) : String :=
  match findId c.opts id with
  | some o => display o
  | none =>
    match c.pos.find? (·.id == id) with
    | some p => posUsage [id] p
    | none => id

/-- The tail of a judgement on the invocation `fs`. -/
def judgeTail (t : Tool) (reason : String → String → Option String) (fs : Invocation) :
    Judgement → Tail
  | .badValue _ o x =>
    match o.arg with
    | some (.enum cs) =>
      match Suggest.didYouMean x cs with
      | some s => { tips := ["a similar value exists: '" ++ s ++ "'"] }
      | none => {}
    | _ =>
      let p := fs.drop 1 |>.map (·.cmd)
      match ((t.grammar.scopeAt p).lookup o.id), choicesOf t p o.id with
      | some (.listOf sep _ _), cs@(_ :: _) =>
        -- clap checks every part of a delimited value against the possible values
        let part := ((x.splitOn (String.singleton sep)).find? (!cs.contains ·)).getD x
        { msg := some ("invalid value '" ++ part ++ "' for '" ++ display o ++ "'"),
          more := "\n  [possible values: " ++ ", ".intercalate cs ++ "]",
          tips := match Suggest.didYouMean part cs with
            | some s => ["a similar value exists: '" ++ s ++ "'"]
            | none => [] }
      | _, _ => { more := refusal t reason p o.id x }
  | .rejected p id v => { more := refusal t reason p id v }
  | .unresolved (p, e) =>
    let c := (t.grammar.walk p).getD t.grammar
    let seen := (fs.getLast?.map (frameUsed c)).getD []
    match e with
    | .missingOption id | .missingArgument id =>
      -- clap lists every missing required argument: options, then positionals
      let reqPos := (c.pos.filter fun q => q.arity == .one || q.arity == .atLeastOne).map (·.id)
      let missing := dedup ((reqIds c seen ++ reqPos).filter fun x => !seen.contains x)
      let others := missing.filter (· != id)
      { more := String.join (others.map fun x => "\n  " ++ missingName c x),
        usage := some (usageLine t c (t.grammar.name :: p) (reqIds c seen) (seen ++ missing)) }
    | .badValue _ v (.enum cs) =>
      { tips := match Suggest.didYouMean v cs with
          | some s => ["a similar value exists: '" ++ s ++ "'"]
          | none => [] }
    | .badValue id v _ => { more := refusal t reason p id v }
    | _ => { usage := some (helpUsage t c (t.grammar.name :: p)) }
  | .broken p r =>
    let c := (t.grammar.walk p).getD t.grammar
    let seen := (fs.getLast?.map (frameUsed c)).getD []
    let path := t.grammar.name :: p
    match r with
    | .requires _ b =>
      { usage := some (usageLine t c path (reqIds c seen) (seen ++ [b])) }
    | .conflicts _ b =>
      let kept := seen.filter (· != b)
      let reqs := (kept.flatMap (requiresOf c)).filter fun x => !kept.contains x && x != b
      { usage := some (usageLine t c path (reqIds c seen) (reqs ++ kept)) }
  | _ => {}

/-- **The tail of a usage error** on `argv`, as the reading reaches it. -/
def tail (t : Tool) (reason : String → String → Option String) (env : String → Option String)
    (argv : List String) (msg : String) : Tail :=
  match pre t t.grammar [t.grammar.name] argv with
  | some _ => preTail t argv msg
  | none =>
    match scan t.grammar argv with
    | .error (p, e) => scanTail t argv p e
    | .ok fs => judgeTail t reason fs (judge t.grammar env fs)

/-- `error: MSG`, the tail, `For more information, try '--help'.` -/
def errorText (msg : String) (tl : Tail) : String := chompS <|
  "error: " ++ tl.msg.getD msg ++ tl.more ++ "\n" ++
    String.join (tl.tips.map fun tip => "\n  tip: " ++ tip ++ "\n") ++
    (match tl.usage with
     | some u => "\n" ++ u ++ "\n"
     | none => "") ++
    (if tl.moreInfo then "\nFor more information, try '--help'." else "")

end Silmaril.Cli.Clap.Exact

namespace Silmaril.Cli.Clap

open Silmaril.Cli Silmaril.Cli.Clap.Exact

/-- **clap's exact texts** of the outcomes of `t` that do not run (the environment is the empty
one: no tool here reads one in the front end; a tool that does passes it to `tail`). The
version line is the grammar's (`name version`). `width`: clap's terminal width (`Help.widthOf`
of `COLUMNS`). `reason id v`: the reason a value parser gives
for refusing the value `v` of the argument `id` (clap prints it after the message), if any. -/
def Tool.exact (t : Tool) (reason : String → String → Option String := fun _ _ => none)
    (width : Nat := Help.width) (argv : List String) : Outcome → String
  | .run _ _ | .undecided _ _ _ => ""
  | .help p => chompS (t.clapHelp p.tail (wantsLong t argv) width)
  | .version =>
    -- a subcommand's own `--version` names it `PROG-SUB` (clap's display name)
    let path := wordsPath t.grammar [t.grammar.name] argv
    let v := ((t.grammar.walk path.tail).bind (·.version)).getD (t.grammar.version.getD "")
    "-".intercalate path ++ " " ++ v
  | .needCommand p => chompS (t.clapHelp p.tail false width)
  | .error msg => Exact.errorText msg (Exact.tail t reason (fun _ => none) argv msg)

end Silmaril.Cli.Clap
