module

public import Init.Data.String.Basic
public import Init.Data.List.Basic

/-!
# The option values of `wasm-tools smith`, `mutate`, `shrink` and `wit-smith`

The command line of these subcommands is read by the specification of upstream's command line
(`Silmaril.Cli.Spec.WasmTools.tool`: the clap pre-pass, the args parser, the value checks, the texts
of help and usage errors). The bodies read the values by option, typed: `Spec` lists the options
a body reads with their kind (`Kind`: a flag, a counted flag (`-v…`), or a value read as upstream
reads it: a string, an unsigned integer as Rust's `u64::from_str`, an integer in a range as
clap's `RangedI64ValueParser`, a Boolean `true`/`false`, a colour), and `Parsed.ofOccs` reads the
specification's occurrences into `Parsed`. `parseVal` is also the reader of
`smith --config` files (`SmithConfig`).

(This module was the clap-subset grammar of these subcommands; that reading is now the
specification's, so the scanner and its theorems about help are gone.)

`Thms` proves the properties the CLI layer relies on.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Args

/-- How an option's value is parsed. -/
inductive Kind where
  /-- No value, at most once. -/
  | flag
  /-- No value, repeatable (`-v`, `-vv`, …). -/
  | count
  /-- Any string. -/
  | str
  /-- Rust `u64::from_str`. -/
  | u64
  /-- clap's ranged integer parser: an `i64`, then `0..=hi`. -/
  | ranged (hi : Nat)
  /-- `true` or `false`. -/
  | bool
  /-- `--color`: `auto`, `never`, `always`, `always-ansi`. -/
  | color
  deriving DecidableEq, Repr

/-- One option. `valName` is the value name in messages (`<MAX_FUNCS>`). -/
structure Opt where
  long : String
  short : Option Char := none
  kind : Kind := .flag
  valName : String := ""
  deriving Repr

/-- A subcommand's grammar. -/
structure Spec where
  /-- `wasm-tools smith`. -/
  path : String
  opts : List Opt
  /-- Positional slots: display name (`[INPUT]`, `<PREDICATE>`) and whether required. -/
  positionals : List (String × Bool)
  /-- The usage line after `Usage: `. -/
  usage : String

/-- A parsed value. -/
inductive Val where
  | flag
  | count (n : Nat)
  | str (s : String)
  | num (n : Nat)
  | bool (b : Bool)
  deriving DecidableEq, Repr

/-- The result of a successful parse: option values by long name, and positionals. -/
structure Parsed where
  vals : List (String × Val) := []
  pos : List String := []
  deriving Repr

namespace Parsed

def get? (p : Parsed) (k : String) : Option Val := (p.vals.find? (·.1 == k)).map (·.2)

def flag (p : Parsed) (k : String) : Bool := (p.get? k).isSome

def str? (p : Parsed) (k : String) : Option String :=
  match p.get? k with
  | some (.str s) => some s
  | _ => none

def num? (p : Parsed) (k : String) : Option Nat :=
  match p.get? k with
  | some (.num n) => some n
  | _ => none

def bool? (p : Parsed) (k : String) : Option Bool :=
  match p.get? k with
  | some (.bool b) => some b
  | _ => none

def count (p : Parsed) (k : String) : Nat :=
  match p.get? k with
  | some (.count n) => n
  | _ => 0

end Parsed

/-! ## Values -/

/-- Rust `u64::from_str` (`from_str_radix(s, 10)`): an optional `+`, then digits; the first
failure in reading order wins. -/
def parseU64 (s : String) : Except String Nat :=
  let cs := s.toList
  if cs.isEmpty then .error "cannot parse integer from empty string" else
  let ds := if cs.head? == some '+' then cs.tail else cs
  if ds.isEmpty then .error "invalid digit found in string" else
  ds.foldlM (m := Except String) (init := 0) fun acc c =>
    if c.isDigit then
      let v := acc * 10 + (c.toNat - '0'.toNat)
      if v ≥ 2 ^ 64 then .error "number too large to fit in target type" else .ok v
    else .error "invalid digit found in string"

/-- Rust `i64::from_str`: an optional sign, then digits. -/
def parseI64 (s : String) : Except String Int :=
  let cs := s.toList
  if cs.isEmpty then .error "cannot parse integer from empty string" else
  let (neg, ds) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if ds.isEmpty then .error "invalid digit found in string" else
  (ds.foldlM (m := Except String) (init := (0 : Nat)) fun acc c =>
    if c.isDigit then
      let v := acc * 10 + (c.toNat - '0'.toNat)
      if !neg && v ≥ 2 ^ 63 then .error "number too large to fit in target type"
      else if neg && v > 2 ^ 63 then .error "number too small to fit in target type"
      else .ok v
    else .error "invalid digit found in string").map fun n => if neg then -(n : Int) else n

/-- `--long <META>` as clap names an option with a value. -/
def Opt.display (o : Opt) : String :=
  match o.kind with
  | .flag | .count => s!"--{o.long}"
  | _ => s!"--{o.long} <{o.valName}>"

def footer : String := "\nFor more information, try '--help'.\n"

/-- The usage block of an error. -/
def usageBlock (sp : Spec) : String := s!"\nUsage: {sp.usage}\n" ++ footer

/-- Parse a value of an option. -/
def parseVal (o : Opt) (v : String) : Except String Val :=
  match o.kind with
  | .flag | .count => .ok .flag
  | .str => .ok (.str v)
  | .u64 =>
    match parseU64 v with
    | .ok n => .ok (.num n)
    | .error e => .error (s!"error: invalid value '{v}' for '{o.display}': {e}\n" ++ footer)
  | .ranged hi =>
    match parseI64 v with
    | .ok n =>
      if 0 ≤ n && n ≤ hi then .ok (.num n.toNat)
      else .error (s!"error: invalid value '{v}' for '{o.display}': {n} is not in 0..={hi}\n" ++ footer)
    | .error e => .error (s!"error: invalid value '{v}' for '{o.display}': {e}\n" ++ footer)
  | .bool =>
    if v == "true" then .ok (.bool true) else if v == "false" then .ok (.bool false)
    else .error (s!"error: invalid value '{v}' for '{o.display}'\n  [possible values: true, false]\n" ++ footer)
  | .color =>
    if ["always", "always-ansi", "never", "auto"].contains v then .ok (.str v)
    else .error (s!"error: invalid value '{v}' for '{o.display}': unrecognized color choice " ++
      s!"'{v}': valid choices are: always, always-ansi, never, auto\n" ++ footer)

/-- An option given twice. -/
def dup (sp : Spec) (o : Opt) : String :=
  s!"error: the argument '{o.display}' cannot be used multiple times\n" ++ usageBlock sp

/-- Record a value for `o` in `p`, failing on a repetition. -/
def record (sp : Spec) (p : Parsed) (o : Opt) (v : Val) : Except String Parsed :=
  match o.kind, p.get? o.long with
  | .count, some (.count n) =>
    .ok { p with vals := p.vals.map fun kv => if kv.1 == o.long then (o.long, .count (n + 1)) else kv }
  | .count, _ => .ok { p with vals := p.vals ++ [(o.long, .count 1)] }
  | _, some _ => .error (dup sp o)
  | _, none => .ok { p with vals := p.vals ++ [(o.long, v)] }

/-- **The parsed arguments from the specification's reading**
(`Silmaril.Cli.Spec.WasmTools.tool`): the option occurrences (`id`, value; `none` for a flag) and
the positionals, each value read by its option's kind (`parseVal`; the specification has checked
the values already, so a refusal is not expected). Occurrences of options `sp` does not list are
skipped; a repeated option keeps its first value (`get?`), a counted one its count. -/
def Parsed.ofOccs (sp : Spec) (occs : List (String × Option String)) (pos : List String) :
    Except String Parsed :=
  occs.foldlM (init := { pos }) fun p (k, v) =>
    match sp.opts.find? (·.long == k) with
    | none => .ok p
    | some o =>
      match o.kind, p.get? o.long with
      | .count, _ => record sp p o .flag
      | _, some _ => .ok p
      | _, none => (parseVal o (v.getD "")).bind (record sp p o)

/-! ## Common options -/

def outputOpt : Opt := { long := "output", short := some 'o', kind := .str, valName := "OUTPUT" }
def watOpt : Opt := { long := "wat", short := some 't' }
def verboseOpt : Opt := { long := "verbose", short := some 'v', kind := .count }
def colorOpt : Opt := { long := "color", kind := .color, valName := "COLOR" }

end Silmaril.Wasm.Tools.Gen.Cmd.Args
