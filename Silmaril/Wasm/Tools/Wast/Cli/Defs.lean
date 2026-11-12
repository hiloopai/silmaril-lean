module

public import Silmaril.Wasm.Tools.Wast.Syntax.Defs
public import Silmaril.Wasm.Tools.Features.Defs

/-!
# Command lines of `json-from-wast` and `wast`

The argument grammar of the two subcommands, as clap 4 reads them for `wasm-tools` 1.262.0
(`src/bin/wasm-tools/{json_from_wast,wast}.rs`, `src/lib.rs` `GeneralOpts`/`OutputArg`),
as a pure function from the argument list to an options record or a usage error.

Tokens (`tokens`): `--` ends the options; `--name=value`, `--name value` and `--name` (a
flag); `-abc` is a cluster of short flags in which the first short option that takes a value
takes the rest of the cluster or else the next argument; `-` alone and anything not starting
with `-` is positional. An option that takes a value does not take a following argument that
starts with `-` (other than `-` itself), as clap.

Subcommand options (`jsonOpts?`, `wastOpts?`): single-valued options may occur once
(`repeated`), flags too except `-v` (counted), list-valued options (`-a`, `-f`) accumulate
comma-separated values; positionals beyond the declared ones are `unexpected`.
`-h`/`--help` win over the option checks once the command line tokenizes (`Parsed.help`).
The token grammar is also given declaratively (`Spells`, `Cluster`), and `tokens` computes
exactly it (`Silmaril.Wasm.Tools.Wast.Cli.tokens_ok_iff`); the records read from the tokens are
characterized in `Silmaril.Wasm.Tools.Wast.Cli.Thms` (`jsonRecord_ok`, `wastRecord_ok`). The
whole is also tested against the pinned binary's recorded outcomes (the `wast-args` golden suite
of `tools/wasm-tools/test-cli.py`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.Cli

/-- An option of a subcommand. -/
structure OptSpec where
  long : String
  short : Option Char := none
  takesValue : Bool := false
  deriving Repr, DecidableEq

/-- A token of the command line. -/
inductive Tok where
  | opt (long : String) (value : Option String)
  | pos (s : String)
  deriving Repr, DecidableEq

/-- Usage errors (clap's exit status 2). -/
inductive ArgError where
  | unknown (arg : String)
  | missingValue (long : String)
  | unexpectedValue (long : String)
  | repeated (long : String)
  | unexpected (arg : String)
  | missingRequired (name : String)
  | badValue (long value : String)
  /-- A `--features` value the feature parser rejects (`Features.parseFeatures`). -/
  | badFeatures (value msg : String)
  deriving Repr, DecidableEq

def ArgError.message : ArgError → String
  | .unknown a => s!"unexpected argument '{a}' found"
  | .missingValue l => s!"a value is required for '--{l}' but none was supplied"
  | .unexpectedValue l => s!"unexpected value for '--{l}'"
  | .repeated l => s!"the argument '--{l}' cannot be used multiple times"
  | .unexpected a => s!"unexpected argument '{a}' found"
  | .missingRequired n => s!"the following required arguments were not provided:\n  {n}"
  | .badValue l v => s!"invalid value '{v}' for '--{l}'"
  | .badFeatures v m => s!"invalid value '{v}' for '--features <FEATURES>': {m}"

/-- Can `s` be an option's value (clap does not take `-x` as a value)? -/
def isValue (s : String) : Bool := s == "-" || !s.startsWith "-"

/-- A value attached to a short option: `-fVALUE`, or `-f=VALUE` (clap drops the `=`). -/
def attached : List Char → List Char
  | '=' :: cs => cs
  | cs => cs

/-- Short cluster `-abc` after the dash, given the next argument: its tokens, and whether
it took the next argument as a value. -/
def shortCluster (specs : List OptSpec) (whole : String) (next : Option String) :
    List Char → Except ArgError (List Tok × Bool)
  | [] => .ok ([], false)
  | c :: cs =>
    match specs.find? (·.short == some c) with
    | none => .error (.unknown whole)
    | some sp =>
      if sp.takesValue then
        if cs.isEmpty then
          match next with
          | some v => if isValue v then .ok ([.opt sp.long (some v)], true)
            else .error (.missingValue sp.long)
          | none => .error (.missingValue sp.long)
        else .ok ([.opt sp.long (some (String.ofList (attached cs)))], false)
      else do
        let (ts, used) ← shortCluster specs whole next cs
        pure (.opt sp.long none :: ts, used)

/-- Split `--name=value`. -/
def splitEq (body : String) : String × Option String :=
  match body.splitOn "=" with
  | n :: v :: vs => (n, some ("=".intercalate (v :: vs)))
  | _ => (body, none)

/-- **Tokenize** a command line against the option table. -/
def tokens (specs : List OptSpec) : List String → Except ArgError (List Tok)
  | [] => .ok []
  | a :: rest =>
    if a == "--" then .ok (rest.map .pos)
    else if a.startsWith "--" then
      let (name, val) := splitEq (a.drop 2).toString
      match specs.find? (·.long == name) with
      | none => .error (.unknown a)
      | some sp =>
        if sp.takesValue then
          match val with
          | some v => (tokens specs rest).map (.opt name (some v) :: ·)
          | none =>
            match rest with
            | v :: rest' =>
              if isValue v then (tokens specs rest').map (.opt name (some v) :: ·)
              else .error (.missingValue name)
            | [] => .error (.missingValue name)
        else match val with
          | some _ => .error (.unexpectedValue name)
          | none => (tokens specs rest).map (.opt name none :: ·)
    else if a.startsWith "-" && a != "-" then
      match shortCluster specs a rest.head? (a.drop 1).toString.toList with
      | .error e => .error e
      | .ok (ts, used) =>
        if used then (tokens specs rest.tail).map (ts ++ ·)
        else (tokens specs rest).map (ts ++ ·)
    else (tokens specs rest).map (.pos a :: ·)
termination_by args => args.length

/-! ## The token grammar, declaratively

`Spells specs args ts`: the command line `args` spells the tokens `ts` (clap's lexical rules
for this option table). `Cluster specs next cs ts used`: the short cluster `cs` (after the
dash), followed by the argument `next`, spells `ts`, and takes `next` as a value when `used`.
`Silmaril.Wasm.Tools.Wast.Cli.tokens_ok_iff`: `tokens` computes exactly this relation. -/

inductive Cluster (specs : List OptSpec) (next : Option String) :
    List Char → List Tok → Bool → Prop where
  | nil : Cluster specs next [] [] false
  /-- A flag, then the rest of the cluster. -/
  | flag {c : Char} {cs : List Char} {sp : OptSpec} {ts : List Tok} {used : Bool} :
      specs.find? (·.short == some c) = some sp → sp.takesValue = false →
      Cluster specs next cs ts used → Cluster specs next (c :: cs) (.opt sp.long none :: ts) used
  /-- An option with a value: the rest of the cluster (`-fVALUE`, `-f=VALUE`). -/
  | attached {c : Char} {cs : List Char} {sp : OptSpec} :
      specs.find? (·.short == some c) = some sp → sp.takesValue = true → cs ≠ [] →
      Cluster specs next (c :: cs) [.opt sp.long (some (String.ofList (attached cs)))] false
  /-- An option with a value: the next argument, which must not look like an option. -/
  | nextArg {c : Char} {sp : OptSpec} {v : String} :
      specs.find? (·.short == some c) = some sp → sp.takesValue = true → next = some v →
      isValue v = true → Cluster specs next [c] [.opt sp.long (some v)] true

inductive Spells (specs : List OptSpec) : List String → List Tok → Prop where
  | nil : Spells specs [] []
  /-- `--`: the rest is positional. -/
  | dashDash {rest : List String} : Spells specs ("--" :: rest) (rest.map .pos)
  /-- `--name=value`. -/
  | longEq {a name v : String} {rest : List String} {sp : OptSpec} {ts : List Tok} :
      a ≠ "--" → a.startsWith "--" = true → splitEq (a.drop 2).toString = (name, some v) →
      specs.find? (·.long == name) = some sp → sp.takesValue = true →
      Spells specs rest ts → Spells specs (a :: rest) (.opt name (some v) :: ts)
  /-- `--name value`. -/
  | longNext {a name v : String} {rest : List String} {sp : OptSpec} {ts : List Tok} :
      a ≠ "--" → a.startsWith "--" = true → splitEq (a.drop 2).toString = (name, none) →
      specs.find? (·.long == name) = some sp → sp.takesValue = true → isValue v = true →
      Spells specs rest ts → Spells specs (a :: v :: rest) (.opt name (some v) :: ts)
  /-- `--flag`. -/
  | longFlag {a name : String} {rest : List String} {sp : OptSpec} {ts : List Tok} :
      a ≠ "--" → a.startsWith "--" = true → splitEq (a.drop 2).toString = (name, none) →
      specs.find? (·.long == name) = some sp → sp.takesValue = false →
      Spells specs rest ts → Spells specs (a :: rest) (.opt name none :: ts)
  /-- A short cluster `-abc`. -/
  | short {a : String} {rest : List String} {ts ts' : List Tok} {used : Bool} :
      a.startsWith "--" = false → a.startsWith "-" = true → a ≠ "-" →
      Cluster specs rest.head? (a.drop 1).toString.toList ts used →
      Spells specs (if used then rest.tail else rest) ts' → Spells specs (a :: rest) (ts ++ ts')
  /-- A positional argument (`-` included). -/
  | pos {a : String} {rest : List String} {ts : List Tok} :
      a ≠ "--" → a.startsWith "--" = false → (a.startsWith "-" = false ∨ a = "-") →
      Spells specs rest ts → Spells specs (a :: rest) (.pos a :: ts)

/-! ## Options records -/

/-- `GeneralOpts`. -/
def generalSpecs : List OptSpec :=
  [⟨"verbose", some 'v', false⟩, ⟨"color", none, true⟩, ⟨"help", some 'h', false⟩]

def jsonSpecs : List OptSpec :=
  generalSpecs ++ [⟨"output", some 'o', true⟩, ⟨"wasm-dir", none, true⟩, ⟨"pretty", none, false⟩,
    ⟨"allow-confusing-unicode", none, true⟩]

def wastSpecs : List OptSpec :=
  generalSpecs ++ [⟨"ignore-error-messages", none, false⟩, ⟨"features", some 'f', true⟩,
    ⟨"allow-confusing-unicode", none, false⟩, ⟨"assert", some 'a', true⟩,
    ⟨"snapshot", none, true⟩]

/-- The outcome of reading a command line. -/
inductive Parsed (α : Type) where
  | run (opts : α)
  /-- `-h` (`long = false`) or `--help`. -/
  | help (long : Bool)
  | error (e : ArgError)
  deriving Repr

/-- `json-from-wast` options. -/
structure JsonOpts where
  wast : String
  output : Option String := none
  wasmDir : Option String := none
  pretty : Bool := false
  allowConfusingUnicode : Option Bool := none
  deriving Repr, DecidableEq

/-- `wast` options. -/
structure WastOpts where
  input : Option String := none
  ignoreErrorMessages : Bool := false
  /-- The `--features` arguments, in order, each already accepted by
  `Features.parseFeatures`. -/
  features : List String := []
  allowConfusingUnicode : Bool := false
  asserts : List String := []
  snapshot : Option String := none
  deriving Repr, DecidableEq

/-- The values of an option in a token list. -/
def values (ts : List Tok) (long : String) : List (Option String) :=
  ts.filterMap fun | .opt l v => if l == long then some v else none | .pos _ => none

def positionals (ts : List Tok) : List String :=
  ts.filterMap fun | .pos s => some s | .opt .. => none

/-- At most one occurrence. -/
def single (ts : List Tok) (long : String) : Except ArgError (Option String) :=
  match values ts long with
  | [] => .ok none
  | [v] => .ok v
  | _ => .error (.repeated long)

def flag (ts : List Tok) (long : String) : Except ArgError Bool :=
  match values ts long with
  | [] => .ok false
  | [_] => .ok true
  | _ => .error (.repeated long)

def colorOk (ts : List Tok) : Except ArgError Unit := do
  match ← single ts "color" with
  | none => pure ()
  | some c => unless ["auto", "never", "always", "always-ansi"].contains c do
      throw (.badValue "color" c)

/-- Was `--help` (long form) given? The tokenizer maps `-h` and `--help` to the same option,
so the raw arguments decide. -/
def helpKind (args : List String) : Option Bool :=
  let pre := args.takeWhile (· != "--")
  if pre.contains "--help" then some true
  else if pre.any (fun a => a.startsWith "-" && !a.startsWith "--" && (a.drop 1).toString.contains 'h') then
    some false
  else none

/-- The value of `--allow-confusing-unicode` of `json-from-wast` (`true` or `false`). -/
def acuValue : Option String → Except ArgError (Option Bool)
  | none => .ok none
  | some "true" => .ok (some true)
  | some "false" => .ok (some false)
  | some v => .error (.badValue "allow-confusing-unicode" v)

/-- The `json-from-wast` record of a token list without `--help`. -/
def jsonRecord (ts : List Tok) : Except ArgError JsonOpts := do
  colorOk ts
  let output ← single ts "output"
  let wasmDir ← single ts "wasm-dir"
  let pretty ← flag ts "pretty"
  let acu ← single ts "allow-confusing-unicode" >>= acuValue
  match positionals ts with
  | [w] => pure { wast := w, output, wasmDir, pretty, allowConfusingUnicode := acu }
  | [] => throw (.missingRequired "<WAST>")
  | _ :: x :: _ => throw (.unexpected x)

/-- Read the arguments of `json-from-wast`. -/
def jsonOpts? (args : List String) : Parsed JsonOpts :=
  match tokens jsonSpecs args with
  | .error e => .error e
  | .ok ts =>
    if (values ts "help").length > 0 then .help (helpKind args == some true) else
    match jsonRecord ts with
    | .ok o => .run o
    | .error e => .error e

/-- Comma-separated values of a repeatable option. -/
def listValues (ts : List Tok) (long : String) : List String :=
  (values ts long).flatMap fun | some v => v.splitOn "," | none => []

def assertValues : List String :=
  ["default", "pretty-whitespace", "snapshot-print", "snapshot-json", "snapshot-folded",
   "test-folded", "no-test-folded", "permissive"]

/-- The feature set of `wast`'s `--features` arguments (`CliFeatures::features`). -/
def WastOpts.featureSet (o : WastOpts) : Features.WFeatures :=
  Features.applyActions (o.features.flatMap fun v => (Features.parseFeatures v).toOption.getD [])

/-- The first `--features` argument the feature parser rejects, with its message. -/
def badFeature? (vs : List String) : Option (String × String) :=
  vs.findSome? fun v => match Features.parseFeatures v with
    | .ok _ => none
    | .error m => some (v, m)

/-- The `wast` record of a token list without `--help`. -/
def wastRecord (ts : List Tok) : Except ArgError WastOpts := do
  colorOk ts
  let iem ← flag ts "ignore-error-messages"
  let acu ← flag ts "allow-confusing-unicode"
  let snapshot ← single ts "snapshot"
  let asserts := listValues ts "assert"
  if let some a := asserts.find? (fun a => !assertValues.contains a) then
    throw (.badValue "assert" a)
  let features := (values ts "features").filterMap id
  if let some (v, m) := badFeature? features then throw (.badFeatures v m)
  match positionals ts with
  | [] => pure { ignoreErrorMessages := iem, features, allowConfusingUnicode := acu,
                 asserts, snapshot }
  | [i] => pure { input := some i, ignoreErrorMessages := iem, features,
                  allowConfusingUnicode := acu, asserts, snapshot }
  | _ :: x :: _ => throw (.unexpected x)

/-- Read the arguments of `wast`. -/
def wastOpts? (args : List String) : Parsed WastOpts :=
  match tokens wastSpecs args with
  | .error e => .error e
  | .ok ts =>
    if (values ts "help").length > 0 then .help (helpKind args == some true) else
    match wastRecord ts with
    | .ok o => .run o
    | .error e => .error e

end Silmaril.Wasm.Tools.Wast.Cli
