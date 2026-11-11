module

public import Init.Data.String

/-!
# The option grammar of `wasm-tools` subcommands (a clap subset)

`wasm-tools` parses its command line with clap 4 (derive API). The subcommands of the validate
track (`validate`, `strip`, `objdump`, `dump`) use only this part of clap, transcribed here as a
pure function from the argument list to the occurrences of each option:

* an option has a long name, maybe a short one, and a kind (`Kind`): a Boolean flag (`SetTrue`:
  at most once), a counter (`Count`, `-v`), a single value (`Option<T>`: at most once), or a
  repeatable value (`Vec<T>`);
* `--name`, `--name=value`, `--name value`; `-x`, clusters `-xyz` of flags and counters, a value
  attached to a short name (`-fVALUE`, `-f=VALUE`) or in the next argument (`-f VALUE`);
* a value in the next argument may not start with `-` unless it is exactly `-` (clap's default
  without `allow_hyphen_values`: `-f -simd` is an error);
* `--` ends the options; `-` alone is a positional argument;
* at most `maxPos` positional arguments;
* `-h`/`--help` request help (clap prints the help and exits 0).

`parse specs maxPos args` returns the occurrences in order (`Parsed`), or the first error
(`CliError`, rendered like clap's first line by `CliError.render`; clap exits with status 2).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.OptGrammar

/-- The kind of an option. -/
inductive Kind where
  | flag
  | count
  | single
  | multi
  deriving Repr, DecidableEq

/-- An option: its identifier, long name, short name and kind; `valueName` is clap's
`<VALUE>` placeholder, used in messages. -/
structure Spec where
  long : String
  short : Option Char := none
  kind : Kind
  valueName : String := ""
  /-- `false` for a short-only option (`#[clap(short)]`): its `long` is only an identifier. -/
  hasLong : Bool := true
  deriving Repr, DecidableEq

/-- Does the option take a value? -/
def Spec.takesValue (s : Spec) : Bool := s.kind == .single || s.kind == .multi

/-- How clap names an option in a message: `--long <VALUE>` or `--long`. -/
def Spec.display (s : Spec) : String :=
  let n := if s.hasLong then s!"--{s.long}" else s!"-{(s.short.getD ' ')}"
  if s.takesValue then s!"{n} <{s.valueName}>" else n

/-- A parsed command line: option occurrences (long name, value) in order, and positional
arguments in order; `help` when `-h`/`--help` was seen (`some true` for `--help`). -/
structure Parsed where
  occ : List (String × Option String) := []
  pos : List String := []
  help : Option Bool := none
  deriving Repr, DecidableEq

/-- A command-line error (clap exits with status 2). -/
inductive CliError where
  | unexpected (arg : String)
  | missingValue (opt : String)
  | multiple (opt : String)
  | noValueAllowed (opt : String)
  deriving Repr, DecidableEq

/-- clap's first line for the error. -/
def CliError.render : CliError → String
  | .unexpected a =>
    s!"error: unexpected argument '{a}' found" ++
      (if a.startsWith "-" then s!"\n\n  tip: to pass '{a}' as a value, use '-- {a}'" else "")
  | .missingValue o => s!"error: a value is required for '{o}' but none was supplied"
  | .multiple o => s!"error: the argument '{o}' cannot be used multiple times"
  | .noValueAllowed o => s!"error: unexpected value for '{o}'"

/-- Find an option by long name. -/
def findLong (specs : List Spec) (n : String) : Option Spec :=
  specs.find? fun s => s.hasLong && s.long == n

/-- Find an option by short name. -/
def findShort (specs : List Spec) (c : Char) : Option Spec := specs.find? (·.short == some c)

/-- Record one occurrence, refusing a second occurrence of a flag or single value. -/
def record (p : Parsed) (s : Spec) (v : Option String) : Except CliError Parsed :=
  if (s.kind == .flag || s.kind == .single) && p.occ.any (·.1 == s.long) then
    .error (.multiple s.display)
  else .ok { p with occ := p.occ ++ [(s.long, v)] }

/-- A next argument usable as a value: not an option-looking string (but `-` is). -/
def valueLike (a : String) : Bool := a == "-" || !a.startsWith "-"

/-- A cluster of short options (the characters after `-`), with the remaining arguments.
Returns the updated result and the remaining arguments. -/
def shortCluster (specs : List Spec) (p : Parsed) :
    List Char → List String → Except CliError (Parsed × List String)
  | [], rest => .ok (p, rest)
  | c :: cs, rest =>
    if c == 'h' && (findShort specs 'h').isNone then
      .ok ({ p with help := some (p.help.getD false) }, rest)
    else
    match findShort specs c with
    | none => .error (.unexpected s!"-{c}")
    | some s =>
      if s.takesValue then
        match cs with
        | [] =>
          match rest with
          | v :: rest' =>
            if valueLike v then do
              let p ← record p s (some v)
              .ok (p, rest')
            else .error (.missingValue s.display)
          | [] => .error (.missingValue s.display)
        | '=' :: v => do
          let p ← record p s (some (String.ofList v))
          .ok (p, rest)
        | v => do
          let p ← record p s (some (String.ofList v))
          .ok (p, rest)
      else do
        let p ← record p s none
        shortCluster specs p cs rest

/-- **The parser**, on the arguments after the subcommand name. Structural on the argument list
with fuel equal to its length (each step consumes at least one argument). -/
def go (specs : List Spec) (maxPos : Nat) : Nat → Parsed → List String → Except CliError Parsed
  | 0, p, _ => .ok p
  | _ + 1, p, [] => .ok p
  | fuel + 1, p, a :: rest =>
    let posArg (p : Parsed) (x : String) : Except CliError Parsed :=
      if p.pos.length < maxPos then .ok { p with pos := p.pos ++ [x] }
      else .error (.unexpected x)
    if a == "--" then
      rest.foldlM posArg p
    else if a.startsWith "--" then
      let body := (a.drop 2).toString
      let (name, inl) : String × Option String :=
        match body.splitOn "=" with
        | [n] => (n, none)
        | n :: vs => (n, some ("=".intercalate vs))
        | [] => (body, none)
      if name == "help" && (findLong specs "help").isNone then
        go specs maxPos fuel { p with help := some true } rest
      else
      match findLong specs name with
      | none => .error (.unexpected a)
      | some s =>
        if s.takesValue then
          match inl with
          | some v => do go specs maxPos fuel (← record p s (some v)) rest
          | none =>
            match rest with
            | v :: rest' =>
              if valueLike v then do go specs maxPos fuel (← record p s (some v)) rest'
              else .error (.missingValue s.display)
            | [] => .error (.missingValue s.display)
        else
          match inl with
          | some _ => .error (.noValueAllowed s.display)
          | none => do go specs maxPos fuel (← record p s none) rest
    else if a.startsWith "-" && a != "-" then do
      let (p, rest') ← shortCluster specs p (a.toList.drop 1) rest
      go specs maxPos fuel p rest'
    else do
      go specs maxPos fuel (← posArg p a) rest

/-- **Parse a subcommand's arguments.** -/
def parse (specs : List Spec) (maxPos : Nat) (args : List String) : Except CliError Parsed :=
  go specs maxPos args.length {} args

/-! ## Reading the result -/

/-- Was the flag given? -/
def Parsed.flag (p : Parsed) (long : String) : Bool := p.occ.any (·.1 == long)

/-- How often was the option given? -/
def Parsed.count (p : Parsed) (long : String) : Nat := (p.occ.filter (·.1 == long)).length

/-- The values of the option, in order. -/
def Parsed.values (p : Parsed) (long : String) : List String :=
  p.occ.filterMap fun (n, v) => if n == long then v else none

/-- The value of a single-valued option. -/
def Parsed.value? (p : Parsed) (long : String) : Option String := (p.values long).head?

/-! ## Shared options -/

/-- `GeneralOpts`: `-v`/`--verbose` (count) and `--color`. -/
def generalSpecs : List Spec :=
  [{ long := "verbose", short := some 'v', kind := .count },
   { long := "color", kind := .single, valueName := "COLOR" }]

/-- `OutputArg`: `-o`/`--output`. -/
def outputSpecs : List Spec :=
  [{ long := "output", short := some 'o', kind := .single, valueName := "OUTPUT" }]

/-- The values clap accepts for `--color`. -/
def colorChoices : List String := ["auto", "never", "always", "always-ansi"]

end Silmaril.Wasm.Tools.OptGrammar
