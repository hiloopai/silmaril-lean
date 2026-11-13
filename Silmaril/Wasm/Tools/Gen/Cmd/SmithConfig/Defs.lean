module

public import Silmaril.Wasm.Tools.Gen.Cmd.Args.Defs
public import Silmaril.Wasm.Tools.Gen.Cmd.Smith.Defs
public import Lean.Data.Json.Parser
public import Lean.Data.Json.Printer

/-!
# `wasm-tools smith --config FILE`: the JSON configuration

Upstream reads the file as JSON into `wasm_smith::InternalOptionalConfig` (serde,
`rename_all = "kebab-case"`, `deny_unknown_fields`) and fills every option the command line
does not give from it (`module_config.or(config)`). The fields are the long names of the
options of `wasm-smith` (every option of `wasm-tools smith` but `-o`, `-t`,
`--ensure-termination`, `--fuel`, `--config`, `-v` and `--color`), with serde's types:

* booleans for the `--*-enabled`-style options (`Field.bool`);
* unsigned integers for the counts and sizes (`Field.num hi`: at most `hi`);
* path strings for `available-imports`, `exports`, `module-shape` (`Field.path`);
* `allowed-instructions`: the `u16` bit set of wasm-smith's `InstructionKind` flags
  (bit `i` is `Smith.allKinds[i]`; `Field.kinds`);
* `memory-offset-choices`: an array of three integers below `2^32` (`Field.triple`);
* `null` for any field: absent.

`fromJson fields j` gives the option values (as `Args.Val`s, in the form the command line
parser gives them, so that `config` and `model` read them unchanged), or serde's message
(without its line and column). `Thms.fromJson_sound`: every value is for a field of the
table, of the field's kind.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.SmithConfig

open Lean (Json JsonNumber)

/-- The JSON type of a configuration field. -/
inductive Field where
  | bool
  | num (hi : Nat)
  | path
  | kinds
  | triple
  deriving DecidableEq, Repr

/-- serde's name of the expected type. -/
def Field.expected : Field → String
  | .bool => "a boolean"
  | .num hi => if hi = 255 then "u8" else if hi = 2 ^ 32 - 1 then "u32" else "usize"
  | .path => "path string"
  | .kinds => "u16"
  | .triple => "a tuple of size 3"

/-- serde's description of an unexpected JSON value. -/
def unexpected : Json → String
  | .null => "unit value"
  | .bool b => s!"boolean `{b}`"
  | .num n =>
    if n.exponent = 0 then
      (if n.mantissa < 0 then s!"integer `{n.mantissa}`" else s!"integer `{n.mantissa}`")
    else s!"floating point `{n.toString}`"
  | .str s => s!"string {(Json.str s).compress}"
  | .arr _ => "sequence"
  | .obj _ => "map"

/-- An unsigned integer value, `none` for any other number. -/
def natOf? (n : JsonNumber) : Option Nat :=
  if n.exponent = 0 && n.mantissa ≥ 0 then some n.mantissa.toNat else none

/-- The kinds of a bit set of `InstructionKind` flags, comma-separated. -/
def kindsOfBits (n : Nat) : String :=
  ",".intercalate ((Smith.allKinds.zipIdx.filter fun (_, i) => n / 2 ^ i % 2 = 1).map (·.1))

/-- **The value of one field**, in the command line's form, or serde's message. -/
def value (f : Field) (j : Json) : Except String Args.Val :=
  let bad := .error s!"invalid type: {unexpected j}, expected {f.expected}"
  match f, j with
  | .bool, .bool b => .ok (.bool b)
  | .num hi, .num n =>
    match natOf? n with
    | some k => if k ≤ hi then .ok (.num k)
        else .error s!"invalid value: integer `{k}`, expected {f.expected}"
    | none =>
      if n.exponent = 0 then .error s!"invalid value: integer `{n.mantissa}`, expected {f.expected}"
      else bad
  | .path, .str s => .ok (.str s)
  | .kinds, .num n =>
    match natOf? n with
    | some k => if k < 2 ^ 16 then .ok (.str (kindsOfBits k))
        else .error s!"invalid value: integer `{k}`, expected u16"
    | none => bad
  | .triple, .arr xs =>
    match xs.toList.mapM (fun x => match x with | .num n => natOf? n | _ => none) with
    | some [a, b, c] =>
      if a < 2 ^ 32 && b < 2 ^ 32 && c < 2 ^ 32 then .ok (.str s!"{a},{b},{c}") else bad
    | _ => bad
  | _, _ => bad

/-- The message for an unknown field. -/
def unknownField (fields : List (String × Field)) (k : String) : String :=
  s!"unknown field `{k}`, expected one of " ++ ", ".intercalate (fields.map (s!"`{·.1}`"))

/-- One member of the document: its value appended, `null` skipped, an unknown key refused. -/
def step (fields : List (String × Field)) (acc : List (String × Args.Val)) :
    String × Json → Except String (List (String × Args.Val))
  | (k, v) =>
    match fields.lookup k with
    | none => .error (unknownField fields k)
    | some f =>
      if v == .null then .ok acc else
      match value f v with
      | .ok x => .ok (acc ++ [(k, x)])
      | .error e => .error e

/-- **The option values of a configuration document.** -/
def fromJson (fields : List (String × Field)) (j : Json) : Except String (List (String × Args.Val)) :=
  match j with
  | .obj kvs => kvs.toList.foldlM (step fields) []
  | .arr xs => .error s!"invalid length {xs.size}, expected struct InternalOptionalConfig with {fields.length} elements"
  | _ => .error s!"invalid type: {unexpected j}, expected struct InternalOptionalConfig"

/-- **The configuration of a JSON text**: parse, then `fromJson`. -/
def parse (fields : List (String × Field)) (text : String) :
    Except String (List (String × Args.Val)) :=
  match Json.parse text with
  | .error e => .error e
  | .ok j => fromJson fields j

/-- The field of an option of the command line grammar (`none`: not a configuration field). -/
def fieldOfOpt (o : Args.Opt) : Option Field :=
  if o.long ∈ ["output", "wat", "ensure-termination", "fuel", "config", "verbose", "color"] then
    none
  else if o.long = "allowed-instructions" then some .kinds
  else if o.long = "memory-offset-choices" then some .triple
  else match o.kind with
    | .bool => some .bool
    | .u64 => some (.num (2 ^ 64 - 1))
    | .ranged hi => some (.num hi)
    | .str => some .path
    | _ => none

/-- The configuration fields of a command line grammar, in its order. -/
def fieldsOf (sp : Args.Spec) : List (String × Field) :=
  sp.opts.filterMap fun o => (fieldOfOpt o).map (o.long, ·)

end Silmaril.Wasm.Tools.Gen.Cmd.SmithConfig
