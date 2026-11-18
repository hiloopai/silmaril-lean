module

public import Silmaril.Formats.LeanNDJSON.Defs
public import Silmaril.Formats.Json.Thms

/-!
# Lean-NDJSON: strict decoding of lean4export 3.1.0 files

`parseFile bytes` splits the bytes into lines (LF; a final LF is optional; no empty lines), parses
each line as JSON with exact integers, decodes the metadata line, then decodes every record into an
`Event`. Decoding is **strict**: every object must have exactly the documented keys (no extra,
missing or duplicate keys), ids are non-negative integers, and only the 3.1.0 record shapes are
accepted. The metadata must name the exporter `lean4export` and format version `3.1.0`; the
exporter and Lean versions are kept.

A rejection says where (`DecodeError`): the envelope, or the line number of the record, with the
record's tag when it is recognised but not supported (`mdata`).

This is syntax only. It does not validate references (`…LeanNDJSON.Validate`), type-check any
declaration, or treat any record as evidence of anything.
-/

@[expose] public section

namespace Silmaril.Formats.LeanNDJSON

open Silmaril.Formats

/-- The object has exactly these keys, each once. -/
def exactKeys (value : Json.Ast Int) (keys : List String) : Bool :=
  match value with
  | .map entries => decide ((entries.toEntries.map Prod.fst).Perm (keys.map Json.stringUnits))
  | _ => false

def object? {A : Type} (value : Json.Ast Int) (keys : List String)
    (decode : Json.Ast Int → Option A) : Option A :=
  if exactKeys value keys then decode value else none

def nat? : Json.Ast Int → Option Nat
  | .scalar (some (.number i)) => if 0 ≤ i then some i.toNat else none
  | _ => none

def bool? : Json.Ast Int → Option Bool
  | .scalar (some (.bool b)) => some b
  | _ => none

def list? {A : Type} (decode : Json.Ast Int → Option A) : Json.Ast Int → Option (List A)
  | .list entries => entries.toList.mapM decode
  | _ => none

def field {A : Type} (decode : Json.Ast Int → Option A) (value : Json.Ast Int) (key : String) :=
  (Json.getMember? value key).bind decode

def naturalString? (value : Json.Ast Int) : Option String := do
  let text ← Json.getString? value
  if !text.isEmpty && text.toList.all Char.isDigit then some text else none

def binder? (value : Json.Ast Int) : Option BinderInfo := do
  match ← Json.getString? value with
  | "default" => some .default
  | "implicit" => some .implicit
  | "strictImplicit" => some .strictImplicit
  | "instImplicit" => some .instImplicit
  | _ => none

def safety? (value : Json.Ast Int) : Option Safety := do
  match ← Json.getString? value with
  | "safe" => some .safeCode
  | "unsafe" => some .unsafeCode
  | "partial" => some .partialCode
  | _ => none

def quotKind? (value : Json.Ast Int) : Option QuotKind := do
  match ← Json.getString? value with
  | "type" => some .type
  | "ctor" => some .ctor
  | "lift" => some .lift
  | "ind" => some .ind
  | _ => none

def hints? (value : Json.Ast Int) : Option Hints :=
  match Json.getString? value with
  | some "opaque" => some .opaque
  | some "abbrev" => some .abbrev
  | _ => object? value ["regular"] fun o => .regular <$> field nat? o "regular"

/-- `{tag: {keys…}}`. -/
def tagged {A : Type} (value : Json.Ast Int) (tag : String) (keys : List String)
    (decode : Json.Ast Int → Option A) : Option A :=
  object? value [tag] fun o => (Json.getMember? o tag).bind fun inner => object? inner keys decode

def nameStr? (value : Json.Ast Int) : Option Event :=
  object? value ["in", "str"] fun o => do
    let i ← field nat? o "in"
    let node ← (Json.getMember? o "str").bind fun inner => object? inner ["pre", "str"] fun n => do
      pure (NameNode.str (← field nat? n "pre") (← field Json.getString? n "str"))
    pure (.name i node)

def nameNum? (value : Json.Ast Int) : Option Event :=
  object? value ["in", "num"] fun o => do
    let i ← field nat? o "in"
    let node ← (Json.getMember? o "num").bind fun inner => object? inner ["pre", "i"] fun n => do
      pure (NameNode.num (← field nat? n "pre") (← field nat? n "i"))
    pure (.name i node)

def levelUnary? (tag : String) (build : Nat → LevelNode) (value : Json.Ast Int) : Option Event :=
  object? value ["il", tag] fun o => do
    pure (.level (← field nat? o "il") (build (← field nat? o tag)))

def levelBinary? (tag : String) (build : Nat → Nat → LevelNode) (value : Json.Ast Int) :
    Option Event :=
  object? value ["il", tag] fun o => do
    let index ← field nat? o "il"
    match ← field (list? nat?) o tag with
    | [a, b] => pure (.level index (build a b))
    | _ => none

def exprUnary? {A : Type} (tag : String) (decode : Json.Ast Int → Option A)
    (build : A → ExprNode) (value : Json.Ast Int) : Option Event :=
  object? value ["ie", tag] fun o => do
    pure (.expr (← field nat? o "ie") (build (← field decode o tag)))

def exprObject? (tag : String) (keys : List String) (decode : Json.Ast Int → Option ExprNode)
    (value : Json.Ast Int) : Option Event :=
  object? value ["ie", tag] fun o => do
    let index ← field nat? o "ie"
    let node ← (Json.getMember? o tag).bind fun inner => object? inner keys decode
    pure (.expr index node)

def exprBinder? (tag : String) (build : Nat → Nat → Nat → BinderInfo → ExprNode)
    (value : Json.Ast Int) : Option Event :=
  exprObject? tag ["name", "type", "body", "binderInfo"] (fun o => do
    pure (build (← field nat? o "name") (← field nat? o "type")
      (← field nat? o "body") (← field binder? o "binderInfo"))) value

def inductiveType? (value : Json.Ast Int) : Option InductiveType :=
  object? value ["name", "levelParams", "type", "numParams", "numIndices", "all", "ctors",
      "numNested", "isRec", "isUnsafe", "isReflexive"] fun o => do
    pure { name := ← field nat? o "name", levelParams := ← field (list? nat?) o "levelParams",
           type := ← field nat? o "type", numParams := ← field nat? o "numParams",
           numIndices := ← field nat? o "numIndices", all := ← field (list? nat?) o "all",
           ctors := ← field (list? nat?) o "ctors", numNested := ← field nat? o "numNested",
           isRec := ← field bool? o "isRec", isUnsafe := ← field bool? o "isUnsafe",
           isReflexive := ← field bool? o "isReflexive" }

def constructor? (value : Json.Ast Int) : Option Constructor :=
  object? value ["name", "levelParams", "type", "induct", "cidx", "numParams", "numFields",
      "isUnsafe"] fun o => do
    pure { name := ← field nat? o "name", levelParams := ← field (list? nat?) o "levelParams",
           type := ← field nat? o "type", induct := ← field nat? o "induct",
           cidx := ← field nat? o "cidx", numParams := ← field nat? o "numParams",
           numFields := ← field nat? o "numFields", isUnsafe := ← field bool? o "isUnsafe" }

def recursorRule? (value : Json.Ast Int) : Option RecursorRule :=
  object? value ["ctor", "nfields", "rhs"] fun o => do
    pure ⟨← field nat? o "ctor", ← field nat? o "nfields", ← field nat? o "rhs"⟩

def recursor? (value : Json.Ast Int) : Option Recursor :=
  object? value ["name", "levelParams", "type", "all", "numParams", "numIndices", "numMotives",
      "numMinors", "rules", "k", "isUnsafe"] fun o => do
    pure { name := ← field nat? o "name", levelParams := ← field (list? nat?) o "levelParams",
           type := ← field nat? o "type", all := ← field (list? nat?) o "all",
           numParams := ← field nat? o "numParams", numIndices := ← field nat? o "numIndices",
           numMotives := ← field nat? o "numMotives", numMinors := ← field nat? o "numMinors",
           rules := ← field (list? recursorRule?) o "rules", k := ← field bool? o "k",
           isUnsafe := ← field bool? o "isUnsafe" }

/-- **Decode one record**, strictly. -/
def decodeEvent? (value : Json.Ast Int) : Option Event :=
  nameStr? value <|> nameNum? value <|>
  levelUnary? "succ" .succ value <|> levelUnary? "param" .param value <|>
  levelBinary? "max" .max value <|> levelBinary? "imax" .imax value <|>
  exprUnary? "bvar" nat? .bvar value <|> exprUnary? "sort" nat? .sort value <|>
  exprUnary? "natVal" naturalString? .natVal value <|>
  exprUnary? "strVal" Json.getString? .strVal value <|>
  exprObject? "const" ["name", "us"] (fun o => do
    pure (.const (← field nat? o "name") (← field (list? nat?) o "us"))) value <|>
  exprObject? "app" ["fn", "arg"] (fun o => do
    pure (.app (← field nat? o "fn") (← field nat? o "arg"))) value <|>
  exprBinder? "lam" .lam value <|> exprBinder? "forallE" .forallE value <|>
  exprObject? "letE" ["name", "type", "value", "body", "nondep"] (fun o => do
    pure (.letE (← field nat? o "name") (← field nat? o "type")
      (← field nat? o "value") (← field nat? o "body") (← field bool? o "nondep"))) value <|>
  exprObject? "proj" ["typeName", "idx", "struct"] (fun o => do
    pure (.proj (← field nat? o "typeName") (← field nat? o "idx") (← field nat? o "struct"))) value <|>
  tagged value "axiom" ["name", "levelParams", "type", "isUnsafe"] (fun o => do
    pure (.declaration (.axiomCode (← field nat? o "name") (← field (list? nat?) o "levelParams")
      (← field nat? o "type") (← field bool? o "isUnsafe")))) <|>
  tagged value "thm" ["name", "levelParams", "type", "value", "all"] (fun o => do
    pure (.declaration (.theoremCode (← field nat? o "name") (← field (list? nat?) o "levelParams")
      (← field nat? o "type") (← field nat? o "value") (← field (list? nat?) o "all")))) <|>
  tagged value "def" ["name", "levelParams", "type", "value", "hints", "safety", "all"] (fun o => do
    pure (.declaration (.definitionCode (← field nat? o "name") (← field (list? nat?) o "levelParams")
      (← field nat? o "type") (← field nat? o "value") (← field hints? o "hints")
      (← field safety? o "safety") (← field (list? nat?) o "all")))) <|>
  tagged value "opaque" ["name", "levelParams", "type", "value", "isUnsafe", "all"] (fun o => do
    pure (.declaration (.opaqueCode (← field nat? o "name") (← field (list? nat?) o "levelParams")
      (← field nat? o "type") (← field nat? o "value") (← field bool? o "isUnsafe")
      (← field (list? nat?) o "all")))) <|>
  tagged value "quot" ["name", "levelParams", "type", "kind"] (fun o => do
    pure (.declaration (.quot (← field nat? o "name") (← field (list? nat?) o "levelParams")
      (← field nat? o "type") (← field quotKind? o "kind")))) <|>
  tagged value "inductive" ["types", "ctors", "recs"] (fun o => do
    pure (.declaration (.inductive (← field (list? inductiveType?) o "types")
      (← field (list? constructor?) o "ctors") (← field (list? recursor?) o "recs"))))

/-- The metadata line. -/
structure Metadata where
  exporterVersion : String
  leanVersion : String
  leanGitHash : String
  formatVersion : String
  deriving DecidableEq, Repr

/-- Decode the metadata: exporter `lean4export`, format `3.1.0`. -/
def decodeMetadata? (value : Json.Ast Int) : Option Metadata :=
  tagged value "meta" ["exporter", "lean", "format"] fun o => do
    let exporter ← Json.getMember? o "exporter"
    let exporterVersion ← object? exporter ["name", "version"] fun e => do
      let name ← field Json.getString? e "name"
      if name = "lean4export" then field Json.getString? e "version" else none
    let lean ← Json.getMember? o "lean"
    let (leanVersion, leanGitHash) ← object? lean ["version", "githash"] fun l => do
      pure (← field Json.getString? l "version", ← field Json.getString? l "githash")
    let format ← Json.getMember? o "format"
    let formatVersion ← object? format ["version"] fun f => do
      let version ← field Json.getString? f "version"
      if version = "3.1.0" then some version else none
    pure ⟨exporterVersion, leanVersion, leanGitHash, formatVersion⟩

/-- Why a file was not decoded. -/
inductive DecodeError where
  /-- The file is empty, or its first line is not lean4export 3.1.0 metadata. -/
  | envelope (why : String)
  /-- A record (by line number, from `1` for the metadata) is not valid JSON or not a supported
  3.1.0 record. -/
  | record (line : Nat) (why : String)
  deriving DecidableEq, Repr

/-- A decoded file: its metadata and its records, in order. -/
structure EventFile where
  metadata : Metadata
  events : List Event
  deriving Repr

/-- Split bytes at LF; a final LF ends the last line rather than starting an empty one. -/
def splitLines (bytes : List UInt8) : List (List UInt8) :=
  let parts := bytes.splitOn 0x0A
  if parts.getLast? = some [] then parts.dropLast else parts

/-- The tag of a record, for messages: its first key other than an id key. -/
def recordTag (value : Json.Ast Int) : String :=
  match value with
  | .map entries =>
    match (entries.toEntries.map Prod.fst).filterMap Json.unitsString? |>.filter
        (fun k => k ∉ ["in", "il", "ie"]) with
    | k :: _ => k
    | [] => "(no tag)"
  | _ => "(not an object)"

/-- Decode the records after the metadata, numbering lines from `first`. -/
def decodeRecords (first : Nat) : List (List UInt8) → Except DecodeError (List Event)
  | [] => .ok []
  | l :: ls => do
    let some v := Json.parseInteger? (Bytes.ofList l)
      | .error (.record first "not JSON with integer numbers")
    let some e := decodeEvent? v
      | .error (.record first (match recordTag v with
          | "mdata" => "mdata is not supported (export without --export-mdata)"
          | t => s!"not a supported lean4export 3.1.0 record (tag {t})"))
    return e :: (← decodeRecords (first + 1) ls)

/-- **Decode a Lean-NDJSON file.** -/
def parseFile (bytes : List UInt8) : Except DecodeError EventFile := do
  match splitLines bytes with
  | [] => .error (.envelope "empty file")
  | m :: ls =>
    let some mv := Json.parseInteger? (Bytes.ofList m)
      | .error (.envelope "the first line is not JSON")
    let some md := decodeMetadata? mv
      | .error (.envelope "the first line is not lean4export 3.1.0 metadata")
    if ls.any List.isEmpty then .error (.envelope "empty line") else
    return ⟨md, ← decodeRecords 2 ls⟩

end Silmaril.Formats.LeanNDJSON
