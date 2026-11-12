module

public import Silmaril.Wasm.Tools.Wast.Syntax.Defs
public import Silmaril.Wasm.Tools.Wast.Lex.Defs
public import Silmaril.Wasm.Text.ValuesExamplesLemmas

/-!
# `json-from-wast`: the JSON form of a `.wast` script

The pure core of `wasm-tools json-from-wast` (1.262.0: `src/bin/wasm-tools/json_from_wast.rs`,
`crates/json-from-wast/src/{lib,build}.rs`): a script (`Silmaril.Wasm.Tools.Wast.Script`)
becomes the `wast2json`-style JSON document (`Wast { source_filename, commands }`) and the
list of auxiliary files (`name`, bytes) it refers to.

* `Json` is a JSON tree with ordered object members; `Json.compact` and `Json.pretty` are
  `serde_json::to_string` and `to_string_pretty` (two-space indentation, `": "`, `[]`/`{}`
  for empty containers, serde's string escapes).
* Literal values are read by silmaril-lean's literal relations: `Text.IN N` for `iN`
  (`intLit?`, sound by `ValuesExamples.in_iff`), `Text.FN t` for floats (`floatLit?`,
  `ValuesExamples.fn_iff`), `Text.UN N` for unsigned fields (`natLit?`). The statements
  are in `Silmaril.Wasm.Tools.Wast.Json.Thms`.
* Modules are encoded by an `Encoder` (a parameter: the text-to-binary encoder of the
  `parse` subcommand). `(module binary …)` is its bytes; `(module quote …)` is written as
  text (`.wat`) and, for non-`assert_malformed` commands, also encoded when the encoder
  accepts the text, exactly as `build.rs` `emit_file`.
* `line` is the 1-based line of the token `wast` takes the span of (`linePos`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding
open Silmaril.Wasm Silmaril.Wasm.Text

/-! ## JSON -/

/-- JSON with ordered object members. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))
  deriving Inhabited, Repr

/-- serde_json's escape of one character. -/
def escChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat == 8 then "\\b"
  else if c.toNat == 12 then "\\f"
  else if c.toNat < 32 then
    let h := "0123456789abcdef".toList
    "\\u00" ++ String.singleton (h.getD (c.toNat / 16) '0') ++ String.singleton (h.getD (c.toNat % 16) '0')
  else String.singleton c

/-- A JSON string literal. -/
def jsonStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ escChar c) "" ++ "\""

mutual
  /-- `serde_json::to_string`. -/
  def Json.compact : Json → String
    | .null => "null"
    | .bool b => if b then "true" else "false"
    | .num n => toString n
    | .str s => jsonStr s
    | .arr xs => "[" ++ Json.compactList xs ++ "]"
    | .obj kvs => "{" ++ Json.compactObj kvs ++ "}"

  def Json.compactList : List Json → String
    | [] => ""
    | [x] => x.compact
    | x :: xs => x.compact ++ "," ++ Json.compactList xs

  def Json.compactObj : List (String × Json) → String
    | [] => ""
    | [(k, v)] => jsonStr k ++ ":" ++ v.compact
    | (k, v) :: kvs => jsonStr k ++ ":" ++ v.compact ++ "," ++ Json.compactObj kvs
end

/-- `n` levels of two-space indentation. -/
def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

mutual
  /-- `serde_json::to_string_pretty`, at indentation level `d`. -/
  def Json.prettyAt (d : Nat) : Json → String
    | .arr [] => "[]"
    | .obj [] => "{}"
    | .arr xs => "[\n" ++ Json.prettyList (d + 1) xs ++ "\n" ++ indent d ++ "]"
    | .obj kvs => "{\n" ++ Json.prettyObj (d + 1) kvs ++ "\n" ++ indent d ++ "}"
    | j => j.compact

  def Json.prettyList (d : Nat) : List Json → String
    | [] => ""
    | [x] => indent d ++ x.prettyAt d
    | x :: xs => indent d ++ x.prettyAt d ++ ",\n" ++ Json.prettyList d xs

  def Json.prettyObj (d : Nat) : List (String × Json) → String
    | [] => ""
    | [(k, v)] => indent d ++ jsonStr k ++ ": " ++ v.prettyAt d
    | (k, v) :: kvs => indent d ++ jsonStr k ++ ": " ++ v.prettyAt d ++ ",\n" ++ Json.prettyObj d kvs
end

def Json.pretty (j : Json) : String := j.prettyAt 0

/-! ### Fast printers

`Json.compact` and `Json.prettyAt` build their output by nested `++`, which copies the left
operand at every level; the `…Into` printers append to one accumulator instead. They are
equal to the specification printers (`Json.compactInto_eq`, `Json.prettyInto_eq` in
`Json.Thms`). -/

/-- `jsonStr` appended to an accumulator. -/
def jsonStrInto (acc s : String) : String :=
  s.foldl (fun acc c => acc ++ escChar c) (acc ++ "\"") ++ "\""

mutual
  def Json.compactInto (acc : String) : Json → String
    | .arr xs => Json.compactListInto (acc ++ "[") xs ++ "]"
    | .obj kvs => Json.compactObjInto (acc ++ "{") kvs ++ "}"
    | .str s => jsonStrInto acc s
    | j => acc ++ j.compact

  def Json.compactListInto (acc : String) : List Json → String
    | [] => acc
    | [x] => x.compactInto acc
    | x :: xs => Json.compactListInto (x.compactInto acc ++ ",") xs

  def Json.compactObjInto (acc : String) : List (String × Json) → String
    | [] => acc
    | [(k, v)] => v.compactInto (jsonStrInto acc k ++ ":")
    | (k, v) :: kvs => Json.compactObjInto (v.compactInto (jsonStrInto acc k ++ ":") ++ ",") kvs
end

mutual
  def Json.prettyInto (d : Nat) (acc : String) : Json → String
    | .arr [] => acc ++ "[]"
    | .obj [] => acc ++ "{}"
    | .arr xs => Json.prettyListInto (d + 1) (acc ++ "[\n") xs ++ "\n" ++ indent d ++ "]"
    | .obj kvs => Json.prettyObjInto (d + 1) (acc ++ "{\n") kvs ++ "\n" ++ indent d ++ "}"
    | j => j.compactInto acc

  def Json.prettyListInto (d : Nat) (acc : String) : List Json → String
    | [] => acc
    | [x] => x.prettyInto d (acc ++ indent d)
    | x :: xs => Json.prettyListInto d (x.prettyInto d (acc ++ indent d) ++ ",\n") xs

  def Json.prettyObjInto (d : Nat) (acc : String) : List (String × Json) → String
    | [] => acc
    | [(k, v)] => v.prettyInto d (jsonStrInto (acc ++ indent d) k ++ ": ")
    | (k, v) :: kvs =>
      Json.prettyObjInto d (v.prettyInto d (jsonStrInto (acc ++ indent d) k ++ ": ") ++ ",\n") kvs
end

/-- The printers the tool runs (`Json.compactFast_eq`, `Json.prettyFast_eq`). -/
def Json.compactFast (j : Json) : String := j.compactInto ""
def Json.prettyFast (j : Json) : String := j.prettyInto 0 ""

/-! ## Literals -/

/-- Bytes as a string, if valid UTF-8 (`wast`'s `&str`). -/
def utf8? (b : List UInt8) : Option String := String.fromUTF8? ⟨b.toArray⟩

/-- `iN` literal (`Text.IN N`). -/
def intLit? (N : Nat) (s : String) : Option (BitVec N) :=
  (ValuesExamples.inCands N s.toList).head?

/-- `uN` literal (`Text.UN N`), with `wast`'s optional `+`. -/
def natLit? (N : Nat) (s : String) : Option Nat :=
  let cs := if s.startsWith "+" then (s.drop 1).toString.toList else s.toList
  (ValuesExamples.unCands N cs).head?

/-- `fN` literal bits (`Text.FN t`). -/
def floatLit? (t : FloatType) (s : String) : Option (BitVec t.width) :=
  (ValuesExamples.fnCands t s.toList).head?

/-! ### A fast path for float literals

`floatLit?` searches every split of the token (sign / magnitude, mantissa / exponent), which
is quadratic to cubic in the token length; `floatLitFast?` cuts at the first sign
character and the first exponent mark and asks the same candidate functions only about
that cut. It is sound for `Text.FN` (`floatLitFast?_sound` in `Json.Thms`), and agrees with
`floatLit?` on every float literal of the test corpora (`tools/wasm-tools/tests/wast`). -/

/-- Split off a leading sign. -/
def signSplit : List Char → List Char × List Char
  | '-' :: r => (['-'], r)
  | '+' :: r => (['+'], r)
  | r => ([], r)

/-- The magnitude, cut at the first exponent mark. -/
def fmagFast? (cs : List Char) : Option FloatMag :=
  if cs = "inf".toList then some .inf
  else if cs = "nan".toList then some .nan
  else if cs.take "nan:0x".toList.length = "nan:0x".toList then
    (ValuesExamples.hexNumVal? (cs.drop "nan:0x".toList.length)).map .nanPayload
  else if cs.take 2 = ['0', 'x'] then
    let ds := cs.drop 2
    let isMark := fun c => c == 'p' || c == 'P'
    let m := ds.takeWhile (fun c => !isMark c)
    let e := ds.dropWhile (fun c => !isMark c)
    match (ValuesExamples.mantCands true m).head?, (ValuesExamples.expCands true e).head? with
    | some mk, some ex => some (.hex mk.1 (ex - 4 * mk.2))
    | _, _ => none
  else
    let isMark := fun c => c == 'e' || c == 'E'
    let m := cs.takeWhile (fun c => !isMark c)
    let e := cs.dropWhile (fun c => !isMark c)
    match (ValuesExamples.mantCands false m).head?, (ValuesExamples.expCands false e).head? with
    | some mk, some ex => some (.dec mk.1 (ex - mk.2))
    | _, _ => none

/-- `fN` literal bits, fast path. -/
def floatLitFast? (t : FloatType) (s : String) : Option (BitVec t.width) :=
  match (ValuesExamples.signCands (signSplit s.toList).1).head?, fmagFast? (signSplit s.toList).2 with
  | some sg, some v =>
    (magBits t v).map fun n => BitVec.ofNat t.width (if sg = -1 then n + 2 ^ (t.width - 1) else n)
  | _, _ => none

/-- Signed decimal of an `N`-bit pattern (Rust's `iN::to_string`). -/
def signedStr {N : Nat} (b : BitVec N) : String := toString b.toInt

/-! ## Values -/

abbrev LowerM := Except String

def oneArg (h : String) : List String → LowerM String
  | [a] => pure a
  | _ => throw s!"expected one argument to `{h}`"

def lit {α : Type} (what : String) (o : Option α) : LowerM α :=
  match o with
  | some a => pure a
  | none => throw s!"invalid {what} literal"

/-- A float lane or argument: bits, or a NaN pattern when `ret`. -/
def floatJ (t : FloatType) (ret : Bool) (s : String) : LowerM Json :=
  if ret && s == "nan:canonical" then pure (.str "nan:canonical")
  else if ret && s == "nan:arithmetic" then pure (.str "nan:arithmetic")
  else do
    let b ← lit (if t == .f32 then "f32" else "f64") (floatLitFast? t s)
    pure (.str (toString b.toNat))

/-- `v128.const shape lane*`. -/
def v128J (ret : Bool) : List String → LowerM Json
  | shape :: lanes => do
    let (lt, n, f) : String × Nat × (String → LowerM Json) ← match shape with
      | "i8x16" => pure ("i8", 16, fun s => do pure (.str (signedStr (← lit "i8" (intLit? 8 s)))))
      | "i16x8" => pure ("i16", 8, fun s => do pure (.str (signedStr (← lit "i16" (intLit? 16 s)))))
      | "i32x4" => pure ("i32", 4, fun s => do pure (.str (signedStr (← lit "i32" (intLit? 32 s)))))
      | "i64x2" => pure ("i64", 2, fun s => do pure (.str (signedStr (← lit "i64" (intLit? 64 s)))))
      | "f32x4" => pure ("f32", 4, floatJ .f32 ret)
      | "f64x2" => pure ("f64", 2, floatJ .f64 ret)
      | _ => throw "expected a v128 lane shape"
    unless lanes.length == n do throw s!"wrong number of lane literals for {shape}"
    let vs ← lanes.mapM f
    pure (.obj [("type", .str "v128"), ("lane_type", .str lt), ("value", .arr vs)])
  | [] => throw "expected a v128 lane shape"

/-- `ref.null ht`. -/
def refNullJ : String → LowerM Json
  | "func" => pure (.obj [("type", .str "funcref"), ("value", .str "null")])
  | "extern" => pure (.obj [("type", .str "externref"), ("value", .str "null")])
  | "any" => pure (.obj [("type", .str "anyref"), ("value", .str "null")])
  | "none" => pure (.obj [("type", .str "nullref")])
  | "nofunc" => pure (.obj [("type", .str "nullfuncref")])
  | "noextern" => pure (.obj [("type", .str "nullexternref")])
  | "exn" => pure (.obj [("type", .str "exnref"), ("value", .str "null")])
  | "eq" => pure (.obj [("type", .str "eqref")])
  | "struct" => pure (.obj [("type", .str "structref")])
  | "array" => pure (.obj [("type", .str "arrayref")])
  | "i31" => pure (.obj [("type", .str "i31ref")])
  | "noexn" => pure (.obj [("type", .str "nullexnref")])
  | "cont" => pure (.obj [("type", .str "contref"), ("value", .str "null")])
  | "nocont" => pure (.obj [("type", .str "nullcontref")])
  | _ => throw "unsupported heap type found in `ref.null`"

/-- Heads of core arguments (`WastArgCore`). -/
def coreArgHeads : List String :=
  ["i32.const", "i64.const", "f32.const", "f64.const", "v128.const", "ref.null",
   "ref.extern", "ref.host"]

/-- Heads of core results (`WastRetCore`). -/
def coreRetHeads : List String :=
  coreArgHeads ++ ["ref.func", "ref.any", "ref.eq", "ref.array", "ref.struct", "ref.i31",
    "ref.i31_shared", "either"]

/-- Heads of component values (`WastVal`). -/
def compHeads : List String :=
  ["bool.const", "u8.const", "s8.const", "u16.const", "s16.const", "u32.const", "s32.const",
   "u64.const", "s64.const", "f32.const", "f64.const", "char.const", "str.const",
   "list.const", "record.const", "tuple.const", "variant.const", "enum.const", "option.none",
   "option.some", "result.ok", "result.err", "flags.const"]

def tyObj (t : String) (rest : List (String × Json) := []) : Json := .obj (("type", .str t) :: rest)

def strJ (b : List UInt8) : LowerM String :=
  match utf8? b with
  | some s => pure s
  | none => throw "malformed UTF-8 encoding"

/-- A core constant (`WastArgCore` when `ret = false`, `WastRetCore` when `ret`). -/
def coreJ (ret : Bool) : Val → LowerM Json
  | .lit "i32.const" as => do
    let a ← oneArg "i32.const" as
    pure (tyObj "i32" [("value", .str (signedStr (← lit "i32" (intLit? 32 a))))])
  | .lit "i64.const" as => do
    let a ← oneArg "i64.const" as
    pure (tyObj "i64" [("value", .str (signedStr (← lit "i64" (intLit? 64 a))))])
  | .lit "f32.const" as => do
    pure (tyObj "f32" [("value", ← floatJ .f32 ret (← oneArg "f32.const" as))])
  | .lit "f64.const" as => do
    pure (tyObj "f64" [("value", ← floatJ .f64 ret (← oneArg "f64.const" as))])
  | .lit "v128.const" as => v128J ret as
  | .lit "ref.null" [ht] => refNullJ ht
  | .lit "ref.null" [] => if ret then pure (tyObj "refnull") else throw "expected a heap type"
  | .lit "ref.extern" [n] => do
    pure (tyObj "externref" [("value", .str (toString (← lit "u32" (natLit? 32 n))))])
  | .lit "ref.extern" [] => if ret then pure (tyObj "externref") else throw "expected a u32"
  | .lit "ref.host" [n] => do
    pure (tyObj "anyref" [("value", .str (toString (← lit "u32" (natLit? 32 n))))])
  | .lit "ref.func" [] => pure (tyObj "funcref")
  | .lit "ref.func" [n] => do
    pure (tyObj "funcref" [("value", .obj [("index", .num (← lit "u32" (natLit? 32 n)))])])
  | .lit "ref.any" [] => pure (tyObj "anyref")
  | .lit "ref.eq" [] => pure (tyObj "eqref")
  | .lit "ref.array" [] => pure (tyObj "arrayref")
  | .lit "ref.struct" [] => pure (tyObj "structref")
  | .lit "ref.i31" [] => pure (tyObj "i31ref")
  | .lit "ref.i31_shared" [] => pure (tyObj "i31refshared")
  | .mixed "either" [] vs => do
    let js ← vs.attach.mapM fun ⟨v, _⟩ => coreJ ret v
    pure (tyObj "either" [("values", .arr js)])
  | .lit h _ | .mixed h _ _ => throw s!"malformed `{h}` constant"

/-- `uN`/`sN` component integers. -/
def compIntJ (h : String) (a : String) : LowerM String :=
  match h with
  | "u8.const" => do pure (toString (← lit "u8" (natLit? 8 a)))
  | "u16.const" => do pure (toString (← lit "u16" (natLit? 16 a)))
  | "u32.const" => do pure (toString (← lit "u32" (natLit? 32 a)))
  | "u64.const" => do pure (toString (← lit "u64" (natLit? 64 a)))
  | "s8.const" => do pure (signedStr (← lit "i8" (intLit? 8 a)))
  | "s16.const" => do pure (signedStr (← lit "i16" (intLit? 16 a)))
  | "s32.const" => do pure (signedStr (← lit "i32" (intLit? 32 a)))
  | "s64.const" => do pure (signedStr (← lit "i64" (intLit? 64 a)))
  | _ => throw s!"malformed `{h}` constant"

/-- A component value (`WastVal`). -/
def compJ : Val → LowerM Json
  | .lit "bool.const" ["true"] => pure (tyObj "bool" [("value", .bool true)])
  | .lit "bool.const" ["false"] => pure (tyObj "bool" [("value", .bool false)])
  | .lit "f32.const" [a] => do
    let b ← lit "f32" (floatLitFast? .f32 a)
    pure (tyObj "f32" [("value", .str (toString b.toNat))])
  | .lit "f64.const" [a] => do
    let b ← lit "f64" (floatLitFast? .f64 a)
    pure (tyObj "f64" [("value", .str (toString b.toNat))])
  | .lit "option.none" [] => pure (tyObj "option" [("value", .null)])
  | .lit h [a] => do
    let t := (h.dropEnd 6).toString
    pure (tyObj t [("value", .str (← compIntJ h a))])
  | .mixed "char.const" [s] [] => do
    let str ← strJ s
    match str.toList with
    | [_] => pure (tyObj "char" [("value", .str str)])
    | [] => throw "empty string"
    | _ => throw "more than one character"
  | .mixed "str.const" [s] [] => do pure (tyObj "string" [("value", .str (← strJ s))])
  | .mixed "enum.const" [s] [] => do pure (tyObj "enum" [("value", .str (← strJ s))])
  | .mixed "flags.const" ss [] => do
    let names ← ss.mapM strJ
    pure (tyObj "flags" [("value", .arr (names.map .str))])
  | .mixed "list.const" [] vs => do
    let js ← vs.attach.mapM fun ⟨v, _⟩ => compJ v
    pure (tyObj "list" [("value", .arr js)])
  | .mixed "tuple.const" [] vs => do
    let js ← vs.attach.mapM fun ⟨v, _⟩ => compJ v
    pure (tyObj "tuple" [("value", .arr js)])
  | .mixed "record.const" [] fs => do
    let js ← fs.attach.mapM fun
      | ⟨.mixed "field" [n] [v], _⟩ => do
        let n ← strJ n
        pure (Json.arr [.str n, ← compJ v])
      | _ => throw "expected `(field \"name\" value)`"
    pure (tyObj "record" [("value", .arr js)])
  | .mixed "variant.const" [c] vs => do
    let c ← strJ c
    match vs with
    | [] => pure (tyObj "variant" [("value", .obj [("case", .str c)])])
    | [v] => pure (tyObj "variant" [("value", .obj [("case", .str c), ("payload", ← compJ v)])])
    | _ => throw "malformed `variant.const`"
  | .mixed "option.some" [] [v] => do pure (tyObj "option" [("value", ← compJ v)])
  | .mixed "result.ok" [] [] => pure (tyObj "result" [("value", .obj [("Ok", .null)])])
  | .mixed "result.ok" [] [v] => do pure (tyObj "result" [("value", .obj [("Ok", ← compJ v)])])
  | .mixed "result.err" [] [] => pure (tyObj "result" [("value", .obj [("Err", .null)])])
  | .mixed "result.err" [] [v] => do pure (tyObj "result" [("value", .obj [("Err", ← compJ v)])])
  | .lit h _ | .mixed h _ _ => throw s!"malformed `{h}` value"
termination_by v => sizeOf v
decreasing_by
  all_goals first
    | (simp_wf; have := List.sizeOf_lt_of_mem ‹_›; simp_all; omega)
    | (simp_wf; omega)

/-- The head of a value. -/
def Val.head : Val → String
  | .lit h _ | .mixed h _ _ => h

/-- An invocation argument: core when its head is a core argument (`WastArg`). -/
def argJ (v : Val) : LowerM Json :=
  if v.head ∈ coreArgHeads then coreJ false v
  else if v.head ∈ compHeads then compJ v
  else throw "expected a [type].const expression"

/-- An expected result (`WastRet`). -/
def retJ (v : Val) : LowerM Json :=
  if v.head ∈ coreRetHeads then coreJ true v
  else if v.head ∈ compHeads then compJ v
  else throw "expected a [type].const expression"

/-! ## Commands -/

/-- Module encoders: the `parse` subcommand's text-to-binary function. -/
structure Encoder where
  /-- Encode a text module `(module $id? field*)` (or component), given its S-expression
  and its source text (which keeps the annotations the S-expression omits). -/
  text : ModKind → SExpEncoding.SExp → String → Except String ByteArray
  /-- Parse and encode the text of a quoted module (`QuoteWat::encode`). -/
  quoted : ByteArray → Except String ByteArray

/-- The state of the conversion: the files emitted so far. -/
structure LowerState where
  /-- The number of modules emitted so far (`JsonBuilder::files`). -/
  count : Nat := 0
  files : Array (String × ByteArray) := #[]

abbrev CmdM := StateT LowerState (Except String)

/-- Options: the file stem of emitted modules and the line table of the source. -/
structure LowerCtx where
  stem : String
  /-- The UTF-8 source (for module source slices). -/
  source : ByteArray
  lines : Array Nat
  enc : Encoder

/-- The text of a quoted module (`QuoteWat::to_test`): the strings, each followed by a
space; a component is wrapped in `(component` … `)`. -/
def quoteText (k : ModKind) (ss : List (List UInt8)) : ByteArray :=
  let body : List UInt8 := ss.flatMap (· ++ [32])
  match k with
  | .core => ⟨body.toArray⟩
  | .component => ⟨("(component".toUTF8.toList ++ body ++ [41]).toArray⟩

/-- Emit a module's file (`emit_file`): its name, `module_type`, and `binary_filename`. -/
def emitFile (c : LowerCtx) (m : QuoteWat) (src : String) (malformed : Bool) :
    CmdM (List (String × Json)) := do
  let n := (← get).count
  modify fun s => { s with count := n + 1 }
  let fname (ext : String) := s!"{c.stem}.{n}.{ext}"
  match m with
  | .wat k id b =>
    let bytes ← match b with
      | .binary ss => pure (⟨(ss.flatMap fun x => x).toArray⟩ : ByteArray)
      | .fields _ => liftM (c.enc.text k (QuoteWat.wat k id b).toSExp src)
    modify fun s => { s with files := s.files.push (fname "wasm", bytes) }
    pure [("filename", .str (fname "wasm")), ("module_type", .str "binary")]
  | .quote k ss =>
    let text := quoteText k ss
    modify fun s => { s with files := s.files.push (fname "wat", text) }
    let base := [("filename", .str (fname "wat")), ("module_type", .str "text")]
    if malformed then pure base
    else match c.enc.quoted text with
      | .ok bytes =>
        modify fun s => { s with files := s.files.push (fname "wasm", bytes) }
        pure (base ++ [("binary_filename", .str (fname "wasm"))])
      | .error _ => pure base
where
  liftM {α : Type} (e : Except String α) : CmdM α := match e with
    | .ok a => pure a
    | .error msg => throw msg

/-- The module name of an identifier. -/
def nameField (key : String) : Option String → List (String × Json)
  | none => []
  | some n => [(key, .str n)]

def liftL {α : Type} (e : LowerM α) : CmdM α := match e with
  | .ok a => pure a
  | .error msg => throw msg

/-- An action (`Action`). -/
def actionJ : Exec → LowerM Json
  | .invoke i => do
    let field ← strJ i.name
    let args ← i.args.mapM argJ
    pure (.obj ([("type", .str "invoke")] ++ nameField "module" i.module ++
      [("field", .str field), ("args", .arr args)]))
  | .get m n => do
    let field ← strJ n
    pure (.obj ([("type", .str "get")] ++ nameField "module" m ++ [("field", .str field)]))
  | .wat _ => throw "unsupported `action` found using a module"

/-! ### Lines

`wast` reports the line of a directive's span, which is the span of a keyword: the module
keyword of a module (the `quote` keyword of a quoted one), the keyword of an invocation or
`get`, otherwise the directive's own keyword. -/

/-- The children of a positioned list. -/
def PNode.children : PNode → List PNode
  | .list _ _ xs => xs
  | .atom .. => []

/-- The span of a module (`QuoteWat::span`): `quote` keyword if quoted, else the head. -/
def modPos (p : PNode) : Nat :=
  match p.children with
  | _ :: .atom q (.sym "quote") :: _ => q
  | h :: _ => h.pos
  | [] => p.pos

/-- The span of an `exec`: the module span or the head keyword. -/
def execPos (p : PNode) : Nat :=
  match p.children with
  | .atom _ (.sym "module") :: _ | .atom _ (.sym "component") :: _ => modPos p
  | h :: _ => h.pos
  | [] => p.pos

/-- The position whose line a directive's command carries. -/
def directivePos (p : PNode) : Nat :=
  match p.children with
  | .atom _ (.sym "module") :: _ | .atom _ (.sym "component") :: _ => modPos p
  | .atom _ (.sym k) :: m :: _ =>
    if k ∈ ["assert_malformed", "assert_malformed_custom", "assert_invalid",
        "assert_invalid_custom", "assert_unlinkable"] then modPos m
    else if k ∈ ["assert_trap", "assert_return"] then execPos m
    else p.children.head!.pos
  | h :: _ => h.pos
  | [] => p.pos

def lineOfDirective (c : LowerCtx) (p : PNode) : Nat := lineOf c.lines (directivePos p)

/-- The command of a directive other than `thread`. -/
def commandBase (c : LowerCtx) : Directive → PNode → CmdM Json
  | d, p => do
    let line : Json := .num (lineOfDirective c p)
    let hd (t : String) : List (String × Json) := [("type", .str t), ("line", line)]
    match d with
    | .module m =>
      let name := match m with | .wat _ id _ => id | .quote .. => none
      let file ← emitFile c m (p.slice c.source) false
      pure (.obj (hd "module" ++ nameField "name" name ++ file))
    | .moduleDefinition k id b =>
      let file ← emitFile c (.wat k id b) (p.slice c.source) false
      pure (.obj (hd "module_definition" ++ nameField "name" id ++ file))
    | .moduleInstance _ i m =>
      pure (.obj (hd "module_instance" ++ nameField "instance" i ++ nameField "module" m))
    | .assertMalformed m s => modCmd "assert_malformed" m s true line (child1 p)
    | .assertMalformedCustom m s => modCmd "assert_malformed_custom" m s true line (child1 p)
    | .assertInvalid m s => modCmd "assert_invalid" m s false line (child1 p)
    | .assertInvalidCustom m s => modCmd "assert_invalid_custom" m s false line (child1 p)
    | .assertUnlinkable m s => modCmd "assert_unlinkable" m s false line (child1 p)
    | .register n m => do
      let n ← liftL (strJ n)
      pure (.obj (hd "register" ++ nameField "name" m ++ [("as", .str n)]))
    | .invoke i => do
      let a ← liftL (actionJ (.invoke i))
      pure (.obj (hd "action" ++ [("action", a)]))
    | .assertTrap (.wat m) s => modCmd "assert_uninstantiable" m s false line (child1 p)
    | .assertTrap e s => do
      let a ← liftL (actionJ e)
      let s ← liftL (strJ s)
      pure (.obj (hd "assert_trap" ++ [("action", a), ("text", .str s)]))
    | .assertReturn e rs => do
      let a ← liftL (actionJ e)
      let js ← liftL (rs.mapM retJ)
      pure (.obj (hd "assert_return" ++ [("action", a), ("expected", .arr js)]))
    | .assertExhaustion i s => do
      let a ← liftL (actionJ (.invoke i))
      let s ← liftL (strJ s)
      pure (.obj (hd "assert_exhaustion" ++ [("action", a), ("text", .str s)]))
    | .assertException e => do
      let a ← liftL (actionJ e)
      pure (.obj (hd "assert_exception" ++ [("action", a)]))
    | .assertSuspension e s => do
      let a ← liftL (actionJ e)
      let s ← liftL (strJ s)
      pure (.obj (hd "assert_suspension" ++ [("action", a), ("text", .str s)]))
    | .thread .. => throw "internal: nested thread"
    | .wait n => pure (.obj (hd "wait" ++ [("thread", .str n)]))
where
  child1 (p : PNode) : PNode := p.children.getD 1 p
  modCmd (t : String) (m : QuoteWat) (s : List UInt8) (malformed : Bool) (line : Json)
      (mp : PNode) : CmdM Json := do
    let file ← emitFile c m (mp.slice c.source) malformed
    let s ← liftL (strJ s)
    pure (.obj ([("type", .str t), ("line", line)] ++ file ++ [("text", .str s)]))

/-- The command of a directive (`JsonBuilder::directive`); `p` is its positioned tree. -/
def commandJ (c : LowerCtx) : Directive → PNode → CmdM Json
  | .thread n sh ds, p => do
    let line : Json := .num (lineOfDirective c p)
    let kids := p.children.drop (if sh.isSome then 3 else 2)
    let cmds ← (ds.zip kids).attach.mapM fun ⟨(d, q), h⟩ =>
      have : sizeOf d < 1 + sizeOf n + sizeOf sh + sizeOf ds := by
        have := List.sizeOf_lt_of_mem (List.of_mem_zip h).1
        omega
      commandJ c d q
    pure (.obj ([("type", .str "thread"), ("line", line), ("name", .str n)] ++
      nameField "shared_module" sh ++ [("commands", .arr cmds)]))
  | d, p => commandBase c d p
termination_by d => sizeOf d

/-- The JSON document of a script and its auxiliary files. -/
def scriptJson (c : LowerCtx) (source : String) (s : Script) (ps : List PNode) :
    Except String (Json × Array (String × ByteArray)) := do
  let ds := match s with
    | .directives ds => ds.zip ps
    | .inline xs =>
      -- the whole file is one module (its span: the start of the file)
      let p : PNode := .list 0 (c.source.size - 1) (.atom 0 (.sym "module") :: ps)
      [(.module (.wat .core none (.fields xs)), p)]
  if let .inline [] := s then throw "expected at least one module field"
  let (cmds, st) ← (ds.mapM fun (d, p) => commandJ c d p).run {}
  pure (.obj [("source_filename", .str source), ("commands", .arr cmds)], st.files)

/-- The file stem (`Path::file_stem`): the last path component without its last extension
(a leading dot does not start an extension). -/
def fileStem (path : String) : String :=
  let base := (path.splitOn "/").getLast!
  match (base.splitOn ".") with
  | [] | [_] => base
  | parts =>
    if base.startsWith "." && parts.length == 2 then base
    else ".".intercalate parts.dropLast

end Silmaril.Wasm.Tools.Wast
