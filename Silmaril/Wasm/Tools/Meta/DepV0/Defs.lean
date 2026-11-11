module

public import Silmaril.Wasm.Tools.Meta.Inflate.Defs

/-!
# The `.dep-v0` custom section (cargo-auditable dependency lists)

wasm-metadata 0.262 (`Dependencies::parse_custom_section`) reads `.dep-v0` as a zlib stream of at
most 2 MiB (`MAX_DECOMPRESSED_SIZE`) holding UTF-8 JSON, deserialized by serde_json 1 into
auditable-serde 0.9's `VersionInfo` and validated; `metadata show` lists each package as
`dependency | NAME [VERSION]` and `--json` holds the re-serialization as a string. This module:

* `readDeps` = `Inflate.zlibInflate`, UTF-8, `parseJson` (RFC 8259 as serde_json reads it:
  no trailing commas or characters, no control characters in strings, `\u` escapes with
  surrogate pairs), `versionInfo` (the derived `Deserialize` of `VersionInfo`/`Package`,
  object or array form, unknown fields ignored, duplicate fields refused, defaults for `format`,
  `kind`, `dependencies`, `root`), `semverOk` (semver 1.0's `Version::from_str`), and the two
  validations of auditable-serde (`MultipleRoots`, `CyclicDependency` by Kahn's algorithm, as
  the `topological_sort` crate);
* `VersionInfo.toJson` = `serde_json::to_string(&VersionInfo)` (fields in declaration order,
  defaults skipped; semver prints a version as written, which `semverOk` checks).

`source` is a `&str` in auditable-serde (`#[serde(from = "&str")]`): serde_json can only lend a
string without escapes, so an escaped `source` is refused, as upstream.

Error messages: serde_json's texts without the `at line L column C` position (compared by
class in the tests).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.DepV0

/-- A JSON value; strings remember whether they had escapes (`borrowable`). -/
inductive J where
  | null
  | bool (b : Bool)
  /-- A number: its text, and whether it is an integer (no fraction or exponent). -/
  | num (text : String) (int : Bool)
  | str (s : String) (borrowable : Bool)
  | arr (xs : List J)
  | obj (kvs : List (String × J))
  deriving Inhabited, Repr

/-- The parser state: the input characters and the position. -/
abbrev P := StateT (Array Char × Nat) (Except String)

def peekC : P (Option Char) := do let (s, i) ← get; pure s[i]?
def advC : P Unit := modify fun (s, i) => (s, i + 1)

/-- The first position from `i` that is not JSON whitespace. -/
def skipWs (s : Array Char) (i : Nat) : Nat → Nat
  | 0 => i
  | f + 1 =>
    match s[i]? with
    | some ' ' | some '\n' | some '\r' | some '\t' => skipWs s (i + 1) f
    | _ => i

/-- Skip JSON whitespace. -/
def ws : P Unit := modify fun (s, i) => (s, skipWs s i (s.size - i))

/-- The number of characters left (the fuel of loops over the input). -/
def left : P Nat := do let (s, i) ← get; pure (s.size - i + 1)

/-- Expect a literal word. -/
def word (w : String) (v : J) : P J := do
  for c in w.toList do
    if (← peekC) != some c then throw "expected ident"
    advC
  pure v

/-- Four hexadecimal digits. -/
def hex4 : P Nat := do
  let mut n := 0
  for _ in [0:4] do
    let some c ← peekC | throw "EOF while parsing a string"
    let d ← if c.isDigit then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else throw "invalid escape"
    advC
    n := n * 16 + d
  pure n

/-- A string after its opening quote. -/
def strBody : Nat → String → Bool → P (String × Bool)
  | 0, _, _ => throw "EOF while parsing a string"
  | f + 1, acc, borrow => do
    let some c ← peekC | throw "EOF while parsing a string"
    advC
    if c == '"' then return (acc, borrow)
    if c.toNat < 0x20 then throw "control character (\\u0000-\\u001F) found while parsing a string"
    if c != '\\' then return ← strBody f (acc.push c) borrow
    let some e ← peekC | throw "EOF while parsing a string"
    advC
    let ch ← match e with
      | '"' => pure '"' | '\\' => pure '\\' | '/' => pure '/' | 'b' => pure '\x08'
      | 'f' => pure '\x0c' | 'n' => pure '\n' | 'r' => pure '\r' | 't' => pure '\t'
      | 'u' => do
        let n ← hex4
        if 0xD800 ≤ n && n < 0xDC00 then
          if (← peekC) != some '\\' then throw "unexpected end of hex escape"
          advC
          if (← peekC) != some 'u' then throw "unexpected end of hex escape"
          advC
          let m ← hex4
          if !(0xDC00 ≤ m && m < 0xE000) then throw "lone leading surrogate in hex escape"
          pure (Char.ofNat (0x10000 + (n - 0xD800) * 1024 + (m - 0xDC00)))
        else if 0xDC00 ≤ n && n < 0xE000 then throw "lone leading surrogate in hex escape"
        else pure (Char.ofNat n)
      | _ => throw "invalid escape"
    strBody f (acc.push ch) false

/-- A number (serde_json's grammar). -/
def number : P J := do
  let (s, i0) ← get
  let mut i := i0
  let mut int := true
  if s[i]? == some '-' then i := i + 1
  match s[i]? with
  | some '0' => i := i + 1
  | some c =>
    if '1' ≤ c && c ≤ '9' then
      while (s[i]?.map Char.isDigit).getD false do i := i + 1
    else throw "invalid number"
  | none => throw "EOF while parsing a value"
  if s[i]? == some '.' then
    int := false
    i := i + 1
    if !(s[i]?.map Char.isDigit).getD false then throw "invalid number"
    while (s[i]?.map Char.isDigit).getD false do i := i + 1
  if s[i]? == some 'e' || s[i]? == some 'E' then
    int := false
    i := i + 1
    if s[i]? == some '+' || s[i]? == some '-' then i := i + 1
    if !(s[i]?.map Char.isDigit).getD false then throw "invalid number"
    while (s[i]?.map Char.isDigit).getD false do i := i + 1
  set (s, i)
  pure (.num (String.ofList ((s.extract i0 i).toList)) int)

mutual
/-- A value; `d` bounds the nesting depth. -/
def value : Nat → P J
  | 0 => throw "recursion limit exceeded"
  | d + 1 => do
    ws
    let some c ← peekC | throw "EOF while parsing a value"
    match c with
    | 'n' => word "null" .null
    | 't' => word "true" (.bool true)
    | 'f' => word "false" (.bool false)
    | '"' => advC; let (s, b) ← strBody (← left) "" true; pure (.str s b)
    | '[' => advC; pure (.arr (← elems d (← left) true []))
    | '{' => advC; pure (.obj (← members d (← left) true []))
    | c => if c == '-' || c.isDigit then number else throw "expected value"
/-- Array elements after `[` (`k` bounds their number). -/
def elems (d : Nat) : Nat → Bool → List J → P (List J)
  | 0, _, _ => throw "EOF while parsing a list"
  | k + 1, first, acc => do
    ws
    if (← peekC) == some ']' then
      advC; return acc.reverse
    if !first then
      if (← peekC) != some ',' then throw "expected `,` or `]`"
      advC
      ws
      if (← peekC) == some ']' then throw "trailing comma"
    let v ← value d
    elems d k false (v :: acc)
/-- Object members after `{`. -/
def members (d : Nat) : Nat → Bool → List (String × J) → P (List (String × J))
  | 0, _, _ => throw "EOF while parsing an object"
  | k + 1, first, acc => do
    ws
    if (← peekC) == some '}' then
      advC; return acc.reverse
    if !first then
      if (← peekC) != some ',' then throw "expected `,` or `}`"
      advC
      ws
      if (← peekC) == some '}' then throw "trailing comma"
    if (← peekC) != some '"' then throw "key must be a string"
    advC
    let (key, _) ← strBody (← left) "" true
    ws
    if (← peekC) != some ':' then throw "expected `:`"
    advC
    let v ← value d
    members d k false ((key, v) :: acc)
end

/-- **`serde_json::from_str`** to a value: one value, then only whitespace. serde_json's
recursion limit is 128 nested arrays or objects. -/
def parseJson (s : String) : Except String J := do
  let (v, (cs, i)) ← (do let v ← value 129; ws; pure v).run (s.toList.toArray, 0)
  if i < cs.size then throw "trailing characters"
  pure v

/-! ## semver -/

/-- A numeric identifier: digits, no leading zero (unless `0`). -/
def numIdOk (s : String) : Bool :=
  !s.isEmpty && s.all Char.isDigit && (s == "0" || !s.startsWith "0") && s.length ≤ 20 &&
    s.toNat! < 2 ^ 64

/-- A dot-separated identifier list (`pre` checks numeric parts for leading zeros). -/
def idsOk (pre : Bool) (s : String) : Bool :=
  (s.splitOn ".").all fun p =>
    !p.isEmpty && p.all (fun c => c.isAlphanum || c == '-') &&
      (!pre || !p.all Char.isDigit || numIdOk p)

/-- **`semver::Version::from_str`** accepts `s`. -/
def semverOk (s : String) : Bool :=
  let (core, build) := match s.splitOn "+" with
    | [c] => (c, none)
    | c :: rest => (c, some ("+".intercalate rest))
    | [] => (s, none)
  let (nums, pre) := match core.splitOn "-" with
    | [c] => (c, none)
    | c :: rest => (c, some ("-".intercalate rest))
    | [] => (core, none)
  match nums.splitOn "." with
  | [a, b, c] =>
    numIdOk a && numIdOk b && numIdOk c && (pre.map (idsOk true)).getD true &&
      (build.map fun b => !b.contains '+' && idsOk false b).getD true
  | _ => false

/-! ## `VersionInfo` -/

/-- A package of the dependency tree. -/
structure Package where
  name : String
  version : String
  source : String
  build : Bool := false
  dependencies : List Nat := []
  root : Bool := false
  deriving Inhabited, Repr

/-- `VersionInfo`. -/
structure VersionInfo where
  packages : List Package
  format : Nat := 0
  deriving Inhabited, Repr

def typeName : J → String
  | .null => "null" | .bool _ => "boolean" | .num _ true => "integer" | .num _ false => "floating point"
  | .str .. => "string" | .arr _ => "sequence" | .obj _ => "map"

def asString (what : String) : J → Except String String
  | .str s _ => .ok s
  | v => .error ("invalid type: " ++ typeName v ++ ", expected " ++ what)

/-- An unsigned integer below `bound`. -/
def asUInt (what : String) (bound : Nat) : J → Except String Nat
  | .num t true =>
    if t.startsWith "-" then .error ("invalid value: integer `" ++ t ++ "`, expected " ++ what)
    else if t.toNat! < bound then .ok t.toNat!
    else .error ("invalid value: integer `" ++ t ++ "`, expected " ++ what)
  | v => .error ("invalid type: " ++ typeName v ++ ", expected " ++ what)

def asBool : J → Except String Bool
  | .bool b => .ok b
  | v => .error ("invalid type: " ++ typeName v ++ ", expected a boolean")

/-- `DependencyKind`: `"build"` or `"runtime"` (or the map form `{"build": null}`). -/
def asKind : J → Except String Bool
  | .str "build" _ => .ok true
  | .str "runtime" _ => .ok false
  | .obj [("build", .null)] => .ok true
  | .obj [("runtime", .null)] => .ok false
  | .str s _ => .error ("unknown variant `" ++ s ++ "`, expected `build` or `runtime`")
  | v => .error ("invalid type: " ++ typeName v ++ ", expected enum DependencyKind")

/-- The fields of a struct given as an object: refuses duplicates of known fields. -/
def fieldsOf (known : List String) (kvs : List (String × J)) : Except String (List (String × J)) := do
  let mut seen : List (String × J) := []
  for (k, v) in kvs do
    if k ∈ known then
      if seen.any (·.1 == k) then throw ("duplicate field `" ++ k ++ "`")
      seen := seen ++ [(k, v)]
  pure seen

def packageFields : List String := ["name", "version", "source", "kind", "dependencies", "root"]

/-- A `Package` from a value. -/
def package (v : J) : Except String Package := do
  let fs ← match v with
    | .obj kvs => fieldsOf packageFields kvs
    | .arr xs =>
      if 6 < xs.length then throw ("invalid length " ++ toString xs.length ++ ", expected struct Package with 6 elements")
      if xs.length < 3 then throw ("invalid length " ++ toString xs.length ++ ", expected struct Package with 6 elements")
      pure (packageFields.zip xs)
    | v => throw ("invalid type: " ++ typeName v ++ ", expected struct Package")
  let get (k : String) : Option J := fs.lookup k
  let some n := get "name" | throw "missing field `name`"
  let some ver := get "version" | throw "missing field `version`"
  let some src := get "source" | throw "missing field `source`"
  let name ← asString "a string" n
  let version ← asString "a SemVer version" ver
  if !semverOk version then throw ("unexpected character in version `" ++ version ++ "`")
  let source ← match src with
    | .str s true => pure s
    | .str s false => throw ("invalid type: string " ++ s.quote ++ ", expected a borrowed string")
    | v => throw ("invalid type: " ++ typeName v ++ ", expected a borrowed string")
  let build ← match get "kind" with
    | some k => asKind k
    | none => pure false
  let dependencies ← match get "dependencies" with
    | some (.arr xs) => xs.mapM (asUInt "usize" (2 ^ 64))
    | some v => throw ("invalid type: " ++ typeName v ++ ", expected a sequence")
    | none => pure []
  let root ← match get "root" with
    | some b => asBool b
    | none => pure false
  pure { name, version, source, build, dependencies, root }

/-- `RawVersionInfo` from a value. -/
def rawVersionInfo (v : J) : Except String VersionInfo := do
  let fs ← match v with
    | .obj kvs => fieldsOf ["packages", "format"] kvs
    | .arr xs =>
      if xs.length < 1 || 2 < xs.length then
        throw ("invalid length " ++ toString xs.length ++ ", expected struct RawVersionInfo with 2 elements")
      pure (["packages", "format"].zip xs)
    | v => throw ("invalid type: " ++ typeName v ++ ", expected struct RawVersionInfo")
  let some ps := fs.lookup "packages" | throw "missing field `packages`"
  let packages ← match ps with
    | .arr xs => xs.mapM package
    | v => throw ("invalid type: " ++ typeName v ++ ", expected a sequence")
  let format ← match fs.lookup "format" with
    | some f => asUInt "u32" (2 ^ 32) f
    | none => pure 0
  pure { packages, format }

/-- Whether the dependency graph (an edge from each dependency to its dependent) has a cycle:
Kahn's algorithm removes the nodes without predecessors until none is left. -/
def hasCycle (ps : List Package) : Bool := Id.run do
  let edges := (ps.zipIdx.flatMap fun (p, i) => p.dependencies.map (·, i)).eraseDups
  let nodes := (edges.flatMap fun (a, b) => [a, b]).eraseDups
  let mut alive := nodes
  let mut es := edges
  for _ in [0:nodes.length + 1] do
    let free := alive.filter fun n => !es.any (·.2 == n)
    if free.isEmpty then break
    alive := alive.filter (· ∉ free)
    es := es.filter fun (a, _) => a ∉ free
  return !alive.isEmpty

/-- auditable-serde's `TryFrom<RawVersionInfo>`. -/
def validate (v : VersionInfo) : Except String VersionInfo :=
  if 1 < (v.packages.filter (·.root)).length then .error "Multiple root packages specified in the input JSON"
  else if hasCycle v.packages then .error "The input JSON specifies a cyclic dependency graph"
  else .ok v

/-- serde_json's escaping of a string. -/
def jsonStr (s : String) : String :=
  let hex := "0123456789abcdef".toList
  "\"" ++ s.toList.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\"" | '\\' => acc ++ "\\\\" | '\n' => acc ++ "\\n" | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t" | '\x08' => acc ++ "\\b" | '\x0c' => acc ++ "\\f"
    | c => if c.toNat < 0x20 then acc ++ "\\u00" ++ String.ofList [hex[c.toNat / 16]!, hex[c.toNat % 16]!]
      else acc.push c) "" ++ "\""

/-- `serde_json::to_string(&Package)`. -/
def Package.toJson (p : Package) : String :=
  "{\"name\":" ++ jsonStr p.name ++ ",\"version\":" ++ jsonStr p.version ++ ",\"source\":" ++
    jsonStr p.source ++ (if p.build then ",\"kind\":\"build\"" else "") ++
    (if p.dependencies.isEmpty then "" else
      ",\"dependencies\":[" ++ ",".intercalate (p.dependencies.map toString) ++ "]") ++
    (if p.root then ",\"root\":true" else "") ++ "}"

/-- **`serde_json::to_string(&VersionInfo)`**. -/
def VersionInfo.toJson (v : VersionInfo) : String :=
  "{\"packages\":[" ++ ",".intercalate (v.packages.map Package.toJson) ++ "]" ++
    (if v.format == 0 then "" else ",\"format\":" ++ toString v.format) ++ "}"

/-- `MAX_DECOMPRESSED_SIZE`. -/
def maxSize : Nat := 2 * 1024 * 1024

/-- **`Dependencies::parse_custom_section`** on the section's data. -/
def readDeps (data : ByteArray) : Except String VersionInfo := do
  let some out ← Inflate.zlibInflate maxSize data
    | throw ("`.dep-v0` custom section decompresses to more than the " ++ toString maxSize ++ " byte limit")
  let some s := String.fromUTF8? out | throw "invalid utf-8 sequence"
  let j ← parseJson s
  validate (← rawVersionInfo j)

end Silmaril.Wasm.Tools.Meta.DepV0

end
