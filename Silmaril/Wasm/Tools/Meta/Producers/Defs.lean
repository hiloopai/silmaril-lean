module

public import Silmaril.Wasm.Tools.Meta.Names.Defs

/-!
# The `producers` custom section

The producers section of the tool conventions, as wasmparser 0.262 reads it, wasm-encoder 0.262
writes it and wasm-metadata 0.262 (`Producers`, an `IndexMap<String, IndexMap<String, String>>`)
keeps it:

* contents: `count (field values)*`, a field name `language`, `sdk` or `processed-by` (other
  names are an error), values `count (name version)*` with names and versions at most 100 000
  bytes (they are skipped first) and UTF-8; nothing after the last field;
* `Producers`: fields in first-insertion order, each with its values in first-insertion order; a
  repeated field or value name replaces the earlier entry in place (`IndexMap::insert`);
* `Producers.add` and `Producers.merge` (`Producers::add`, `merge`: values of the other take precedence);
* `encProducers`: the bytes of the custom section.

`readProducers` is the full read (`Producers::from_bytes`); `producersCountOk` is the check
`KnownCustom::Producers` makes before (only the field count), without which the section is not
treated as a producers section at all. Theorems: `Silmaril.Wasm.Tools.Meta.Producers.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- An ordered map with `IndexMap::insert` semantics. -/
abbrev OMap (α : Type) := List (String × α)

/-- `IndexMap::insert`: replace in place, or append. -/
def OMap.insert {α : Type} : OMap α → String → α → OMap α
  | [], k, v => [(k, v)]
  | (k', v') :: m, k, v => if k' == k then (k, v) :: m else (k', v') :: OMap.insert m k v

/-- The producers: fields and their name/version values. -/
abbrev Producers := OMap (OMap String)

/-- `Producers::add`. -/
def Producers.add (p : Producers) (field name version : String) : Producers :=
  match p.lookup field with
  | some vals => p.insert field (vals.insert name version)
  | none => p ++ [(field, [(name, version)])]

/-- `Producers::merge`: every value of `q`, in order, added to `p`. -/
def Producers.merge (p q : Producers) : Producers :=
  q.foldl (fun p (f, vals) => vals.foldl (fun p (n, v) => Producers.add p f n v) p) p

/-- A string from bytes known to be UTF-8. -/
def strOf (b : List UInt8) : String := String.fromUTF8! (ByteArray.mk b.toArray)

/-- `k` values of a field (`ProducersFieldValue`: two strings, at most 100 000 bytes since the
values are skipped first, and UTF-8). -/
def readValues : Nat → OMap String → List UInt8 → Except String (OMap String × List UInt8)
  | 0, acc, bs => .ok (acc, bs)
  | k + 1, acc, bs =>
    match readStr bs with
    | .error e => .error e
    | .ok (n, r) =>
      match readStr r with
      | .error e => .error e
      | .ok (v, r) => readValues k (acc.insert (strOf n) (strOf v)) r

/-- `k` fields. -/
def readFields : Nat → Producers → List UInt8 → Except String (Producers × List UInt8)
  | 0, acc, bs => .ok (acc, bs)
  | k + 1, acc, bs =>
    match readUStr bs with
    | .error e => .error e
    | .ok (n, r) =>
      let name := strOf n
      if !(name == "language" || name == "sdk" || name == "processed-by") then
        .error ("invalid producers field name: `" ++ name ++ "`") else
      match readU32 r with
      | .error e => .error e
      | .ok (c, r) =>
        match readValues c [] r with
        | .error e => .error e
        | .ok (vals, r) => readFields k (acc.insert name vals) r

/-- `Producers::from_bytes`: the whole section contents. -/
def readProducers (bs : List UInt8) : Except String Producers :=
  match readU32 bs with
  | .error e => .error e
  | .ok (k, r) =>
    match readFields k [] r with
    | .error e => .error e
    | .ok (p, []) => .ok p
    | .ok (_, _ :: _) => .error "section size mismatch: unexpected data at the end of the section"

/-- `ProducersSectionReader::new` succeeds (the field count reads). -/
def producersCountOk (bs : List UInt8) : Bool := (readU32 bs).toBool

/-- The bytes of a string. -/
def sBytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- The values of a field. -/
def encValues (vals : OMap String) : List UInt8 :=
  encU32 vals.length ++ (vals.flatMap fun (n, v) => encStr (sBytes n) ++ encStr (sBytes v))

/-- The contents of a producers section. -/
def encProdBody (p : Producers) : List UInt8 :=
  encU32 p.length ++ (p.flatMap fun (f, vals) => encStr (sBytes f) ++ encValues vals)

/-- `"producers"`. -/
def producersName : List UInt8 := sBytes "producers"

/-- The custom section of producers (wasm-encoder's `ProducersSection`). -/
def encProducers (p : Producers) : List UInt8 := customSec producersName (encProdBody p)

end Silmaril.Wasm.Tools.Meta

end
