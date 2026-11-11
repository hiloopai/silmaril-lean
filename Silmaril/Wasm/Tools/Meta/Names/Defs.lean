module

public import Silmaril.Wasm.Tools.Meta.Frame.Defs

/-!
# The `name` and `component-name` custom sections

The name section of the Wasm appendix (with the extended-name-section subsections) and the
`component-name` section of the Component Model, as wasmparser 0.262 reads them and wasm-encoder
0.262 writes them (`wasm-tools 1.262.0`).

A section is a sequence of subsections `id:u7 size:var_u32 data`. Decoded subsections (`NSub`):

| id | module `name` | component `component-name` |
|---|---|---|
| 0 | module name (`read_string`, at most 100 000 bytes) | component name (unlimited) |
| 1, 4–9, 11 | name map (functions, types, tables, memories, globals, elements, data, tags) | — |
| 2, 3, 10, 12, 13 | indirect name map (locals, labels, fields, parameters, tag parameters) | — |
| 1 | — | a sort (`00 k` core, `k` component) and a name map |
| other | unknown (kept as raw bytes) | unknown |

A name map is `count (index name)*` with strictly increasing indices ("names out of order") and
UTF-8 names without a length limit, and nothing after the last entry; an indirect name map is
`count (index map)*` with strictly increasing indices, where the inner maps are delimited by
skipping (each inner name at most 100 000 bytes).

* `decodeNames`/`decodeCompNames`: the full decode (wasm-encoder's `RoundtripReencoder`
  iterates every map); `strict := true` rejects unknown subsections (what `wasm-tools demangle`
  does).
* `scanNames`/`scanCompNames`: the lazy read of wasm-metadata's `ModuleNames::from_bytes` and
  `ComponentNames::from_bytes` (only the subsection framing, the name subsection and the first
  count of each map are read); it returns the module or component name.
* `encNames`: wasm-encoder's `NameSection`/`ComponentNameSection` bytes of decoded subsections.

Quirk kept from upstream: a `component-name` subsection 1 with an unknown sort is re-encoded
without its sort bytes (wasmparser's `Unknown { ty: 1, data }` holds the bytes after the sort).

Theorems in `Silmaril.Wasm.Tools.Meta.Names.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- A name map: indices and (UTF-8) names. -/
abbrev NMap := List (Nat × List UInt8)

/-- A decoded subsection. -/
inductive NSub where
  /-- Subsection 0: the module (or component) name. -/
  | name (n : List UInt8)
  /-- A name map subsection; `pre` is the sort prefix of a component subsection 1 (empty in a
  module). -/
  | map (id : Nat) (pre : List UInt8) (m : NMap)
  /-- An indirect name map subsection. -/
  | ind (id : Nat) (m : List (Nat × NMap))
  /-- Any other subsection, as raw bytes. -/
  | raw (id : Nat) (data : List UInt8)
  deriving Repr, Inhabited, DecidableEq

/-- Module subsection ids holding a name map. -/
def mapIds : List Nat := [1, 4, 5, 6, 7, 8, 9, 11]
/-- Module subsection ids holding an indirect name map. -/
def indIds : List Nat := [2, 3, 10, 12, 13]

/-! ## Encoding (wasm-encoder) -/

/-- A string: its length and bytes. -/
def encStr (s : List UInt8) : List UInt8 := encU32 s.length ++ s

/-- The entries of a name map. -/
def encEntries : NMap → List UInt8
  | [] => []
  | (i, s) :: m => encU32 i ++ encStr s ++ encEntries m

/-- A name map. -/
def encMap (m : NMap) : List UInt8 := encU32 m.length ++ encEntries m

/-- The entries of an indirect name map. -/
def encIndEntries : List (Nat × NMap) → List UInt8
  | [] => []
  | (i, m) :: ms => encU32 i ++ encMap m ++ encIndEntries ms

/-- An indirect name map. -/
def encInd (ms : List (Nat × NMap)) : List UInt8 := encU32 ms.length ++ encIndEntries ms

/-- A subsection: id, size, data. -/
def encSub (id : Nat) (data : List UInt8) : List UInt8 := id.toUInt8 :: (encU32 data.length ++ data)

/-- The bytes of a decoded subsection. -/
def NSub.encode : NSub → List UInt8
  | .name n => encSub 0 (encStr n)
  | .map id pre m => encSub id (pre ++ encMap m)
  | .ind id ms => encSub id (encInd ms)
  | .raw id d => encSub id d

/-- The contents of a name section. -/
def encNames : List NSub → List UInt8
  | [] => []
  | s :: ss => s.encode ++ encNames ss

/-- A custom section with the given name and contents (wasm-encoder's `CustomSection`). -/
def customSec (name data : List UInt8) : List UInt8 := rawSec 0 (encStr name ++ data)

/-- `"name"`. -/
def nameName : List UInt8 := "name".toUTF8.toList
/-- `"component-name"`. -/
def compNameName : List UInt8 := "component-name".toUTF8.toList

/-! ## Decoding (wasmparser) -/

/-- Whether an index may follow `last` (strictly increasing). -/
def idxOk (last : Option Nat) (i : Nat) : Bool :=
  match last with
  | none => true
  | some p => p < i

/-- `k` entries of a name map, after the last index `last`. With `lim`, names are at most
100 000 bytes (the inner maps of an indirect map, which wasmparser delimits with
`skip_string`). -/
def readEntries (lim : Bool) : Nat → Option Nat → List UInt8 → Except String (NMap × List UInt8)
  | 0, _, bs => .ok ([], bs)
  | k + 1, last, bs =>
    match readU32 bs with
    | .error e => .error e
    | .ok (i, r) =>
      if !idxOk last i then .error "names out of order" else
      match (if lim then readStr r else readUStr r) with
      | .error e => .error e
      | .ok (s, r) =>
        match readEntries lim k (some i) r with
        | .error e => .error e
        | .ok (m, r) => .ok ((i, s) :: m, r)

/-- A name map filling `bs` (`NameMap` iterated to the end). -/
def readMap (bs : List UInt8) : Except String NMap :=
  match readU32 bs with
  | .error e => .error e
  | .ok (k, r) =>
    match readEntries false k none r with
    | .error e => .error e
    | .ok (m, []) => .ok m
    | .ok (_, _ :: _) => .error "section size mismatch: unexpected data at the end of the section"

/-- `k` entries of an indirect name map, after the last index `last`. wasmparser skips each
inner map (`skip_string`: names at most 100 000 bytes) and then reads it as a name map that
fills the skipped bytes; reading it in place with `lim` accepts and rejects the same inputs. -/
def readIndEntries : Nat → Option Nat → List UInt8 → Except String (List (Nat × NMap) × List UInt8)
  | 0, _, bs => .ok ([], bs)
  | k + 1, last, bs =>
    match readU32 bs with
    | .error e => .error e
    | .ok (i, r) =>
      if !idxOk last i then .error "indirect names out of order" else
      match readU32 r with
      | .error e => .error e
      | .ok (c, r) =>
        match readEntries true c none r with
        | .error e => .error e
        | .ok (m, r) =>
          match readIndEntries k (some i) r with
          | .error e => .error e
          | .ok (ms, r) => .ok ((i, m) :: ms, r)

/-- An indirect name map filling `bs`. -/
def readInd (bs : List UInt8) : Except String (List (Nat × NMap)) :=
  match readU32 bs with
  | .error e => .error e
  | .ok (k, r) =>
    match readIndEntries k none r with
    | .error e => .error e
    | .ok (ms, []) => .ok ms
    | .ok (_, _ :: _) => .error "section size mismatch: unexpected data at the end of the section"

/-- A module or component name subsection: a string and nothing after it. -/
def readNameSub (limited : Bool) (data : List UInt8) : Except String (List UInt8) :=
  match (if limited then readStr data else readUStr data) with
  | .error e => .error e
  | .ok (s, []) => .ok s
  | .ok (_, _ :: _) => .error "trailing data at the end of a name"

/-- A subsection of the module `name` section, fully decoded. -/
def decodeModSub (strict : Bool) (id : Nat) (data : List UInt8) : Except String NSub :=
  if id == 0 then (readNameSub true data).map .name
  else if id ∈ mapIds then (readMap data).map (.map id [])
  else if id ∈ indIds then (readInd data).map (.ind id)
  else if strict then .error "unknown name section"
  else .ok (.raw id data)

/-- The sort of a `component-name` subsection 1: the sort bytes, if known, and the rest. -/
def compSort (data : List UInt8) : Except String (Option (List UInt8) × List UInt8) :=
  match data with
  | [] => .error errEof
  | 0 :: [] => .error errEof
  | 0 :: k :: r =>
    if k.toNat ∈ [0, 1, 2, 3, 4, 0x10, 0x11, 0x12] then .ok (some [0, k], r) else .ok (none, r)
  | k :: r => if k.toNat ∈ [1, 2, 3, 4, 5] then .ok (some [k], r) else .ok (none, r)

/-- A subsection of the `component-name` section, fully decoded. -/
def decodeCompSub (id : Nat) (data : List UInt8) : Except String NSub :=
  if id == 0 then (readNameSub false data).map .name
  else if id == 1 then
    match compSort data with
    | .error e => .error e
    | .ok (some pre, r) => (readMap r).map (.map 1 pre)
    | .ok (none, r) => .ok (.raw 1 r)
  else .ok (.raw id data)

/-- The subsections of a name section (`Subsections`): `id:u7`, a size, that many bytes, each
decoded by `dec`. `fuel` bounds the number of subsections. -/
def readSubs (dec : Nat → List UInt8 → Except String NSub) :
    Nat → List UInt8 → Except String (List NSub)
  | _, [] => .ok []
  | 0, _ :: _ => .error "too many subsections"
  | f + 1, id :: bs =>
    if 128 ≤ id.toNat then .error "invalid u7" else
    match readU32 bs with
    | .error e => .error e
    | .ok (n, r) =>
      if (r.take n).length < n then .error errEof else
      match dec id.toNat (r.take n) with
      | .error e => .error e
      | .ok s =>
        match readSubs dec f (r.drop n) with
        | .error e => .error e
        | .ok ss => .ok (s :: ss)

/-- The module `name` section, fully decoded. -/
def decodeNames (strict : Bool) (bs : List UInt8) : Except String (List NSub) :=
  readSubs (decodeModSub strict) bs.length bs

/-- The `component-name` section, fully decoded. -/
def decodeCompNames (bs : List UInt8) : Except String (List NSub) :=
  readSubs decodeCompSub bs.length bs

/-! ## The lazy read of wasm-metadata -/

/-- What `ModuleNames::from_bytes` reads of one module subsection: the name of subsection 0,
the count of a map (not the entries). -/
def scanModSub (id : Nat) (data : List UInt8) : Except String NSub :=
  if id == 0 then (readNameSub true data).map .name
  else if id ∈ mapIds ∨ id ∈ indIds then (readU32 data).map fun _ => .raw id data
  else .ok (.raw id data)

/-- What `ComponentNames::from_bytes` reads of one component subsection. -/
def scanCompSub (id : Nat) (data : List UInt8) : Except String NSub :=
  if id == 0 then (readNameSub false data).map .name
  else if id == 1 then
    match compSort data with
    | .error e => .error e
    | .ok (some _, r) => (readU32 r).map fun _ => .raw 1 data
    | .ok (none, _) => .ok (.raw 1 data)
  else .ok (.raw id data)

/-- The last name subsection's name (`from_bytes` keeps the last). -/
def lastName : List NSub → Option (List UInt8)
  | [] => none
  | .name n :: ss => (lastName ss).getD n |> some
  | _ :: ss => lastName ss

/-- `ModuleNames::from_bytes(..).get_name()`. -/
def scanNames (bs : List UInt8) : Except String (Option (List UInt8)) :=
  (readSubs scanModSub bs.length bs).map lastName

/-- `ComponentNames::from_bytes(..).get_name()`. -/
def scanCompNames (bs : List UInt8) : Except String (Option (List UInt8)) :=
  (readSubs scanCompSub bs.length bs).map lastName

end Silmaril.Wasm.Tools.Meta

end
