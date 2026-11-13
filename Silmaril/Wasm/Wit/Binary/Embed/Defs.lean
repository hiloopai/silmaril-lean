module

public import Silmaril.Wasm.Wit.Binary.Custom.Defs

/-!
# A world embedded in a core module

`wasm-tools component embed` (wit-component 0.263.0, `src/metadata.rs`,
`embed_component_metadata`) appends to a core module a custom section named
`component-type` whose contents are `encodeWorldType` of a world
(`Binary.Custom`); `wit-component` reads back every custom section whose name
starts with `component-type` (`metadata::decode`). This module is the core-module
side of that convention:

* `coreSections`: the sections of a core module (id and content window), after
  the magic and version; only the section framing is read;
* `customSections`: the custom sections (id 0) with their names and contents;
* `customSection`: the bytes of one custom section;
* `embedPayload`: append a `component-type` section holding a payload;
* `extractPayload`: the contents of the unique `component-type…` section;
* `extractWorldType`: `decodeWorldType` of that payload.

The framing is plain Wasm (`section ::= id:byte size:u32 contents`, `custom ::=
name bytes`); it is read with the parsers of `Silmaril.Parse.ByteParse`. Not proved:
that `extractPayload (embedPayload m b) = .ok b` (tested in
`tests/wasm-wit/differential.sh` against `wasm-tools component embed`).
Several `component-type` sections (which wit-component merges) are rejected.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Parse.ByteParse

/-- The magic number and version of a core module. -/
def coreHeader : List UInt8 := [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]

/-- The sections from offset `i` on: `(id, start, end)` of each section's contents. -/
def coreSectionsFrom (b : ByteArray) : Nat → Nat → Except String (List (UInt8 × Nat × Nat))
  | 0, _ => throw "too many sections"
  | fuel + 1, i =>
    if h : i < b.size then
      match (u32 : Parser Nat) b b.size (i + 1) with
      | Res.ok n j =>
        if j + n ≤ b.size then
          ((b[i], j, j + n) :: ·) <$> coreSectionsFrom b fuel (j + n)
        else throw s!"section at offset {i} exceeds the module"
      | Res.err _ => throw s!"malformed section size at offset {i + 1}"
    else pure []

/-- The sections of a core module. -/
def coreSections (b : ByteArray) : Except String (List (UInt8 × Nat × Nat)) :=
  if (b.extract 0 8).data.toList == coreHeader then coreSectionsFrom b b.size 8
  else throw "not a core module (magic or version)"

/-- The custom sections of a core module: name and contents. -/
def customSections (b : ByteArray) : Except String (List (String × ByteArray)) := do
  let ss ← coreSections b
  ss.filterMapM fun (id, s, e) =>
    if id = 0 then
      match (Silmaril.Parse.ByteParse.name : Parser String) b e s with
      | Res.ok n j => pure (some (n, b.extract j e))
      | Res.err _ => throw s!"malformed custom section name at offset {s}"
    else pure none

/-- The bytes of a custom section. -/
def customSection (name : String) (payload : ByteArray) : Option ByteArray := do
  let nm ← Enc.name name
  let body := nm ++ payload.data.toList
  let sz ← Enc.u32 body.length
  pure ⟨(0 :: sz ++ body).toArray⟩

/-- The name of the section (wit-component's `embed_component_metadata`). -/
def componentTypeSection : String := "component-type"

/-- `wasm-tools component embed` on an existing module: append the payload as a
`component-type` custom section. -/
def embedPayload (m payload : ByteArray) : Except String ByteArray := do
  let _ ← coreSections m
  match customSection componentTypeSection payload with
  | some s => pure (m ++ s)
  | none => throw "payload too large"

/-- The contents of the `component-type…` custom section of a core module. -/
def extractPayload (m : ByteArray) : Except String ByteArray := do
  let cs ← customSections m
  match cs.filter (·.1.startsWith componentTypeSection) with
  | [(_, d)] => pure d
  | [] => throw "no component-type custom section"
  | _ => throw "several component-type custom sections (merging is not supported)"

/-- The world a core module embeds. -/
def extractWorldType (m : ByteArray) : Except String (PackageName × String × World × StringEncoding) := do
  decodeWorldType (← extractPayload m)

end Silmaril.Wasm.Wit.Binary
