module

public import Silmaril.Wasm.Tools.Meta.Leb.Defs

/-!
# The payload structure of a Wasm binary, as wasmparser's `Parser` sees it

`wasm-tools demangle`, `metadata show` and `metadata add` walk a binary with wasmparser's
`Parser::parse_all` (wasmparser 0.262, the parser of `wasm-tools 1.262.0`) and rebuild it from the
sections it reports. This module models that walk:

* `parseUnit` reads a header (module `00 61 73 6d 01 00 00 00`, component
  `00 61 73 6d 0d 00 01 00`) and then the sections. Every section is an id byte below `0x80`, a
  `var_u32` size and that many bytes. In a component, sections 1 (core module) and 4 (component)
  hold a nested unit, which is parsed in turn and must fill its section exactly.
* The checks the parser makes on top of the framing (`checkModuleSec`, `checkComponentSec`):
  custom section names (a `var_u32` length up to 100 000 and UTF-8), the order of module
  sections, the item counts that start vector sections, the single item of the start and data
  count sections, the function bodies of the code section (count, sizes, no trailing bytes),
  the function/code and data-count/data counts, at most one component start section, and the
  "expected section, got wasm magic number" case. Unknown section ids are accepted, as the
  parser does (the validator, not the parser, rejects them).
* What the parser does **not** check is not checked here either: section contents beyond the
  first count, and validity.

A parsed unit keeps the size field of each section as written (`Sec.size`), so the input is
exactly the concatenation of its parts (`parseUnit_sound` in `Silmaril.Wasm.Tools.Meta.Frame.Thms`).
Errors carry wasmparser's message (not the byte offset).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- The two encodings of a Wasm binary. -/
inductive Enc where
  | module
  | component
  deriving DecidableEq, Repr, Inhabited

/-- `\0asm`. -/
def magic : List UInt8 := [0x00, 0x61, 0x73, 0x6d]

/-- The preamble of an encoding: the magic number and the version word. -/
def Enc.header : Enc → List UInt8
  | .module => magic ++ [0x01, 0x00, 0x00, 0x00]
  | .component => magic ++ [0x0d, 0x00, 0x01, 0x00]

/-- A section as written: its id, the bytes of its size field, and its contents. -/
structure Sec where
  id : UInt8
  size : List UInt8
  body : List UInt8
  deriving Repr, Inhabited, DecidableEq

/-- The bytes of a section, as they were read. -/
def Sec.bytes (s : Sec) : List UInt8 := s.id :: (s.size ++ s.body)

/-- A section with a minimal size field (wasm-encoder's `RawSection`). -/
def rawSec (id : UInt8) (body : List UInt8) : List UInt8 := id :: (encU32 body.length ++ body)

/-- An item of a unit: a section, or (in a component) a nested core module (`id = 1`) or
component (`id = 4`) section with its parsed contents. -/
inductive Item where
  | sec (s : Sec)
  | nest (id : UInt8) (size : List UInt8) (enc : Enc) (items : List Item)
  deriving Repr, Inhabited

mutual
/-- The bytes of an item, as they were read. -/
def Item.bytes : Item → List UInt8
  | .sec s => s.bytes
  | .nest id size enc items => id :: (size ++ (enc.header ++ Item.listBytes items))
/-- The bytes of a list of items. -/
def Item.listBytes : List Item → List UInt8
  | [] => []
  | i :: is => i.bytes ++ Item.listBytes is
end

/-- The number of bytes of the `var_u32` at the front of a list: up to and including the first
byte without the continuation bit. -/
def lebLen : List UInt8 → Nat
  | [] => 0
  | b :: bs => if b.toNat < 128 then 1 else lebLen bs + 1

/-- wasmparser's `read_string`/`skip_string` framing: a `var_u32` length at most 100 000 and
that many bytes; the string's bytes and the rest. -/
def readStrBytes (bs : List UInt8) : Except String (List UInt8 × List UInt8) := do
  let (n, r) ← readU32 bs
  if 100000 < n then throw "string size out of bounds"
  let s := r.take n
  if s.length < n then throw errEof
  pure (s, r.drop n)

/-- UTF-8 validity of a byte string (Rust's `str::from_utf8`). -/
def utf8Ok (s : List UInt8) : Bool := (ByteArray.mk s.toArray).validateUTF8

/-- wasmparser's `read_string`: `readStrBytes` and UTF-8 validity. -/
def readStr (bs : List UInt8) : Except String (List UInt8 × List UInt8) := do
  let (s, r) ← readStrBytes bs
  if !utf8Ok s then throw "malformed UTF-8 encoding"
  pure (s, r)

/-- wasmparser's `read_unlimited_string` (the names of name maps): no length limit. -/
def readUStr (bs : List UInt8) : Except String (List UInt8 × List UInt8) := do
  let (n, r) ← readU32 bs
  let s := r.take n
  if s.length < n then throw errEof
  if !utf8Ok s then throw "malformed UTF-8 encoding"
  pure (s, r.drop n)

/-- The name and the data of a custom section's contents (`CustomSectionReader::new`). -/
def customOf (body : List UInt8) : Except String (List UInt8 × List UInt8) := readStr body

/-- The counts the parser keeps while reading a module (`SectionCounts`) and the order of the
last known section, plus whether a component start section was seen. -/
structure PState where
  order : Nat := 0
  funcs : Option Nat := none
  codes : Option Nat := none
  dataCount : Option Nat := none
  datas : Option Nat := none
  start : Bool := false
  deriving Repr, Inhabited

/-- wasmparser's `Order` of a module section id (`none` for custom and unknown ids). -/
def moduleOrder : Nat → Option Nat
  | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4 | 5 => some 5 | 13 => some 6
  | 6 => some 7 | 7 => some 8 | 8 => some 9 | 9 => some 10 | 12 => some 11 | 10 => some 12
  | 11 => some 13 | _ => none

/-- `check_function_code_counts`. -/
def checkFuncCode (st : PState) : Except String Unit :=
  match st.funcs, st.codes with
  | some n, some m => if n != m then throw "function and code section have inconsistent lengths"
      else pure ()
  | some n, none => if 0 < n then
      throw "function section has non-zero count but code section is absent" else pure ()
  | none, some m => if 0 < m then
      throw "function section is absent but code section has non-zero count" else pure ()
  | none, none => pure ()

/-- `check_data_count`. -/
def checkDataCount (st : PState) : Except String Unit :=
  match st.dataCount, st.datas with
  | some n, some m => if n != m then throw "data count and data section have inconsistent lengths"
      else pure ()
  | some n, none => if 0 < n then throw "data count is non-zero but data section is absent"
      else pure ()
  | none, _ => pure ()

/-- `single_item` over a `var_u32`: the section holds exactly one `var_u32`. -/
def singleU32 (desc : String) (body : List UInt8) : Except String Nat := do
  let (n, r) ← readU32 body
  if !r.isEmpty then throw s!"unexpected content in the {desc} section"
  pure n

/-- The function bodies of a code section: `k` entries, each a `var_u32` size and that many
bytes, filling the section. -/
def codeBodies : Nat → List UInt8 → Except String Unit
  | 0, [] => pure ()
  | 0, _ :: _ => throw "trailing bytes at end of section"
  | k + 1, bs => do
    let (n, r) ← readU32 bs
    let b := r.take n
    if b.length < n then throw errEof
    codeBodies k (r.drop n)

/-- The checks of `Parser::parse_reader` on one section of a module. -/
def checkModuleSec (st : PState) (id : Nat) (body : List UInt8) : Except String PState := do
  if id == 0 then
    let _ ← customOf body
    return st
  match moduleOrder id with
  | none => pure st
  | some o =>
    if o ≤ st.order then throw "section out of order"
    let st := { st with order := o }
    if id == 8 then
      let _ ← singleU32 "start" body
      pure st
    else if id == 12 then
      let n ← singleU32 "data count" body
      pure { st with dataCount := some n }
    else if id == 10 then
      let (n, r) ← readU32 body
      let st := { st with codes := some n }
      checkFuncCode st
      codeBodies n r
      pure st
    else
      let (n, _) ← readU32 body
      if id == 3 then pure { st with funcs := some n }
      else if id == 11 then
        let st := { st with datas := some n }
        checkDataCount st
        pure st
      else pure st

/-- `ComponentStartFunction::from_reader` as a single item: function index, at most 1000
argument indices, a result count at most 1000. -/
def readCompStart (body : List UInt8) : Except String Unit := do
  let (_, r) ← readU32 body
  let (k, r) ← readU32 r
  if 1000 < k then throw "start function arguments size is out of bounds"
  let r ← (List.range k).foldlM (fun r _ => do let (_, r) ← readU32 r; pure r) r
  let (m, r) ← readU32 r
  if 1000 < m then throw "start function results size is out of bounds"
  if !r.isEmpty then throw "unexpected content in the component start section"

/-- The checks of `Parser::parse_reader` on one (non-nested) section of a component. -/
def checkComponentSec (st : PState) (id : Nat) (body : List UInt8) : Except String PState := do
  if id == 0 then
    let _ ← customOf body
    return st
  if id == 9 then
    if st.start then throw "component cannot have more than one start function"
    readCompStart body
    return { st with start := true }
  if id ∈ [2, 3, 5, 6, 7, 8, 10, 11] then
    let _ ← readU32 body
  pure st

/-- The header of a unit: the encoding its version word names, checked against `expect`. -/
def readHeader (expect : Option Enc) (bs : List UInt8) : Except String (Enc × List UInt8) := do
  let m := bs.take 4
  if m.length < 4 then throw errEof
  if m != magic then throw "magic header not detected: bad magic number"
  let v := (bs.drop 4).take 4
  if v.length < 4 then throw errEof
  let rest := bs.drop 8
  if v == [0x01, 0x00, 0x00, 0x00] then
    if expect == some .component then throw "expected a version header for a component"
    pure (.module, rest)
  else if v == [0x0d, 0x00, 0x01, 0x00] then
    if expect == some .module then throw "expected a version header for a module"
    pure (.component, rest)
  else throw "unknown binary version"

/-- The framing of one section after its id byte: the size field as written, the contents and
the rest of the unit. Also the parser's two checks before the size: the id must not start the
magic number (a concatenated second binary) and must be below `0x80`. -/
def readSec (id : UInt8) (bs : List UInt8) :
    Except String (List UInt8 × List UInt8 × List UInt8) :=
  if (id :: bs).take 4 == magic then .error "expected section, got wasm magic number"
  else if 128 ≤ id.toNat then .error "malformed section id"
  else match readU32 bs with
    | .error e => .error e
    | .ok (n, r) =>
      if (r.take n).length < n then .error errEof
      else .ok (bs.take (lebLen bs), r.take n, r.drop n)

/-- The checks on one non-nested section. -/
def checkSec : Enc → PState → Nat → List UInt8 → Except String PState
  | .module => checkModuleSec
  | .component => checkComponentSec

/-- The checks at the end of a unit. -/
def checkEnd : Enc → PState → Except String Unit
  | .module, st => do checkFuncCode st; checkDataCount st
  | .component, _ => pure ()

/-- Whether a section of a unit of encoding `enc` holds a nested unit. -/
def isNest (enc : Enc) (id : UInt8) : Bool := enc == .component && (id == 1 || id == 4)

/-- The encoding a nested section must hold. -/
def nestEnc (id : UInt8) : Enc := if id == 1 then .module else .component

mutual
/-- The sections of a unit of encoding `enc`, after its header, to the end of `bs`. `fuel`
bounds the number of sections and the nesting depth (`bs.length + 1` suffices). -/
def parseSecs : Nat → Enc → PState → List UInt8 → Except String (List Item)
  | 0, _, _, _ => throw "nesting too deep"
  | _ + 1, enc, st, [] => do
    checkEnd enc st
    pure []
  | f + 1, enc, st, id :: bs => do
    let (size, body, rest) ← readSec id bs
    if isNest enc id then
      if 1073741824 < body.length then
        throw ((if id == 1 then "module" else "component") ++ " section is too large")
      let (enc', items) ← parseUnit f (some (nestEnc id)) body
      let is ← parseSecs f enc st rest
      pure (.nest id size enc' items :: is)
    else
      let st ← checkSec enc st id.toNat body
      let is ← parseSecs f enc st rest
      pure (.sec ⟨id, size, body⟩ :: is)
/-- A unit (module or component): header, then sections filling `bs`. -/
def parseUnit : Nat → Option Enc → List UInt8 → Except String (Enc × List Item)
  | 0, _, _ => throw "nesting too deep"
  | f + 1, expect, bs => do
    let (enc, rest) ← readHeader expect bs
    let items ← parseSecs f enc {} rest
    pure (enc, items)
end

/-- A whole binary, as `Parser::new(0).parse_all` walks it. -/
def parseBinary (bs : List UInt8) : Except String (Enc × List Item) :=
  parseUnit (bs.length + 2) none bs

end Silmaril.Wasm.Tools.Meta

end
