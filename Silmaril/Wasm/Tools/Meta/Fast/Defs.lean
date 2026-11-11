module

public import Silmaril.Wasm.Tools.Meta.Frame.Defs

/-!
# The payload walk over a `ByteArray`, with wasmparser's error offsets

`parseBinary` (`Silmaril.Wasm.Tools.Meta.Frame.Defs`) is the specification of wasmparser's payload
walk on a `List UInt8`. On a 3 MB binary the list alone costs about 100 MB, so the commands run
this module's `parseBinaryB` instead: the same walk over a `ByteArray`, where a section is a range
of the array (`SecB`) and nothing is copied.

`parseBinaryB` also reports errors as wasmparser does, with the byte offset of the failure
(`FErr`, printed `msg (at offset 0x…)` by `FErr.render`): the offsets of `BinaryReader`
(`read_var_u32`, `read_bytes`, `read_string`), of `Parser::parse_reader` (section start, size
field, end of unit) and of `delimited`/`single_item`. Where wasmparser reads past the end of a
section (the count and the function bodies of a code section are read from the whole remaining
input and only then checked against the section size, `delimited`), so does `parseBinaryB`, so the
first error found is the same as upstream's.

`ItemB.toItem` maps the result to the specification's items. The equivalence theorem
`parseBinaryB_spec` (`Silmaril.Wasm.Tools.Meta.FastCmd.Thms`) states that both walks succeed on the
same inputs with the same result:
`(parseBinaryB ba).toOption.map (itemsOf ba) = (parseBinary ba.data.toList).toOption`.
Error messages and offsets are not part of that statement; they are tested against the pinned
`wasm-tools` (`tools/wasm-tools/tests/meta-differential.sh`, the malformed-binary cases).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- An error with wasmparser's offset. -/
abbrev FErr := String × Nat

/-- `0x…` in lower-case hexadecimal (Rust's `{:x}` with the prefix). -/
def hexStr (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The offset of an error that has none (an anyhow error of a later stage, already
rendered). -/
def FErr.noOffset : Nat := 2 ^ 64

/-- An error without an offset. -/
def FErr.plain (msg : String) : FErr := (msg, FErr.noOffset)

/-- anyhow's rendering of a `BinaryReaderError`: `msg (at offset 0x…)`. -/
def FErr.render (e : FErr) : String :=
  if e.2 == FErr.noOffset then e.1 else e.1 ++ " (at offset " ++ hexStr e.2 ++ ")"

/-- A check run on each custom section, in stream order, when the section is reached (the
contents `[a, b)`): the work a consumer of wasmparser's payloads does before it asks for the next
payload. Used only to find the first error in stream order; `noHook` for the walk itself. -/
abbrev Hook := Bool → Nat → Nat → Except FErr Unit

/-- No check. -/
def noHook : Hook := fun _ _ _ => .ok ()

/-- The bytes of `ba` in `[i, j)`, as a list (the specification's view; equal to
`(ba.data.toList.drop i).take (j - i)`, `sl_eq` in the theorems). -/
def sl (ba : ByteArray) (i j : Nat) : List UInt8 := (ba.extract i j).toList

/-- The byte at `i` (`0` past the end). -/
@[inline] def byteAt (ba : ByteArray) (i : Nat) : UInt8 := ba.get! i

/-- The continuation bytes of a `var_u32` read at `pos`, below `lim` (`readU32Go`). -/
def rdU32Go (ba : ByteArray) (lim acc shift pos : Nat) : Except FErr (Nat × Nat) :=
  if h : pos < lim then
    let b := byteAt ba pos
    let acc' := acc + b.toNat % 128 * 2 ^ shift
    if 25 ≤ shift ∧ b.toNat / 2 ^ (32 - shift) ≠ 0 then
      .error (if 128 ≤ b.toNat then "invalid var_u32: integer representation too long"
        else "invalid var_u32: integer too large", pos)
    else if b.toNat < 128 then .ok (acc', pos + 1) else rdU32Go ba lim acc' (shift + 7) (pos + 1)
  else .error (errEof, pos)
termination_by lim - pos

/-- wasmparser's `read_var_u32` at `pos`, reading below `lim`: the value and the next position. -/
def rdU32 (ba : ByteArray) (lim pos : Nat) : Except FErr (Nat × Nat) :=
  if pos < lim then
    let b := byteAt ba pos
    if b.toNat < 128 then .ok (b.toNat, pos + 1) else rdU32Go ba lim (b.toNat % 128) 7 (pos + 1)
  else .error (errEof, pos)

/-- `read_bytes(n)` at `pos`: the end of the bytes. -/
def rdBytes (lim pos n : Nat) : Except FErr Nat :=
  if pos + n ≤ lim then .ok (pos + n) else .error (errEof, pos)

/-- UTF-8 validity of `[i, j)`. -/
def utf8OkB (ba : ByteArray) (i j : Nat) : Bool := (ba.extract i j).validateUTF8

/-- `read_string` at `pos` (below `lim`): the start and end of the string. `limited` is the
100 000-byte limit (`read_unlimited_string` has none). -/
def rdStr (ba : ByteArray) (lim pos : Nat) (limited : Bool := true) : Except FErr (Nat × Nat) := do
  let (n, p) ← rdU32 ba lim pos
  if limited && 100000 < n then throw ("string size out of bounds", p - 1)
  let e ← rdBytes lim p n
  if !utf8OkB ba p e then throw ("malformed UTF-8 encoding", e - 1)
  pure (p, e)

/-- A section as a range of the input: the position of its size field, of its contents and the
end of its contents. -/
structure SecB where
  id : UInt8
  sizeAt : Nat
  bodyAt : Nat
  bodyEnd : Nat
  deriving Repr, Inhabited

/-- An item of a unit, over the input array. -/
inductive ItemB where
  | sec (s : SecB)
  | nest (id : UInt8) (sizeAt bodyAt bodyEnd : Nat) (enc : Enc) (items : List ItemB)
  deriving Repr, Inhabited

/-- The specification's view of a section. -/
def SecB.toSec (ba : ByteArray) (s : SecB) : Sec := ⟨s.id, sl ba s.sizeAt s.bodyAt, sl ba s.bodyAt s.bodyEnd⟩

/-- The specification's view of an item. -/
def ItemB.toItem (ba : ByteArray) : ItemB → Item
  | .sec s => .sec (s.toSec ba)
  | .nest id sa bAt _ enc items => .nest id (sl ba sa bAt) enc (items.attach.map fun ⟨i, _⟩ => i.toItem ba)
termination_by i => i
decreasing_by simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ items›; omega

/-- `{:#x?}` of a byte slice (`[`, one `0x…,` per line indented by four spaces, `]`). -/
def debugHexBytes (bs : List UInt8) : String :=
  "[\n" ++ String.join (bs.map fun b => "    " ++ hexStr b.toNat ++ ",\n") ++ "]"

/-- `{:#10x}`: `0x…` right-aligned in ten columns. -/
def hex10 (n : Nat) : String :=
  let s := hexStr n
  "".pushn ' ' (10 - s.length) ++ s

/-- The little-endian `u32` at `i`. -/
def u32At (ba : ByteArray) (i : Nat) : Nat :=
  (byteAt ba i).toNat + 256 * (byteAt ba (i + 1)).toNat + 65536 * (byteAt ba (i + 2)).toNat +
    16777216 * (byteAt ba (i + 3)).toNat

/-- Whether the four bytes at `i` are the magic number. -/
def magicAt (ba : ByteArray) (i : Nat) : Bool :=
  byteAt ba i == 0 && byteAt ba (i + 1) == 0x61 && byteAt ba (i + 2) == 0x73 && byteAt ba (i + 3) == 0x6d

/-- The header of a unit at `pos` (`State::Header`): the encoding and the position after it. -/
def readHeaderB (ba : ByteArray) (expect : Option Enc) (lim pos : Nat) : Except FErr (Enc × Nat) := do
  if lim < pos + 4 then throw (errEof, pos)
  if !magicAt ba pos then
    throw ("magic header not detected: bad magic number - expected=" ++ debugHexBytes magic ++
      " actual=" ++ debugHexBytes (sl ba pos (pos + 4)), pos)
  if lim < pos + 8 then throw (errEof, pos + 4)
  let v := u32At ba (pos + 4)
  if v == 1 then
    if expect == some .component then throw ("expected a version header for a component", pos)
    pure (.module, pos + 8)
  else if v == 0x1000d then
    if expect == some .module then throw ("expected a version header for a module", pos)
    pure (.component, pos + 8)
  else throw ("unknown binary version: " ++ hex10 v, pos + 4)

/-- `check_function_code_counts` at offset `off`. -/
def checkFuncCodeB (st : PState) (off : Nat) : Except FErr Unit :=
  match checkFuncCode st with
  | .ok () => .ok ()
  | .error e => .error (e, off)

/-- `check_data_count` at offset `off`. -/
def checkDataCountB (st : PState) (off : Nat) : Except FErr Unit :=
  match checkDataCount st with
  | .ok () => .ok ()
  | .error e => .error (e, off)

/-- `single_item` over a `var_u32` in `[a, b)`. -/
def singleU32B (ba : ByteArray) (desc : String) (a b : Nat) : Except FErr Nat := do
  let (n, p) ← rdU32 ba b a
  if p != b then throw ("unexpected content in the " ++ desc ++ " section", p)
  pure n

/-- The function bodies of a code section (`State::FunctionBody`): `k` entries from `pos`, with
`len` bytes of the section left; reads go up to `lim` and are then checked against `len`
(`delimited`). The end of the section. -/
def codeBodiesB (ba : ByteArray) (lim : Nat) : Nat → Nat → Nat → Except FErr Nat
  | 0, pos, len => if len == 0 then .ok pos else .error ("trailing bytes at end of section", pos)
  | k + 1, pos, len => do
    let (n, q) ← rdU32 ba lim pos
    let e ← rdBytes lim q n
    if len < e - pos then throw (errEof, pos)
    codeBodiesB ba lim k e (len - (e - pos))

/-- `ComponentStartFunction::from_reader` as a single item over `[a, b)`. -/
def readCompStartB (ba : ByteArray) (a b : Nat) : Except FErr Unit := do
  let (_, p) ← rdU32 ba b a
  let (k, q) ← rdU32 ba b p
  if 1000 < k then throw ("start function arguments size is out of bounds", p)
  let r ← (List.range k).foldlM (fun r _ => do let (_, r) ← rdU32 ba b r; pure r) q
  let (m, s) ← rdU32 ba b r
  if 1000 < m then throw ("start function results size is out of bounds", r)
  if s != b then throw ("unexpected content in the component start section", s)

/-- The checks of `Parser::parse_reader` on one module section whose contents are `[a, b)`
(`b ≤ lim`), except the code section. -/
def checkModuleSecB (ba : ByteArray) (st : PState) (id : Nat) (a b : Nat) : Except FErr PState := do
  if id == 0 then
    let _ ← rdStr ba b a
    return st
  match moduleOrder id with
  | none => pure st
  | some o =>
    if o ≤ st.order then throw ("section out of order", a)
    let st := { st with order := o }
    if id == 8 then
      let _ ← singleU32B ba "start" a b
      pure st
    else if id == 12 then
      let n ← singleU32B ba "data count" a b
      pure { st with dataCount := some n }
    else
      let (n, _) ← rdU32 ba b a
      if id == 3 then pure { st with funcs := some n }
      else if id == 11 then
        let st := { st with datas := some n }
        checkDataCountB st b
        pure st
      else pure st

/-- The checks of `Parser::parse_reader` on one (non-nested) component section `[a, b)`. -/
def checkComponentSecB (ba : ByteArray) (st : PState) (id : Nat) (a b : Nat) : Except FErr PState := do
  if id == 0 then
    let _ ← rdStr ba b a
    return st
  if id == 9 then
    if st.start then throw ("component cannot have more than one start function", a)
    readCompStartB ba a b
    return { st with start := true }
  if id ∈ [2, 3, 5, 6, 7, 8, 10, 11] then
    let _ ← rdU32 ba b a
  pure st

/-- The checks at the end of a unit, at offset `off`. -/
def checkEndB : Enc → PState → Nat → Except FErr Unit
  | .module, st, off => do checkFuncCodeB st off; checkDataCountB st off
  | .component, _, _ => pure ()

mutual
/-- The sections of a unit from `pos`: the input is available below `lim`, and the unit
declares its end at `max` (`none` for the outer unit, whose end is the end of the input). -/
def parseSecsHB (ba : ByteArray) (hk : Hook) : Nat → Enc → PState → Nat → Nat → Option Nat → Except FErr (List ItemB)
  | 0, _, _, pos, _, _ => .error ("nesting too deep", pos)
  | f + 1, enc, st, pos, lim, max => do
    if lim ≤ pos then
      if let some m := max then if pos < m then throw (errEof, pos)
      checkEndB enc st pos
      return []
    if pos + 4 ≤ lim && magicAt ba pos then throw ("expected section, got wasm magic number", pos)
    let id := byteAt ba pos
    if 128 ≤ id.toNat then throw ("malformed section id", pos)
    let (len, a) ← rdU32 ba lim (pos + 1)
    let b := a + len
    if let some m := max then
      if m < b then throw ("section too large, " ++ toString len ++ " goes past " ++ hexStr m, pos + 1)
    if isNest enc id then
      if 1073741824 < len then
        throw ((if id == 1 then "module" else "component") ++ " section is too large", pos + 1)
      let (enc', items) ← parseUnitHB ba hk f (some (nestEnc id)) a (Nat.min b lim) (some b)
      let is ← parseSecsHB ba hk f enc st b lim max
      pure (.nest id (pos + 1) a b enc' items :: is)
    else if enc == .module && id == 10 then
      match moduleOrder 10 with
      | none => throw ("unreachable", pos)
      | some o =>
        if o ≤ st.order then throw ("section out of order", a)
        let (n, p) ← rdU32 ba lim a
        if len < p - a then throw (errEof, a)
        let st := { st with order := o, codes := some n }
        checkFuncCodeB st a
        let e ← codeBodiesB ba lim n p (len - (p - a))
        let is ← parseSecsHB ba hk f enc st e lim max
        pure (.sec ⟨id, pos + 1, a, b⟩ :: is)
    else
      let _ ← rdBytes lim a len
      let st ← match enc with
        | .module => checkModuleSecB ba st id.toNat a b
        | .component => checkComponentSecB ba st id.toNat a b
      if id == 0 then hk max.isNone a b
      let is ← parseSecsHB ba hk f enc st b lim max
      pure (.sec ⟨id, pos + 1, a, b⟩ :: is)
/-- A unit at `pos`: header, then sections. -/
def parseUnitHB (ba : ByteArray) (hk : Hook) : Nat → Option Enc → Nat → Nat → Option Nat → Except FErr (Enc × List ItemB)
  | 0, _, pos, _, _ => .error ("nesting too deep", pos)
  | f + 1, expect, pos, lim, max => do
    let (enc, p) ← readHeaderB ba expect lim pos
    let items ← parseSecsHB ba hk f enc {} p lim max
    pure (enc, items)
end

/-- **The payload walk over a `ByteArray`** (`Parser::new(0).parse_all`). -/
def parseBinaryHB (ba : ByteArray) (hk : Hook) : Except FErr (Enc × List ItemB) :=
  parseUnitHB ba hk (ba.size + 2) none 0 ba.size none

/-- The payload walk without a hook. -/
def parseBinaryB (ba : ByteArray) : Except FErr (Enc × List ItemB) := parseBinaryHB ba noHook

/-- The name and data ranges of a custom section's contents `[a, b)`. -/
def customOfB (ba : ByteArray) (a b : Nat) : Except FErr (Nat × Nat) := rdStr ba b a

/-- A slice of the input as an array. -/
@[inline] def slice (ba : ByteArray) (i j : Nat) : ByteArray := ba.extract i j

/-- Append `[a, b)` of `ba` to `out`. -/
@[inline] def appendSlice (out ba : ByteArray) (a b : Nat) : ByteArray :=
  ba.copySlice a out out.size (b - a) false

/-- Append a list of bytes. -/
@[inline] def appendList (out : ByteArray) (l : List UInt8) : ByteArray :=
  l.foldl ByteArray.push out

/-- Append `rawSec id body` for the body `[a, b)` of `ba`. -/
def pushRawSec (out : ByteArray) (id : UInt8) (ba : ByteArray) (a b : Nat) : ByteArray :=
  appendSlice (appendList (out.push id) (encU32 (b - a))) ba a b

end Silmaril.Wasm.Tools.Meta

end
