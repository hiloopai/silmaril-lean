module

public import Silmaril.Wasm.Binary.Basic

/-!
# Section framing of Wasm modules and components (wasmparser's `Parser`)

The layer of a Wasm binary below its section contents, as wasmparser's `Parser`
(`crates/wasmparser/src/parser.rs`, wasm-tools 1.262.0) reads it; `strip` and `objdump` work at
this layer.

* `readUN N b`: an unsigned LEB128 number of at most `N` bits, with the bytes it used; exactly
  silmaril-lean's grammar `UN N` (`Thms`: `readUN_sound`, `readUN_complete`), which for `N = 32`
  is wasmparser's `read_var_u32` (at most 5 bytes, the unused bits of the fifth zero);
* `encUN n`: the minimal LEB128 encoding (`Thms`: `encUN_un`);
* `RawSec`: a section as it is in the file: id, the bytes of its size, its content;
  `RawSec.bytes`, `join`: the bytes of sections; `RawSec.canon`: the same section with its size
  written minimally (what `wasm_encoder::RawSection` writes);
* `splitSecs b`: the sections of `b` (no checks on contents); `Thms`: `splitSecs_sound`
  (`join` gives back `b`), `splitSecs_join` (complete on well-formed sizes);
* `Enc`, `readHeader`: the 8-byte preamble (`\0asm`, version 1 kind 0 for a module, version
  `0xd` kind 1 for a component);
* `checkSecs`: the checks wasmparser's `Parser` makes on the section list beyond framing
  (section ids, module section order, function/code and data-count consistency, custom section
  names, the counts of vector sections, single-item sections, code entry framing, nested
  headers are checked by the caller). These are a transcription of upstream's checks, tested
  against it (`tools/wasm-tools/tests`), not a theorem.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Framing

open Silmaril.Wasm.Binary (Bytes)

/-! ## LEB128 -/

/-- An unsigned LEB128 number of at most `N` bits: `(value, bytes used, rest)`. Mirrors
silmaril-lean's `UN N` clause by clause. -/
def readUN : Nat → Bytes → Option (Nat × Bytes × Bytes)
  | _, [] => none
  | N, n :: b =>
    if n.toNat < 2 ^ 7 then
      if n.toNat < 2 ^ N then some (n.toNat, [n], b) else none
    else if 7 < N then
      match readUN (N - 7) b with
      | some (m, lb, r) => some (2 ^ 7 * m + (n.toNat - 2 ^ 7), n :: lb, r)
      | none => none
    else none

/-- `read_var_u32`. -/
def readU32 (b : Bytes) : Option (Nat × Bytes × Bytes) := readUN 32 b

/-- The minimal LEB128 encoding. -/
def encUN (n : Nat) : Bytes :=
  if h : n < 2 ^ 7 then [n.toUInt8]
  else (n % 2 ^ 7 + 2 ^ 7).toUInt8 :: encUN (n / 2 ^ 7)
termination_by n
decreasing_by omega

/-- `n ≤ l.length`, walking at most `n` cells (`Thms`: `atLeast_iff`); the length of a
multi-megabyte list is not computed for every section. -/
def atLeast {α : Type} : Nat → List α → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, _ :: r => atLeast n r

/-! ## Sections -/

/-- A section as it is in the file. -/
structure RawSec where
  id : UInt8
  size : Bytes
  content : Bytes
  deriving Repr, DecidableEq

/-- The bytes of a section. -/
def RawSec.bytes (s : RawSec) : Bytes := s.id :: (s.size ++ s.content)

/-- The bytes of a list of sections. -/
def join : List RawSec → Bytes
  | [] => []
  | s :: ss => s.bytes ++ join ss

/-- The section with its size written minimally. -/
def RawSec.canon (s : RawSec) : RawSec := { s with size := encUN s.content.length }

/-- The sections of a byte string, with fuel (one step per section). -/
def splitSecsF : Nat → Bytes → Option (List RawSec)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, id :: rest =>
    match readU32 rest with
    | none => none
    | some (len, lb, r) =>
      if atLeast len r then
        (splitSecsF fuel (r.drop len)).map (⟨id, lb, r.take len⟩ :: ·)
      else none

/-- **The sections of a byte string** (the part after the preamble). -/
def splitSecs (b : Bytes) : Option (List RawSec) := splitSecsF b.length b

/-- Well-formed size fields: each section's size bytes are an LEB128 `u32` of its length. -/
def SizesOk (ss : List RawSec) : Prop :=
  ∀ s ∈ ss, Silmaril.Wasm.Binary.U32 s.size s.content.length

/-! ## The preamble -/

/-- Module or component. -/
inductive Enc where
  | module
  | component
  deriving Repr, DecidableEq

/-- `\0asm`. -/
def magic : Bytes := [0x00, 0x61, 0x73, 0x6D]

/-- The preamble of an encoding (`wasm_encoder::{Module, Component}::HEADER`). -/
def Enc.header : Enc → Bytes
  | .module => magic ++ [0x01, 0x00, 0x00, 0x00]
  | .component => magic ++ [0x0d, 0x00, 0x01, 0x00]

/-- Read the preamble (`State::Header`): the encoding and the rest. `expect` is the encoding a
nested section requires. Errors are upstream's messages. -/
def readHeader (expect : Option Enc) (b : Bytes) : Except String (Enc × Bytes) :=
  if b.take 4 ≠ magic then .error "magic header not detected: bad magic number"
  else if !atLeast 8 b then .error "unexpected end-of-file"
  else
    let v := b.drop 4 |>.take 4
    let r := b.drop 8
    if v = [0x01, 0x00, 0x00, 0x00] then
      if expect = some .component then .error "expected a version header for a component"
      else .ok (.module, r)
    else if v = [0x0d, 0x00, 0x01, 0x00] then
      if expect = some .module then .error "expected a version header for a module"
      else .ok (.component, r)
    else .error "unknown binary version"

/-! ## The parser's checks -/

/-- The order rank of a module section id (`Order`), `none` for custom and unknown ids. -/
def orderRank : Nat → Option Nat
  | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4 | 5 => some 5 | 13 => some 6
  | 6 => some 7 | 7 => some 8 | 8 => some 9 | 9 => some 10 | 12 => some 11 | 10 => some 12
  | 11 => some 13
  | _ => none

/-- Is a module section id one of wasmparser's vector sections (`SectionLimited`)? -/
def moduleLimited (id : Nat) : Bool :=
  id ∈ [1, 2, 3, 4, 5, 6, 7, 9, 11, 13]

/-- Is a component section id one of wasmparser's vector sections? -/
def componentLimited (id : Nat) : Bool :=
  id ∈ [2, 3, 5, 6, 7, 8, 10, 11]

/-- `read_string`: a name of at most 100 000 bytes of UTF-8; the name and the rest. -/
def readName (b : Bytes) : Except String (String × Bytes) :=
  match readU32 b with
  | none => .error "unexpected end-of-file"
  | some (len, _, r) =>
    if len > 100000 then .error "string size out of bounds"
    else if !atLeast len r then .error "unexpected end-of-file"
    else
      match String.fromUTF8? (ByteArray.mk (r.take len).toArray) with
      | some s => .ok (s, r.drop len)
      | none => .error "malformed UTF-8 encoding"

/-- The name of a custom section and the offset of its data within the content. -/
def customName (content : Bytes) : Except String (String × Nat) := do
  let (n, r) ← readName content
  return (n, content.length - r.length)

/-- The leading count of a vector section. -/
def secCount (content : Bytes) : Except String Nat :=
  match readU32 content with
  | some (n, _, _) => .ok n
  | none => .error "unexpected end-of-file"

/-- Read a `u32`, as an `Except`. -/
def u32E (b : Bytes) : Except String (Nat × Bytes) :=
  match readU32 b with
  | some (n, _, r) => .ok (n, r)
  | none => .error "unexpected end-of-file"

/-- A single-item section (`start`, `data count`): one `u32` and nothing else. -/
def singleItem (desc : String) (content : Bytes) : Except String Nat := do
  let (n, r) ← u32E content
  if r.isEmpty then return n else .error s!"unexpected content in the {desc} section"

/-- The component start section: function index, arguments (at most 1000 indices), result
count (at most 1000), and nothing else. -/
def componentStart (content : Bytes) : Except String Unit := do
  let (_, r) ← u32E content
  let (nargs, r₁) ← u32E r
  if nargs > 1000 then .error "start function arguments size is out of bounds"
  let mut cur := r₁
  for _ in [0:nargs] do
    let (_, r') ← u32E cur
    cur := r'
  let (nres, r₂) ← u32E cur
  if nres > 1000 then .error "start function results size is out of bounds"
  if r₂.isEmpty then return () else .error "unexpected content in the component start section"

/-- The code section's entries: a count, then that many size-prefixed bodies exactly filling
the section. Returns the count. -/
def codeEntries (content : Bytes) : Except String Nat := do
  let (n, r₀) ← u32E content
  let mut cur := r₀
  for _ in [0:n] do
    let (len, r') ← u32E cur
    if !atLeast len r' then .error "unexpected end-of-file"
    cur := r'.drop len
  if cur.isEmpty then return n else .error "trailing bytes at end of section"

/-- The parser's running state for a module: last order rank, function and code counts, data
count and data entries. -/
structure ModState where
  last : Nat := 0
  funcs : Option Nat := none
  codes : Option Nat := none
  dataCount : Option Nat := none
  datas : Option Nat := none

/-- `check_function_code_counts`. -/
def ModState.checkCode (st : ModState) : Except String Unit :=
  match st.funcs, st.codes with
  | some n, some m => if n ≠ m then .error "function and code section have inconsistent lengths"
      else .ok ()
  | some n, none => if n > 0 then
      .error "function section has non-zero count but code section is absent" else .ok ()
  | none, some m => if m > 0 then
      .error "function section is absent but code section has non-zero count" else .ok ()
  | none, none => .ok ()

/-- `check_data_count`. -/
def ModState.checkData (st : ModState) : Except String Unit :=
  match st.dataCount, st.datas with
  | some n, some m => if n ≠ m then
      .error "data count and data section have inconsistent lengths" else .ok ()
  | some n, none => if n > 0 then .error "data count is non-zero but data section is absent"
      else .ok ()
  | _, _ => .ok ()

/-- One section of a module, through the parser's checks. -/
def ModState.step (st : ModState) (s : RawSec) : Except String ModState := do
  let id := s.id.toNat
  if id = 0 then
    let _ ← customName s.content
    return st
  match orderRank id with
  | none => return st
  | some k =>
    if k ≤ st.last then .error "section out of order"
    let st := { st with last := k }
    if moduleLimited id then
      let n ← secCount s.content
      if id = 3 then return { st with funcs := some n }
      if id = 11 then
        let st := { st with datas := some n }
        st.checkData
        return st
      return st
    if id = 8 then
      let _ ← singleItem "start" s.content
      return st
    if id = 12 then
      let n ← singleItem "data count" s.content
      return { st with dataCount := some n }
    -- id = 10, the code section
    let n ← codeEntries s.content
    let st := { st with codes := some n }
    st.checkCode
    return st

/-- **The parser's checks on a module's sections.** -/
def checkModule (ss : List RawSec) : Except String Unit := do
  let st ← ss.foldlM ModState.step {}
  st.checkCode
  st.checkData

/-- One section of a component (nested module and component sections are checked by the
caller). -/
def checkComponentSec (s : RawSec) : Except String Unit := do
  let id := s.id.toNat
  if id = 0 then
    let _ ← customName s.content
    return ()
  if componentLimited id then
    let _ ← secCount s.content
    return ()
  if id = 9 then componentStart s.content
  if (id = 1 ∨ id = 4) ∧ s.content.length > 1024 * 1024 * 1024 then
    .error (if id = 1 then "module section is too large" else "component section is too large")
  return ()

/-- **The parser's checks on a component's sections** (one start section at most). -/
def checkComponent (ss : List RawSec) : Except String Unit := do
  for s in ss do checkComponentSec s
  if (ss.filter (·.id == 9)).length > 1 then
    .error "component cannot have more than one start function"

/-- A section id with the high bit set is an error (`malformed section id`), and a section may
not start with the magic number. -/
def checkIds (ss : List RawSec) : Except String Unit := do
  for s in ss do
    if s.id.toNat ≥ 0x80 then .error "malformed section id"
    if s.id = 0 && s.size = [0x61] && s.content.take 2 = [0x73, 0x6D] then
      .error "expected section, got wasm magic number"

/-- The checks of an encoding. -/
def checkSecs (e : Enc) (ss : List RawSec) : Except String Unit := do
  checkIds ss
  match e with
  | .module => checkModule ss
  | .component => checkComponent ss

/-- Is the section a nested module or component (in a component)? -/
def nestedEnc : Enc → RawSec → Option Enc
  | .component, s => if s.id = 1 then some .module else if s.id = 4 then some .component else none
  | .module, _ => none

/-- Parse the preamble and split the sections. -/
def frame (expect : Option Enc) (b : Bytes) : Except String (Enc × List RawSec) := do
  let (e, rest) ← readHeader expect b
  match splitSecs rest with
  | some ss =>
    checkSecs e ss
    return (e, ss)
  | none => .error "unexpected end-of-file"

end Silmaril.Wasm.Tools.Framing
