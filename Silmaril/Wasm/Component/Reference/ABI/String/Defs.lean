module

public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs

/-!
# Canonical ABI strings: codecs, tagged lengths and store plans

This file transcribes the memory-independent part of the canonical ABI string
algorithms of the Python reference `design/mvp/canonical-abi/definitions.py`
(component-model revision `a25fc0b`; prose in `CanonicalABI.md`, sections
"Loading" → `load_string`, and "Storing" → `store_string`):

* `CanonicalOptions.string_encoding` (`'utf8' | 'utf16' | 'latin1+utf16'`) is
  `StringEncoding`, and the Python `String = tuple[str, str, int]` is `StringValue`.
* `utf16_tag`, `REALLOC_I32_MAX` and `MAX_STRING_BYTE_LENGTH` are `utf16Tag`,
  `reallocI32Max` and `maxStringByteLength`. At `a25fc0b` the maximum string byte
  length is `(1 << 28) - 1` (not `(1 << 31) - 1` as in older revisions).
* The Python codecs `'utf-8'`, `'utf-16-le'` and `'latin-1'` (strict mode) are
  `utf8Encode`/`utf8Decode?`, `utf16Encode`/`utf16Decode?` and
  `latin1Encode`/`latin1Decode`. Decoding failures are `none`, which the callers
  turn into traps. The UTF-8 decoder is Lean's `String.fromUTF8?`, whose validity
  notion (`ByteArray.IsValidUTF8`: "is the encoding of some list of scalar
  values") is exactly well-formed UTF-8, as for Python's strict codec.
* `load_string_from_range` is `loadStringFromRange?` over a byte-list image of
  memory (`loadRange` exposes its length/alignment/decoder choice separately).
* `store_string_into_range`, `store_string_copy`, `store_string_to_utf8`,
  `store_utf16_to_utf8`, `store_latin1_to_utf8`, `store_utf8_to_utf16`,
  `store_string_to_latin1_or_utf16` and `store_probably_utf16_to_latin1_or_utf16`
  are `storeStringIntoRange` and the `store*` plan builders. They do not touch
  memory: they return a `StorePlan`, a straight-line program of `StoreStep`s
  (realloc requests relative to the current pointer, trap checks, writes and the
  in-place latin1 inflation / utf16 deflation loops) plus the returned (tagged)
  code-unit count. The Python control flow never depends on realloc results
  except through traps, so this program is exact; `StorePlan.run` replays it over
  a byte-list memory with a caller-supplied realloc. Consecutive single-byte
  Python writes with no realloc or check in between are merged into one `write`.

Deviations and non-claims. Python `assert`s (such as `REALLOC_I32_MAX` bounds and
`dst_byte_length == len(encoded)`) are not traps; the plan builders are total and
their behaviour on inputs violating those assertions (a `StringValue` whose
code-unit hint disagrees with its text, see `StringValue.Consistent`) is
unspecified by the reference. `storeStringIntoRange` untags a `latin1+utf16`
source with the *destination* memory's tag, as the Python does. Memory is a
`List UInt8` here; realloc is an arbitrary function in `StorePlan.run`, and the
memory-backed canonical ABI is expected to replay `StorePlan.steps` itself.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

/-- `CanonicalOptions.string_encoding`. -/
inductive StringEncoding where
  | utf8 | utf16 | latin1Utf16
  deriving Repr, DecidableEq

/-- A concrete byte codec: the Python `encoding` argument to `bytes.decode`. -/
inductive Codec where
  | utf8 | utf16 | latin1
  deriving Repr, DecidableEq

/-- `utf16_tag(ptr_type) = 1 << (ptr_size(ptr_type) * 8 - 1)`. -/
def utf16Tag : AddrType → Nat
  | .i32 => 2 ^ 31
  | .i64 => 2 ^ 63

/-- `REALLOC_I32_MAX`. -/
def reallocI32Max : Nat := 2 ^ 32 - 1

/-- `MAX_STRING_BYTE_LENGTH` at `a25fc0b`. -/
def maxStringByteLength : Nat := 2 ^ 28 - 1

/-- Python `bool(tagged & tag)`. -/
def isUtf16Tagged (a : AddrType) (tagged : Nat) : Bool := tagged &&& utf16Tag a != 0

/-- Python `tagged ^ tag`, used only when the tag bit is set. -/
def untagUtf16 (a : AddrType) (tagged : Nat) : Nat := tagged ^^^ utf16Tag a

/-- Python `code_units | utf16_tag(ptr_type)`. -/
def tagUtf16 (a : AddrType) (units : Nat) : Nat := units ||| utf16Tag a

/-! ## UTF-8 -/

/-- Python `str.encode('utf-8')`. -/
def utf8Encode (s : String) : List UInt8 := s.toList.flatMap String.utf8EncodeChar

/-- Python strict `bytes.decode('utf-8')`; `none` is a `UnicodeError`. -/
def utf8Decode? (bs : List UInt8) : Option String := String.fromUTF8? bs.toByteArray

/-! ## UTF-16LE -/

/-- The UTF-16 code units of one scalar value (a surrogate pair above the BMP). -/
def utf16EncodeChar (c : Char) : List UInt16 :=
  if c.toNat < 0x10000 then [c.toNat.toUInt16]
  else
    let v := c.toNat - 0x10000
    [(0xD800 + v / 0x400).toUInt16, (0xDC00 + v % 0x400).toUInt16]

def utf16Units (s : String) : List UInt16 := s.toList.flatMap utf16EncodeChar

/-- Number of UTF-16 code units of a scalar value. -/
def utf16CharLength (c : Char) : Nat := if c.toNat < 0x10000 then 1 else 2

/-- Number of UTF-16 code units of a string. -/
def utf16Length (s : String) : Nat := (s.toList.map utf16CharLength).sum

/-- Strict UTF-16 decoding of code units: lone or reversed surrogates fail. -/
def utf16DecodeUnits? : List UInt16 → Option (List Char)
  | [] => some []
  | u :: us =>
    if u.toNat < 0xD800 ∨ 0xE000 ≤ u.toNat then
      (Char.ofNat u.toNat :: ·) <$> utf16DecodeUnits? us
    else if u.toNat < 0xDC00 then
      match us with
      | l :: us' =>
        if 0xDC00 ≤ l.toNat ∧ l.toNat < 0xE000 then
          (Char.ofNat (0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00)) :: ·) <$>
            utf16DecodeUnits? us'
        else none
      | [] => none
    else none

def unitsToBytesLE : List UInt16 → List UInt8
  | [] => []
  | u :: us => (u.toNat % 256).toUInt8 :: (u.toNat / 256).toUInt8 :: unitsToBytesLE us

/-- Pair little-endian bytes into code units; an odd length fails ("truncated data"). -/
def bytesToUnitsLE? : List UInt8 → Option (List UInt16)
  | [] => some []
  | [_] => none
  | lo :: hi :: bs => ((lo.toNat + 256 * hi.toNat).toUInt16 :: ·) <$> bytesToUnitsLE? bs

/-- Python `str.encode('utf-16-le')`. -/
def utf16Encode (s : String) : List UInt8 := unitsToBytesLE (utf16Units s)

/-- Python strict `bytes.decode('utf-16-le')`. -/
def utf16Decode? (bs : List UInt8) : Option String := do
  let us ← bytesToUnitsLE? bs
  let cs ← utf16DecodeUnits? us
  pure (String.ofList cs)

/-! ## Latin-1 -/

/-- Every scalar value is below 256, so `str.encode('latin-1')` succeeds. -/
def isLatin1 (s : String) : Bool := s.toList.all (·.toNat < 256)

/-- Python `str.encode('latin-1')`; only meaningful when `isLatin1 s`. -/
def latin1Encode (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

/-- Python `bytes.decode('latin-1')`, which never fails. -/
def latin1Decode (bs : List UInt8) : String := String.ofList (bs.map (Char.ofNat ·.toNat))

def Codec.decode? : Codec → List UInt8 → Option String
  | .utf8, bs => utf8Decode? bs
  | .utf16, bs => utf16Decode? bs
  | .latin1, bs => some (latin1Decode bs)

/-! ## Values and loading -/

/-- The Python lifted `String = (str, encoding, tagged_code_units)`. The code-unit
count is a hint in the source encoding and keeps the tag bit. -/
structure StringValue where
  str : String
  encoding : StringEncoding
  taggedCodeUnits : Nat
  deriving Repr, DecidableEq

/-- The byte range and codec chosen by `load_string_from_range`. -/
structure LoadRange where
  alignment : Alignment
  byteLength : Nat
  codec : Codec
  deriving Repr, DecidableEq

/-- The `match cx.opts.string_encoding` of `load_string_from_range`. A `utf16`
length is not untagged: a tagged value fails the maximum-length check. -/
def loadRange (enc : StringEncoding) (a : AddrType) (tagged : Nat) : LoadRange :=
  match enc with
  | .utf8 => ⟨.one, tagged, .utf8⟩
  | .utf16 => ⟨.two, 2 * tagged, .utf16⟩
  | .latin1Utf16 =>
    if isUtf16Tagged a tagged then ⟨.two, 2 * untagUtf16 a tagged, .utf16⟩
    else ⟨.two, tagged, .latin1⟩

/-- `load_string_from_range(cx, ptr, tagged_code_units)` over the whole memory
image `mem`; `none` is a trap. -/
def loadStringFromRange? (enc : StringEncoding) (a : AddrType) (mem : List UInt8)
    (ptr tagged : Nat) : Option StringValue :=
  let r := loadRange enc a tagged
  if r.byteLength > maxStringByteLength then none
  else if ptr ≠ alignTo ptr r.alignment then none
  else if ptr + r.byteLength > mem.length then none
  else (r.codec.decode? ((mem.drop ptr).take r.byteLength)).map fun s => ⟨s, enc, tagged⟩

/-- The code-unit hint of a value agrees with its text, as it does for every
value produced by `loadStringFromRange?` (with the same address type). The Python
store functions assert this. -/
def StringValue.Consistent (a : AddrType) (v : StringValue) : Prop :=
  match v.encoding with
  | .utf8 => v.taggedCodeUnits = (utf8Encode v.str).length
  | .utf16 => v.taggedCodeUnits = utf16Length v.str
  | .latin1Utf16 =>
    if isUtf16Tagged a v.taggedCodeUnits then
      untagUtf16 a v.taggedCodeUnits = utf16Length v.str
    else v.taggedCodeUnits = v.str.length ∧ isLatin1 v.str = true

instance (a : AddrType) (v : StringValue) : Decidable (v.Consistent a) := by
  unfold StringValue.Consistent; split <;> first | split <;> infer_instance | infer_instance

/-! ## Store plans -/

/-- One step of a store algorithm, relative to the current pointer `ptr`. -/
inductive StoreStep where
  /-- `ptr = cx.allocate(alignment, size)`, i.e. `reallocate(0, 0, alignment, size)`. -/
  | allocate (alignment : Alignment) (size : Nat)
  /-- `ptr = cx.reallocate(ptr, oldSize, alignment, newSize)`. -/
  | reallocate (oldSize : Nat) (alignment : Alignment) (newSize : Nat)
  /-- `trap_if(ptr != align_to(ptr, alignment))`. -/
  | trapIfMisaligned (alignment : Alignment)
  /-- `trap_if(ptr + size > len(cx.opts.memory))`. -/
  | trapIfOutOfBounds (size : Nat)
  /-- `cx.opts.memory[ptr + offset : ptr + offset + len(bytes)] = bytes`. -/
  | write (offset : Nat) (bytes : List UInt8)
  /-- `for j in range(count-1, -1, -1): mem[ptr+2j] = mem[ptr+j]; mem[ptr+2j+1] = 0`. -/
  | inflateLatin1 (count : Nat)
  /-- `for i in range(count): mem[ptr+i] = mem[ptr+2i]`. -/
  | deflateUtf16 (count : Nat)
  deriving Repr, DecidableEq

/-- The steps of one store and the returned (possibly tagged) code-unit count. The
returned pointer is the current pointer after the last step. -/
structure StorePlan where
  steps : List StoreStep
  taggedCodeUnits : Nat
  deriving Repr, DecidableEq

/-- Every write and every inflation/deflation loop touches only
`[ptr, ptr + min allocated checked)`, where `allocated` is the size requested by
the latest realloc and `checked` the size of the latest bounds check after it;
each `reallocate` passes the current block size as its old size. -/
def stepsInBounds : Nat → Nat → List StoreStep → Bool
  | _, _, [] => true
  | _, _, .allocate _ size :: ss => stepsInBounds size 0 ss
  | al, _, .reallocate old _ size :: ss => old == al && stepsInBounds size 0 ss
  | al, _, .trapIfOutOfBounds k :: ss => stepsInBounds al k ss
  | al, ck, .trapIfMisaligned _ :: ss => stepsInBounds al ck ss
  | al, ck, .write off bs :: ss => decide (off + bs.length ≤ min al ck) && stepsInBounds al ck ss
  | al, ck, .inflateLatin1 n :: ss => decide (2 * n ≤ min al ck) && stepsInBounds al ck ss
  | al, ck, .deflateUtf16 n :: ss => decide (2 * n ≤ min al ck) && stepsInBounds al ck ss

def StorePlan.InBounds (p : StorePlan) : Prop := stepsInBounds 0 0 p.steps = true

/-- The `new_byte_length` of every realloc call, in order. -/
def StorePlan.requestSizes (p : StorePlan) : List Nat :=
  p.steps.filterMap fun
    | .allocate _ n | .reallocate _ _ n => some n
    | _ => none

/-- Length of the longest prefix whose scalar values are below `bound`. -/
def prefixBelow (bound : Nat) (s : String) : Nat :=
  (s.toList.takeWhile (·.toNat < bound)).length

/-- `store_string_copy(cx, src, src_code_units, dst_code_unit_size, dst_alignment,
dst_encoding)`, given `encoded = src.encode(dst_encoding)`. -/
def storeStringCopy (encoded : List UInt8) (codeUnits unitSize : Nat) (align : Alignment) :
    StorePlan :=
  let len := unitSize * codeUnits
  ⟨[.allocate align len, .trapIfMisaligned align, .trapIfOutOfBounds len, .write 0 encoded],
    codeUnits⟩

/-- `store_string_to_utf8(cx, src, src_code_units, worst_case_size)`. -/
def storeStringToUtf8 (src : String) (codeUnits worstCase : Nat) : StorePlan :=
  let encoded := utf8Encode src
  let i := prefixBelow 0x80 src
  let start := [.allocate .one codeUnits, .trapIfOutOfBounds codeUnits, .write 0 (encoded.take i)]
  if i = src.length then ⟨start, codeUnits⟩
  else
    let shrink :=
      if worstCase > encoded.length then
        [.reallocate worstCase .one encoded.length, .trapIfOutOfBounds encoded.length]
      else []
    ⟨start ++ [.reallocate codeUnits .one worstCase, .trapIfOutOfBounds worstCase,
      .write i (encoded.drop i)] ++ shrink, encoded.length⟩

/-- `store_utf16_to_utf8`: worst case `3 * src_code_units`. -/
def storeUtf16ToUtf8 (src : String) (codeUnits : Nat) : StorePlan :=
  storeStringToUtf8 src codeUnits (codeUnits * 3)

/-- `store_latin1_to_utf8`: worst case `2 * src_code_units`. -/
def storeLatin1ToUtf8 (src : String) (codeUnits : Nat) : StorePlan :=
  storeStringToUtf8 src codeUnits (codeUnits * 2)

/-- `store_utf8_to_utf16(cx, src, src_code_units)`. -/
def storeUtf8ToUtf16 (src : String) (codeUnits : Nat) : StorePlan :=
  let worstCase := 2 * codeUnits
  let encoded := utf16Encode src
  let shrink :=
    if encoded.length < worstCase then
      [.reallocate worstCase .two encoded.length, .trapIfMisaligned .two,
        .trapIfOutOfBounds encoded.length]
    else []
  ⟨[.allocate .two worstCase, .trapIfMisaligned .two, .trapIfOutOfBounds worstCase,
    .write 0 encoded] ++ shrink, encoded.length / 2⟩

/-- `store_string_to_latin1_or_utf16(cx, src, src_code_units)`. -/
def storeStringToLatin1OrUtf16 (a : AddrType) (src : String) (codeUnits : Nat) : StorePlan :=
  let i := prefixBelow 0x100 src
  let start := [.allocate .two codeUnits, .trapIfMisaligned .two, .trapIfOutOfBounds codeUnits,
    .write 0 ((latin1Encode src).take i)]
  if i = src.length then
    let shrink :=
      if i < codeUnits then
        [.reallocate codeUnits .two i, .trapIfMisaligned .two, .trapIfOutOfBounds i]
      else []
    ⟨start ++ shrink, i⟩
  else
    let worstCase := 2 * codeUnits
    let encoded := utf16Encode src
    let shrink :=
      if worstCase > encoded.length then
        [.reallocate worstCase .two encoded.length, .trapIfMisaligned .two,
          .trapIfOutOfBounds encoded.length]
      else []
    ⟨start ++ [.reallocate codeUnits .two worstCase, .trapIfMisaligned .two,
      .trapIfOutOfBounds worstCase, .inflateLatin1 i, .write (2 * i) (encoded.drop (2 * i))] ++
      shrink, tagUtf16 a (encoded.length / 2)⟩

/-- `store_probably_utf16_to_latin1_or_utf16(cx, src, src_code_units)`. The final
realloc is unconditional and uses alignment 1, as in the Python. -/
def storeProbablyUtf16ToLatin1OrUtf16 (a : AddrType) (src : String) (codeUnits : Nat) :
    StorePlan :=
  let byteLength := 2 * codeUnits
  let encoded := utf16Encode src
  let start := [.allocate .two byteLength, .trapIfMisaligned .two,
    .trapIfOutOfBounds byteLength, .write 0 encoded]
  if src.toList.any (·.toNat ≥ 0x100) then ⟨start, tagUtf16 a (encoded.length / 2)⟩
  else
    let latin1Size := encoded.length / 2
    ⟨start ++ [.deflateUtf16 latin1Size, .reallocate byteLength .one latin1Size,
      .trapIfOutOfBounds latin1Size], latin1Size⟩

/-- `src_simple_encoding` of `store_string_into_range`, untagging with the
destination tag `utf16_tag(cx.opts.memory.ptr_type())`. -/
def StringValue.simpleCodec (a : AddrType) (v : StringValue) : Codec :=
  match v.encoding with
  | .utf8 => .utf8
  | .utf16 => .utf16
  | .latin1Utf16 => if isUtf16Tagged a v.taggedCodeUnits then .utf16 else .latin1

/-- `src_code_units` of `store_string_into_range`. -/
def StringValue.codeUnits (a : AddrType) (v : StringValue) : Nat :=
  match v.encoding with
  | .latin1Utf16 =>
    if isUtf16Tagged a v.taggedCodeUnits then untagUtf16 a v.taggedCodeUnits
    else v.taggedCodeUnits
  | _ => v.taggedCodeUnits

/-- `store_string_into_range(cx, v)` into a memory of address type `a` with
destination encoding `dst`. -/
def storeStringIntoRange (dst : StringEncoding) (a : AddrType) (v : StringValue) : StorePlan :=
  let src := v.str
  let n := v.codeUnits a
  match dst, v.simpleCodec a with
  | .utf8, .utf8 => storeStringCopy (utf8Encode src) n 1 .one
  | .utf8, .utf16 => storeUtf16ToUtf8 src n
  | .utf8, .latin1 => storeLatin1ToUtf8 src n
  | .utf16, .utf8 => storeUtf8ToUtf16 src n
  | .utf16, .utf16 | .utf16, .latin1 => storeStringCopy (utf16Encode src) n 2 .two
  | .latin1Utf16, simple =>
    match v.encoding, simple with
    | .latin1Utf16, .latin1 => storeStringCopy (latin1Encode src) n 1 .two
    | .latin1Utf16, _ => storeProbablyUtf16ToLatin1OrUtf16 a src n
    | _, _ => storeStringToLatin1OrUtf16 a src n

/-! ## Replaying a plan -/

/-- The arguments of one `cx.reallocate(old, old_byte_length, alignment,
new_byte_length)` call (`allocate` passes `old = old_byte_length = 0`). -/
structure ReallocRequest where
  oldPtr : Nat
  oldSize : Nat
  alignment : Nat
  newSize : Nat
  deriving Repr, DecidableEq

/-- A realloc implementation: from allocator state and memory, either a trap
(`none`) or new state, memory and the returned pointer. -/
abbrev Realloc (σ : Type) := ReallocRequest → σ × List UInt8 → Option (σ × List UInt8 × Nat)

/-- Machine state while replaying a plan. `requests` logs realloc calls, oldest first. -/
structure StoreState (σ : Type) where
  alloc : σ
  mem : List UInt8
  ptr : Nat
  requests : List ReallocRequest

/-- Bytearray slice assignment `mem[addr : addr + len(bs)] = bs`. -/
def writeBytes (mem : List UInt8) (addr : Nat) (bs : List UInt8) : List UInt8 :=
  mem.take addr ++ bs ++ mem.drop (addr + bs.length)

def memInflateLatin1 (mem : List UInt8) (ptr count : Nat) : List UInt8 :=
  (List.range count).reverse.foldl
    (fun m j => (m.set (ptr + 2 * j) (m.getD (ptr + j) 0)).set (ptr + 2 * j + 1) 0) mem

def memDeflateUtf16 (mem : List UInt8) (ptr count : Nat) : List UInt8 :=
  (List.range count).foldl (fun m i => m.set (ptr + i) (m.getD (ptr + 2 * i) 0)) mem

section
variable {σ : Type}

def StoreStep.run (realloc : Realloc σ) (st : StoreState σ) : StoreStep → Option (StoreState σ)
  | .allocate al size => call ⟨0, 0, al.bytes, size⟩
  | .reallocate old al size => call ⟨st.ptr, old, al.bytes, size⟩
  | .trapIfMisaligned al => if st.ptr ≠ alignTo st.ptr al then none else some st
  | .trapIfOutOfBounds size => if st.ptr + size > st.mem.length then none else some st
  | .write off bs => some { st with mem := writeBytes st.mem (st.ptr + off) bs }
  | .inflateLatin1 n => some { st with mem := memInflateLatin1 st.mem st.ptr n }
  | .deflateUtf16 n => some { st with mem := memDeflateUtf16 st.mem st.ptr n }
where
  call (r : ReallocRequest) : Option (StoreState σ) :=
    (realloc r (st.alloc, st.mem)).map fun (alloc, mem, ptr) =>
      ⟨alloc, mem, ptr, st.requests ++ [r]⟩

def StoreStep.runAll (realloc : Realloc σ) (st : StoreState σ) :
    List StoreStep → Option (StoreState σ)
  | [] => some st
  | s :: ss => (s.run realloc st).bind fun st' => runAll realloc st' ss

/-- Replay a plan from allocator state and memory. On success, returns the final
state; the stored string is `(final.ptr, plan.taggedCodeUnits)`. -/
def StorePlan.run (p : StorePlan) (realloc : Realloc σ) (alloc : σ) (mem : List UInt8) :
    Option (StoreState σ) :=
  StoreStep.runAll realloc ⟨alloc, mem, 0, []⟩ p.steps

end

/-- A bump allocator that copies `min(oldSize, newSize)` bytes from the old block,
trapping when the new block does not fit in memory. Its state is the next free
address. Used only for tests and examples. -/
def bumpRealloc : Realloc Nat := fun r (next, mem) =>
  let ptr := (next + r.alignment - 1) / r.alignment * r.alignment
  if ptr + r.newSize > mem.length then none
  else
    let moved := (mem.drop r.oldPtr).take (min r.oldSize r.newSize)
    some (ptr + r.newSize, writeBytes mem ptr moved, ptr)

end Silmaril.Wasm.Component.ABI
