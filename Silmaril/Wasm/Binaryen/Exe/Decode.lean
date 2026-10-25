module

public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Exe.EncodePadded

@[expose] public section

/-! # Executable binary decoder (the UNTRUSTED front end of `binaryen-lean`)

**Path chosen: a Lean binary decoder, not JSON from `tools/wasm-lean`.**

* The Rust decoder (`tools/wasm-lean/src/emit.rs`) emits Lean *source*; reusing it
  would mean a second emitter (JSON) plus `FromJson` instances for all of Core
  3.0's `Instr` (≈150 constructors) and its types, and a subprocess per run.
* The executable only needs the fragment the encoder covers (the Binaryen
  profile); everything else is passed through byte-for-byte, so a decoder for that
  fragment is small (sections 0–13; the profile's opcodes).
* Decoding is then **checked, not trusted**: the driver re-encodes the decoded
  module with the certified encoder and compares with the input
  (`roundTrip`). Equality plus `encodeModule?_sound` gives
  `Binary.Core.Encodes input m` (`decode_checked`), so the decoded module *is*
  the input's meaning. Non-canonical inputs (custom sections, non-minimal LEB,
  split locals groups) are reported and stripped of custom sections first
  (`stripCustom`); if they still differ the driver passes the input through.
* `tools/wasm-lean` stays the conformance oracle: `DecodeTest.lean` cross-checks
  the decoded export signatures of the corpus against `wasm-lean exports`.

Out-of-fragment constructs make `decodeModule` return `.error`; the driver treats
that as "out of profile" and copies the input unchanged.

## The fragment (milestone D1)

Exactly the image of `encodeModule?` (`Encode.lean`), read back:

* the header `\0asm` version 1;
* section 0 (custom): skipped, anywhere;
* section 1 (types): `0x60` function types only, each decoded as the singleton
  final group `⟨[⟨true, [], .func ft⟩]⟩` (the encoder's `encRecType`);
* section 2 (imports): function imports (`0x00 typeidx`), i32 or i64 funcref table imports,
  32-bit or 64-bit memory imports (`0x02` limits), global imports (`0x03 globaltype`)
  and tag imports (`0x04 tagtype`);
* section 13 (tags, after memories and before globals), tag exports (`0x04 tagidx`);
  `throw`, `throw_ref` and `try_table` with its catch clauses (`readCatch`);
* section 3 (functions), section 10 (code): same length, zipped into `Func`s;
  locals groups are expanded with `List.replicate`;
* sections 4 and 9 (funcref tables and function-index element segments);
* section 5 (defined 32-bit or 64-bit memories), 6 (globals), 7 (exports: functions, memories and globals), 8 (start);
* section 11 (data segments of kinds 0, 1 and 2) and the data count section 12, which
  comes before the code section; the count itself is not checked here (the round trip
  re-encodes it as the number of segments);
* value types `i32`/`i64`/`f32`/`f64`; block types `0x40`, a value type, or an `s33` type
  index; instructions: `encInstr`'s opcodes, nothing else (`if` with or without
  `else`, `select` without types, integer constants read as `s32`/`s64` and
  converted with `BitVec.ofInt`).

Non-custom sections must appear at most once, in binary section order (the tag
section 13 precedes globals; data count 12 precedes code). Every
vector count is bounded by the bytes left (each element takes at least a byte),
a function's locals by `maxLocals`, and section and code-entry sizes must match
the bytes consumed. Recursion over instructions is structural on a fuel argument
equal to the input size (each nested call consumes a byte first, so fuel never
runs out on real input); vector and section loops are bounded `for` loops. No
`partial` definitions.

## Round-trip policy (milestone D3)

`checkRoundTrip input m` classifies the re-encoding of the decoded module:

* `exact`: `encodeModule? m = .ok input`, hence `Encodes input m`
  (`decode_checked`);
* `customStripped`: equal after `stripCustom`; the input differs from a module
  encoding `m` only by custom sections, which carry no semantics (names, producers
  … are dropped, as `wasm-opt` does without `-g`);
* `mismatch offset`: the bytes differ (non-minimal LEB128, split locals groups,
  an empty `else`, empty sections, …) or `encodeModule?` failed.

**Policy:** optimise only when `RoundTrip.trusted` holds (`exact` or
`customStripped`); on `mismatch` pass the input through, reporting the first
differing offset. Rationale: the decoder is untrusted, and the end-to-end claim
(`Encodes input m` → passes preserve `m` → `Encodes output m'`) needs the first
link, which only the byte comparison gives. Optimising a mismatching decode
would make the output's relation to the input depend on unverified decoder code.
The driver (`Main.lean`) enforces this policy through `decodeChecked` /
`RoundTrip.trusted`: a module whose round trip is not trusted is passed through
(`"stage":"roundtrip"`) unless the experimental `--trust-decoder` flag is given.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- Decoder state: the input and a position. -/
structure Cursor where
  bytes : ByteArray
  pos : Nat

/-- The decoding monad. -/
abbrev DecodeM := StateT Cursor (Except String)

/-- Fail, reporting the current position. -/
def decodeError {α : Type} (msg : String) : DecodeM α := do
  let c ← get
  throw s!"decoder: {msg} (at byte {c.pos})"

def readByte : DecodeM UInt8 := do
  let c ← get
  if h : c.pos < c.bytes.size then
    set { c with pos := c.pos + 1 }
    pure c.bytes[c.pos]
  else throw s!"decoder: unexpected end of input at {c.pos}"

/-- The next byte, not consumed. -/
def peekByte : DecodeM (Option UInt8) := do
  let c ← get
  pure c.bytes[c.pos]?

/-- Bytes left in the input. -/
def remaining : DecodeM Nat := do
  let c ← get
  pure (c.bytes.size - c.pos)

/-- Unsigned LEB128 of at most `N` bits: at most `⌈N/7⌉` bytes, and the unused bits
of the last byte must be zero (equivalently, the value is below `2 ^ N`). -/
def readU (N : Nat) : DecodeM Nat := do
  let rec go (shift fuel : Nat) : DecodeM Nat := do
    match fuel with
    | 0 => throw "decoder: LEB128 too long"
    | fuel + 1 =>
      let b ← readByte
      let v := (b.toNat % 0x80) * 2 ^ shift
      if b.toNat < 0x80 then pure v else pure (v + (← go (shift + 7) fuel))
  let n ← go 0 ((N + 6) / 7)
  if n < 2 ^ N then pure n else throw "decoder: LEB128 out of range"

/-- Signed LEB128 of at most `N` bits: at most `⌈N/7⌉` bytes, and the unused bits of
the last byte must be the sign extension (equivalently, the value lies in
`[-2 ^ (N-1), 2 ^ (N-1))`). -/
def readS (N : Nat) : DecodeM Int := do
  let rec go (shift fuel : Nat) (acc : Int) : DecodeM Int := do
    match fuel with
    | 0 => throw "decoder: LEB128 too long"
    | fuel + 1 =>
      let b ← readByte
      let acc := acc + ((b.toNat % 0x80 : Nat) : Int) * 2 ^ shift
      if b.toNat < 0x80 then
        if b.toNat ≥ 0x40 then pure (acc - 2 ^ (shift + 7)) else pure acc
      else go (shift + 7) fuel acc
  let i ← go 0 ((N + 6) / 7) 0
  if -(2 ^ (N - 1) : Int) ≤ i ∧ i < 2 ^ (N - 1) then pure i
  else throw "decoder: signed LEB128 out of range"

/-- An index (`u32`). -/
def readIdx {k : IndexKind} : DecodeM (Idx k) := do
  let n ← readU 32
  if h : n < 2 ^ 32 then pure ⟨⟨n, h⟩⟩ else decodeError "index out of range"

/-- A vector count; each element takes at least one byte, so a count above the bytes
left is rejected before anything is allocated. -/
def readCount : DecodeM Nat := do
  let n ← readU 32
  if n ≤ (← remaining) then pure n else decodeError s!"vector count {n} exceeds the input"

/-- A vector of `f`s (bounded loop, no recursion). -/
def readVec {α : Type} (f : DecodeM α) : DecodeM (List α) := do
  let n ← readCount
  let mut acc : Array α := Array.mkEmpty n
  for _ in [0:n] do
    acc := acc.push (← f)
  pure acc.toList

/-- `n` raw bytes. -/
def readBytes (n : Nat) : DecodeM ByteArray := do
  let c ← get
  if c.pos + n ≤ c.bytes.size then
    set { c with pos := c.pos + n }
    pure (c.bytes.extract c.pos (c.pos + n))
  else decodeError s!"{n} bytes requested past the end"

/-- A name: a byte vector holding UTF-8 (the encoder writes `String.toUTF8`). -/
def readName : DecodeM String := do
  let n ← readCount
  let bs ← readBytes n
  match String.fromUTF8? bs with
  | some s => pure s
  | none => decodeError "name is not valid UTF-8"

/-- A non-negative `s33` type index. -/
def readTypeIdxS33 (what : String) : DecodeM TypeIdx := do
  let x ← readS 33
  if h : 0 ≤ x ∧ x.toNat < 2 ^ 32 then pure ⟨⟨x.toNat, h.2⟩⟩
  else decodeError s!"{what} {x} outside the profile"

/-- Heap types (`encHeapType`): an abstract heap type byte or a type index. -/
def readHeapType : DecodeM HeapType := do
  match (← peekByte).bind (fun b => absHeapTypeOf? b.toNat) with
  | some ht => let _ ← readByte; pure (.abstract ht)
  | none => pure (.typeIdx (← readTypeIdxS33 "heap type"))

/-- The cast flags of `br_on_cast(_fail)` (`encCastOp`): bit 0 the source's nullability,
bit 1 the target's. -/
def readCastOp : DecodeM (Bool × Bool) := do
  match (← readByte).toNat with
  | 0 => pure (false, false)
  | 1 => pure (true, false)
  | 2 => pure (false, true)
  | 3 => pure (true, true)
  | n => decodeError s!"cast flags {n} out of range"

/-- Value types of the profile (`encValType`): numeric types, `v128` and references. -/
def readValType : DecodeM ValType := do
  let b ← readByte
  match b.toNat with
  | 0x7F => pure (.num (.int .i32))
  | 0x7E => pure (.num (.int .i64))
  | 0x7D => pure (.num (.float .f32))
  | 0x7C => pure (.num (.float .f64))
  | 0x7B => pure (.vec .v128)
  | 0x63 => pure (.ref ⟨true, ← readHeapType⟩)
  | 0x64 => pure (.ref ⟨false, ← readHeapType⟩)
  | n =>
    match absHeapTypeOf? n with
    | some ht => pure (.ref ⟨true, .abstract ht⟩)
    | none => decodeError s!"value type 0x{String.ofList (Nat.toDigits 16 n)} outside the profile"

/-- Reference types (`encRefType`): the one-byte shorthands and the prefixed forms. -/
def readRefType : DecodeM RefType := do
  match ← readValType with
  | .ref rt => pure rt
  | _ => decodeError "reference type expected"

/-- Block types (`encBlockType`): `0x40`, a value type, or a non-negative `s33`. -/
def readBlockType : DecodeM BlockType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x40 => let _ ← readByte; pure .empty
  | some 0x7F | some 0x7E | some 0x7D | some 0x7C | some 0x7B | some 0x63 | some 0x64 =>
    pure (.value (← readValType))
  | some b =>
    if (absHeapTypeOf? b).isSome then pure (.value (← readValType))
    else pure (.typeIdx (← readTypeIdxS33 "block type"))
  | none => pure (.typeIdx (← readTypeIdxS33 "block type"))

/-- Relational operators in opcode order after `eqz` (inverse of `intRelOff`). -/
def relOps : List IntRelOp :=
  [.eq, .ne, .lt .signed, .lt .unsigned, .gt .signed, .gt .unsigned,
   .le .signed, .le .unsigned, .ge .signed, .ge .unsigned]

/-- Binary operators in opcode order (inverse of `intBinOff`). -/
def binOps : List IntBinOp :=
  [.add, .sub, .mul, .div .signed, .div .unsigned, .rem .signed, .rem .unsigned,
   .and, .or, .xor, .shl, .shr .signed, .shr .unsigned, .rotl, .rotr]

/-- Bit-counting unary operators in opcode order. -/
def unOps : List IntUnOp := [.clz, .ctz, .popcnt]

/-- The opcode `op` falls in the block `[base, base + ops.length)`. -/
def opIn {α : Type} (ops : List α) (base op : Nat) : Option α :=
  if base ≤ op then ops[op - base]? else none

/-- A single-memory argument with a Core 3.0 `u64` offset. -/
def readMemArg : DecodeM MemArg := do
  let align ← readU 32
  unless align < 64 do decodeError "explicit memory indices are not supported"
  let offset ← readU 64
  if ha : align < 2 ^ 32 then
    if ho : offset < 2 ^ 64 then pure ⟨⟨align, ha⟩, ⟨offset, ho⟩⟩
    else decodeError "memory offset out of range"
  else decodeError "memory alignment out of range"

/-- All indexed memory operands use the existing Core grammar reader. The public
single-memory `readMemArg` remains available unchanged; actual scalar and SIMD
instructions use this pair so explicit memory indices cannot be discarded. -/
def readIndexedMemArg : DecodeM (MemIdx × MemArg) := fun cursor =>
  match Binary.Core.Decode.readMemArg.run ⟨cursor.bytes, cursor.pos⟩ with
  | .error error => .error error
  | .ok (argument, next) => .ok (argument, ⟨next.bytes, next.pos⟩)

/-- Read a scalar or SIMD memory instruction without restricting its memory index. -/
def readMemInstr (mk : MemIdx → MemArg → Instr) : DecodeM Instr := do
  let (memory, argument) ← readIndexedMemArg
  pure (mk memory argument)

/-- The ordinary `u32` memory index for size, grow and bulk-memory instructions. -/
def readMemoryIdx : DecodeM MemIdx := readIdx

/-- Fixed-width floating-point bits, without conversion through a host float. -/
def readFloatBits (t : FloatType) : DecodeM (BitVec t.width) := do
  let bs ← readBytes (t.width / 8)
  pure (BitVec.ofNat t.width (Binary.littleEndian bs.data.toList))

def floatUnOps : List FloatUnOp := [.abs, .neg, .ceil, .floor, .trunc, .nearest, .sqrt]
def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]

/-- The `0xFD` opcodes other than `v128.const` and `i8x16.shuffle`, read from the Core
grammar's opcode tables (inverse of `encSIMDInstr`), retaining explicit vector
memory indices. -/
def readFD (n : Nat) : DecodeM Instr := do
  match Binary.Core.prefixFDOp? n with
  | some i => pure i
  | none =>
  match Binary.Core.vecMemOp? n with
  | some mk => readMemInstr mk
  | none =>
  match Binary.Core.vecMemLaneOp? n with
  | some mk => do
    let (memory, argument) ← readIndexedMemArg
    pure (mk memory argument (Binary.Core.laneOf (← readByte)))
  | none =>
  match Binary.Core.vecLaneOp? n with
  | some mk => pure (mk (Binary.Core.laneOf (← readByte)))
  | none => decodeError s!"0xfd opcode {n} outside the profile"

/-- Non-structured instructions (inverse of the leaf cases of `encInstr`). -/
def readPlain (op : Nat) : DecodeM Instr := do
  match op with
  | 0x00 => pure .unreachable
  | 0x01 => pure .nop
  | 0x08 => pure (.throw (← readIdx))
  | 0x0A => pure .throwRef
  | 0x0C => pure (.br (← readIdx))
  | 0x0D => pure (.brIf (← readIdx))
  | 0x0E =>
    let ls ← readVec readIdx
    let l ← readIdx
    pure (.brTable ls l)
  | 0x0F => pure .return_
  | 0x10 => pure (.call (← readIdx))
  | 0x11 => do
    let y ← readIdx
    let x ← readIdx
    pure (.callIndirect x y)
  | 0x12 => pure (.returnCall (← readIdx))
  | 0x13 => do
    let y ← readIdx
    let x ← readIdx
    pure (.returnCallIndirect x y)
  | 0x14 => pure (.callRef (← readIdx))
  | 0x15 => pure (.returnCallRef (← readIdx))
  | 0x1A => pure .drop
  | 0x1B => pure (.select none)
  | 0xD0 => pure (.refNull (← readHeapType))
  | 0xD1 => pure .refIsNull
  | 0xD2 => pure (.refFunc (← readIdx))
  | 0x20 => pure (.localGet (← readIdx))
  | 0x21 => pure (.localSet (← readIdx))
  | 0x22 => pure (.localTee (← readIdx))
  | 0x23 => pure (.globalGet (← readIdx))
  | 0x24 => pure (.globalSet (← readIdx))
  | 0x25 => pure (.tableGet (← readIdx))
  | 0x26 => pure (.tableSet (← readIdx))
  | 0x28 => readMemInstr (.intLoad .i32 none)
  | 0x29 => readMemInstr (.intLoad .i64 none)
  | 0x2A => readMemInstr (.floatLoad .f32)
  | 0x2B => readMemInstr (.floatLoad .f64)
  | 0x2C => readMemInstr (.intLoad .i32 (some (.i8, .signed)))
  | 0x2D => readMemInstr (.intLoad .i32 (some (.i8, .unsigned)))
  | 0x2E => readMemInstr (.intLoad .i32 (some (.i16, .signed)))
  | 0x2F => readMemInstr (.intLoad .i32 (some (.i16, .unsigned)))
  | 0x30 => readMemInstr (.intLoad .i64 (some (.i8, .signed)))
  | 0x31 => readMemInstr (.intLoad .i64 (some (.i8, .unsigned)))
  | 0x32 => readMemInstr (.intLoad .i64 (some (.i16, .signed)))
  | 0x33 => readMemInstr (.intLoad .i64 (some (.i16, .unsigned)))
  | 0x34 => readMemInstr (.intLoad .i64 (some (.i32, .signed)))
  | 0x35 => readMemInstr (.intLoad .i64 (some (.i32, .unsigned)))
  | 0x36 => readMemInstr (.intStore .i32 none)
  | 0x37 => readMemInstr (.intStore .i64 none)
  | 0x38 => readMemInstr (.floatStore .f32)
  | 0x39 => readMemInstr (.floatStore .f64)
  | 0x3A => readMemInstr (.intStore .i32 (some .i8))
  | 0x3B => readMemInstr (.intStore .i32 (some .i16))
  | 0x3C => readMemInstr (.intStore .i64 (some .i8))
  | 0x3D => readMemInstr (.intStore .i64 (some .i16))
  | 0x3E => readMemInstr (.intStore .i64 (some .i32))
  | 0x3F => pure (.memorySize (← readMemoryIdx))
  | 0x40 => pure (.memoryGrow (← readMemoryIdx))
  | 0x41 => do let v ← readS 32; pure (.intConst .i32 (BitVec.ofInt 32 v))
  | 0x42 => do let v ← readS 64; pure (.intConst .i64 (BitVec.ofInt 64 v))
  | 0x43 => pure (.floatConst .f32 (← readFloatBits .f32))
  | 0x44 => pure (.floatConst .f64 (← readFloatBits .f64))
  | 0x45 => pure (.intTestOp .i32 .eqz)
  | 0x50 => pure (.intTestOp .i64 .eqz)
  | 0xA7 => pure (.convert .wrap)
  | 0xA8 => pure (.convert (.trunc .f32 .i32 .signed))
  | 0xA9 => pure (.convert (.trunc .f32 .i32 .unsigned))
  | 0xAA => pure (.convert (.trunc .f64 .i32 .signed))
  | 0xAB => pure (.convert (.trunc .f64 .i32 .unsigned))
  | 0xAC => pure (.convert (.extend .signed))
  | 0xAD => pure (.convert (.extend .unsigned))
  | 0xAE => pure (.convert (.trunc .f32 .i64 .signed))
  | 0xAF => pure (.convert (.trunc .f32 .i64 .unsigned))
  | 0xB0 => pure (.convert (.trunc .f64 .i64 .signed))
  | 0xB1 => pure (.convert (.trunc .f64 .i64 .unsigned))
  | 0xB2 => pure (.convert (.convert .i32 .f32 .signed))
  | 0xB3 => pure (.convert (.convert .i32 .f32 .unsigned))
  | 0xB4 => pure (.convert (.convert .i64 .f32 .signed))
  | 0xB5 => pure (.convert (.convert .i64 .f32 .unsigned))
  | 0xB6 => pure (.convert .demote)
  | 0xB7 => pure (.convert (.convert .i32 .f64 .signed))
  | 0xB8 => pure (.convert (.convert .i32 .f64 .unsigned))
  | 0xB9 => pure (.convert (.convert .i64 .f64 .signed))
  | 0xBA => pure (.convert (.convert .i64 .f64 .unsigned))
  | 0xBB => pure (.convert .promote)
  | 0xBC => pure (.convert (.reinterpretInt .f32))
  | 0xBD => pure (.convert (.reinterpretInt .f64))
  | 0xBE => pure (.convert (.reinterpretFloat .i32))
  | 0xBF => pure (.convert (.reinterpretFloat .i64))
  | 0xC0 => pure (.intUnOp .i32 (.extend .i8))
  | 0xC1 => pure (.intUnOp .i32 (.extend .i16))
  | 0xC2 => pure (.intUnOp .i64 (.extend .i8))
  | 0xC3 => pure (.intUnOp .i64 (.extend .i16))
  | 0xC4 => pure (.intUnOp .i64 (.extend .i32))
  | 0xFD =>
    let n ← readU 32
    match n with
    | 12 =>
      let bs ← readBytes 16
      pure (.vecConst (BitVec.ofNat 128 (Binary.littleEndian bs.data.toList)))
    | 13 =>
      let ls ← readBytes 16
      pure (.vecShuffle (ls.data.toList.map Binary.Core.laneOf))
    | _ => readFD n
  | 0x1C => pure (.select (some (← readVec readValType)))
  | 0xD3 => pure .refEq
  | 0xD4 => pure .refAsNonNull
  | 0xD5 => pure (.brOnNull (← readIdx))
  | 0xD6 => pure (.brOnNonNull (← readIdx))
  | 0xFB =>
    let n ← readU 32
    match n with
    | 0 => pure (.structNew (← readIdx))
    | 1 => pure (.structNewDefault (← readIdx))
    | 2 => do let x ← readIdx; pure (.structGet none x (← readIdx))
    | 3 => do let x ← readIdx; pure (.structGet (some .signed) x (← readIdx))
    | 4 => do let x ← readIdx; pure (.structGet (some .unsigned) x (← readIdx))
    | 5 => do let x ← readIdx; pure (.structSet x (← readIdx))
    | 6 => pure (.arrayNew (← readIdx))
    | 7 => pure (.arrayNewDefault (← readIdx))
    | 8 => do
      let x ← readIdx
      let k ← readU 32
      if h : k < 2 ^ 32 then pure (.arrayNewFixed x ⟨k, h⟩)
      else decodeError "array.new_fixed length out of range"
    | 9 => do let x ← readIdx; pure (.arrayNewData x (← readIdx))
    | 10 => do let x ← readIdx; pure (.arrayNewElem x (← readIdx))
    | 11 => pure (.arrayGet none (← readIdx))
    | 12 => pure (.arrayGet (some .signed) (← readIdx))
    | 13 => pure (.arrayGet (some .unsigned) (← readIdx))
    | 14 => pure (.arraySet (← readIdx))
    | 15 => pure .arrayLen
    | 16 => pure (.arrayFill (← readIdx))
    | 17 => do let x ← readIdx; pure (.arrayCopy x (← readIdx))
    | 18 => do let x ← readIdx; pure (.arrayInitData x (← readIdx))
    | 19 => do let x ← readIdx; pure (.arrayInitElem x (← readIdx))
    | 20 => pure (.refTest ⟨false, ← readHeapType⟩)
    | 21 => pure (.refTest ⟨true, ← readHeapType⟩)
    | 22 => pure (.refCast ⟨false, ← readHeapType⟩)
    | 23 => pure (.refCast ⟨true, ← readHeapType⟩)
    | 24 => do
      let (n₁, n₂) ← readCastOp
      let l ← readIdx
      let h₁ ← readHeapType
      pure (.brOnCast l ⟨n₁, h₁⟩ ⟨n₂, ← readHeapType⟩)
    | 25 => do
      let (n₁, n₂) ← readCastOp
      let l ← readIdx
      let h₁ ← readHeapType
      pure (.brOnCastFail l ⟨n₁, h₁⟩ ⟨n₂, ← readHeapType⟩)
    | 26 => pure .anyConvertExtern
    | 27 => pure .externConvertAny
    | 28 => pure .refI31
    | 29 => pure (.i31Get .signed)
    | 30 => pure (.i31Get .unsigned)
    | _ => decodeError s!"0xfb opcode {n} outside the profile"
  | 0xFC =>
    let n ← readU 32
    match n with
    | 0 => pure (.convert (.truncSat .f32 .i32 .signed))
    | 1 => pure (.convert (.truncSat .f32 .i32 .unsigned))
    | 2 => pure (.convert (.truncSat .f64 .i32 .signed))
    | 3 => pure (.convert (.truncSat .f64 .i32 .unsigned))
    | 4 => pure (.convert (.truncSat .f32 .i64 .signed))
    | 5 => pure (.convert (.truncSat .f32 .i64 .unsigned))
    | 6 => pure (.convert (.truncSat .f64 .i64 .signed))
    | 7 => pure (.convert (.truncSat .f64 .i64 .unsigned))
    | 8 =>
      let d ← readIdx
      pure (.memoryInit (← readMemoryIdx) d)
    | 9 => pure (.dataDrop (← readIdx))
    | 10 =>
      let dst ← readMemoryIdx
      pure (.memoryCopy dst (← readMemoryIdx))
    | 11 => pure (.memoryFill (← readMemoryIdx))
    | 12 =>
      let e ← readIdx
      pure (.tableInit (← readIdx) e)
    | 13 => pure (.elemDrop (← readIdx))
    | 14 =>
      let dst ← readIdx
      pure (.tableCopy dst (← readIdx))
    | 15 => pure (.tableGrow (← readIdx))
    | 16 => pure (.tableSize (← readIdx))
    | 17 => pure (.tableFill (← readIdx))
    | _ => decodeError s!"0xfc opcode {n} outside the profile"
  | op =>
    if let some o := opIn relOps 0x46 op then pure (.intRelOp .i32 o)
    else if let some o := opIn relOps 0x51 op then pure (.intRelOp .i64 o)
    else if let some o := opIn unOps 0x67 op then pure (.intUnOp .i32 o)
    else if let some o := opIn binOps 0x6A op then pure (.intBinOp .i32 o)
    else if let some o := opIn unOps 0x79 op then pure (.intUnOp .i64 o)
    else if let some o := opIn binOps 0x7C op then pure (.intBinOp .i64 o)
    else if let some o := opIn floatRelOps 0x5B op then pure (.floatRelOp .f32 o)
    else if let some o := opIn floatRelOps 0x61 op then pure (.floatRelOp .f64 o)
    else if let some o := opIn floatUnOps 0x8B op then pure (.floatUnOp .f32 o)
    else if let some o := opIn floatUnOps 0x99 op then pure (.floatUnOp .f64 o)
    else if let some o := opIn floatBinOps 0x92 op then pure (.floatBinOp .f32 o)
    else if let some o := opIn floatBinOps 0xA0 op then pure (.floatBinOp .f64 o)
    else decodeError s!"opcode 0x{String.ofList (Nat.toDigits 16 op)} outside the profile"

/-- A `try_table` catch clause (`encCatch`). -/
def readCatch : DecodeM Catch := do
  match (← readByte).toNat with
  | 0x00 =>
    let x ← readIdx
    pure (.catch_ x (← readIdx))
  | 0x01 =>
    let x ← readIdx
    pure (.catchRef x (← readIdx))
  | 0x02 => pure (.catchAll (← readIdx))
  | 0x03 => pure (.catchAllRef (← readIdx))
  | k => decodeError s!"catch kind {k} outside the profile"

mutual
/-- One instruction whose opcode `op` has been read. Structural on `fuel`. -/
def readInstr (fuel : Nat) (op : Nat) : DecodeM Instr :=
  match fuel with
  | 0 => decodeError "out of fuel"
  | fuel + 1 =>
    match op with
    | 0x02 => do
      let bt ← readBlockType
      let (body, t) ← readSeq fuel
      if t == 0x0B then pure (.block bt body) else decodeError "`else` inside `block`"
    | 0x03 => do
      let bt ← readBlockType
      let (body, t) ← readSeq fuel
      if t == 0x0B then pure (.loop bt body) else decodeError "`else` inside `loop`"
    | 0x04 => do
      let bt ← readBlockType
      let (thn, t) ← readSeq fuel
      if t == 0x0B then pure (.if_ bt thn [])
      else
        let (els, t') ← readSeq fuel
        if t' == 0x0B then pure (.if_ bt thn els) else decodeError "second `else` in `if`"
    | 0x1F => do
      let bt ← readBlockType
      let cs ← readVec readCatch
      let (body, t) ← readSeq fuel
      if t == 0x0B then pure (.tryTable bt cs body) else decodeError "`else` inside `try_table`"
    | op => readPlain op
/-- Instructions up to and including a terminator (`end` 0x0B or `else` 0x05), which
is returned. Structural on `fuel`. -/
def readSeq (fuel : Nat) : DecodeM (List Instr × UInt8) :=
  match fuel with
  | 0 => decodeError "out of fuel"
  | fuel + 1 => do
    let b ← readByte
    if b == 0x0B || b == 0x05 then pure ([], b)
    else
      let i ← readInstr fuel b.toNat
      let (rest, t) ← readSeq fuel
      pure (i :: rest, t)
end

/-- An expression: instructions, then `end` (`encExpr`). -/
def readExpr : DecodeM Expr := do
  let (is, t) ← readSeq ((← remaining) + 1)
  if t == 0x0B then pure is else decodeError "`else` outside `if`"

/-- An implementation limit on the locals of one function (wasm-tools and V8 use the
same bound); the format allows `2 ^ 32 - 1`, which would exhaust memory on
`List.replicate`. -/
def maxLocals : Nat := 50000

/-- A field (`encFieldType`): a storage type, then a mutability. -/
def readFieldType : DecodeM FieldType := do
  let z ← match (← peekByte).map UInt8.toNat with
    | some 0x78 => do let _ ← readByte; pure (StorageType.packed .i8)
    | some 0x77 => do let _ ← readByte; pure (StorageType.packed .i16)
    | _ => pure (StorageType.val (← readValType))
  let m ← match (← readByte).toNat with
    | 0x00 => pure Mutability.const
    | 0x01 => pure Mutability.var
    | _ => decodeError "bad field mutability"
  pure ⟨m, z⟩

/-- A composite type (`encCompType`) whose form byte `b` has been read. -/
def readCompType (b : UInt8) : DecodeM CompositeType := do
  match b.toNat with
  | 0x60 =>
    let params ← readVec readValType
    let results ← readVec readValType
    pure (.func ⟨params, results⟩)
  | 0x5F => pure (.struct (← readVec readFieldType))
  | 0x5E => pure (.array (← readFieldType))
  | n => decodeError s!"type form 0x{String.ofList (Nat.toDigits 16 n)} outside the profile"

/-- A sub type (`encSubType`): `0x4F`/`0x50` with supertypes, or a bare composite
type (final, no supertypes). -/
def readSubType : DecodeM SubType := do
  let b ← readByte
  match b.toNat with
  | 0x4F => do
    let xs ← readVec readIdx
    pure ⟨true, xs, ← readCompType (← readByte)⟩
  | 0x50 => do
    let xs ← readVec readIdx
    pure ⟨false, xs, ← readCompType (← readByte)⟩
  | _ => pure ⟨true, [], ← readCompType b⟩

/-- A type-section entry (`encRecType`): a `0x4E` group, or a single sub type. -/
def readRecType : DecodeM RecType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x4E => do let _ ← readByte; pure ⟨← readVec readSubType⟩
  | _ => pure ⟨[← readSubType]⟩

/-- A global type: value type and mutability (`encGlobal`, `encImport`). -/
def readGlobalType : DecodeM GlobalType := do
  let t ← readValType
  let m ← match (← readByte).toNat with
    | 0x00 => pure Mutability.const
    | 0x01 => pure Mutability.var
    | _ => decodeError "bad global mutability"
  pure ⟨m, t⟩

/-- An i32 or i64 memory type with optional maximum (`encMemory`). As in Core
3.0, both address types use `u64` bounds; validity is checked separately. -/
def readMemory : DecodeM MemoryType := do
  let flag ← readByte
  unless flag == 0 || flag == 1 || flag == 4 || flag == 5 do
    decodeError "memory limits outside the fragment"
  let address := if flag.toNat < 4 then AddrType.i32 else .i64
  let lo ← readU 64
  let hi ← if flag.toNat % 2 == 1 then pure (some (← readU 64)) else pure none
  if hlo : lo < 2 ^ 64 then
    match hi with
    | none => pure ⟨address, ⟨lo, hlo⟩, none⟩
    | some hi =>
      if hhi : hi < 2 ^ 64 then pure ⟨address, ⟨lo, hlo⟩, some ⟨hi, hhi⟩⟩
      else decodeError "memory maximum out of range"
  else decodeError "memory minimum out of range"

/-- A table type: a reference type, then the same limits syntax as memories. -/
def readTableType : DecodeM TableType := do
  let rt ← readRefType
  let limits ← readMemory
  pure ⟨limits.address, limits.limits, rt⟩

/-- A defined table with an implicit null or explicit `0x40 0x00` initializer. -/
def readTable : DecodeM Table := do
  if (← peekByte) == some 0x40 then
    let _ ← readByte
    unless (← readByte) == 0x00 do decodeError "bad table initializer prefix"
    let tt ← readTableType
    pure ⟨tt, ← readExpr⟩
  else
    let tt ← readTableType
    pure ⟨tt, [.refNull tt.element.heap]⟩

/-- A tag type: the exception attribute and a function type index (`encTagType`). -/
def readTagType : DecodeM TagType := do
  unless (← readByte) == 0x00 do decodeError "tag attribute outside the profile"
  readIdx

/-- A function, table, memory, global or tag import (`encImport`). -/
def readImport : DecodeM Import := do
  let moduleName ← readName
  let name ← readName
  match (← readByte).toNat with
  | 0x00 => pure ⟨moduleName, name, .func (← readIdx)⟩
  | 0x02 => pure ⟨moduleName, name, .memory (← readMemory)⟩
  | 0x03 => pure ⟨moduleName, name, .global (← readGlobalType)⟩
  | 0x01 => pure ⟨moduleName, name, .table (← readTableType)⟩
  | 0x04 => pure ⟨moduleName, name, .tag (← readTagType)⟩
  | _ => decodeError s!"import {moduleName}.{name} is outside the profile"

/-- A function-index segment or an expression segment of any reference type, kinds 0–7
(`encElem`). -/
def readElem : DecodeM Elem := do
  let kind ← readU 32
  let rt : RefType := ⟨false, .abstract .func⟩
  let elemKind : DecodeM Unit := do
    unless (← readByte) == 0x00 do decodeError "element kind outside the profile"
  let funcs : DecodeM (List Expr) := do
    let ys ← readVec (readIdx (k := .func))
    pure (ys.map fun y => [.refFunc y])
  match kind with
  | 0 =>
    let off ← readExpr
    pure ⟨rt, ← funcs, .active ⟨0⟩ off⟩
  | 1 =>
    elemKind
    pure ⟨rt, ← funcs, .passive⟩
  | 2 =>
    let x ← readIdx
    let off ← readExpr
    elemKind
    pure ⟨rt, ← funcs, .active x off⟩
  | 3 =>
    elemKind
    pure ⟨rt, ← funcs, .declarative⟩
  | 4 =>
    let off ← readExpr
    pure ⟨⟨true, .abstract .func⟩, ← readVec readExpr, .active ⟨0⟩ off⟩
  | 5 =>
    let rt ← readRefType
    pure ⟨rt, ← readVec readExpr, .passive⟩
  | 6 =>
    let x ← readIdx
    let off ← readExpr
    let rt ← readRefType
    pure ⟨rt, ← readVec readExpr, .active x off⟩
  | 7 =>
    let rt ← readRefType
    pure ⟨rt, ← readVec readExpr, .declarative⟩
  | k => decodeError s!"element segment kind {k} outside the profile"

/-- A global (`encGlobal`). -/
def readGlobal : DecodeM Global := do
  let gt ← readGlobalType
  let init ← readExpr
  pure ⟨gt, init⟩

/-- A function, table, memory, global or tag export (`encExport`). -/
def readExport : DecodeM Export := do
  let name ← readName
  match (← readByte).toNat with
  | 0x00 => pure ⟨name, .func (← readIdx)⟩
  | 0x01 => pure ⟨name, .table (← readIdx)⟩
  | 0x02 => pure ⟨name, .memory (← readIdx)⟩
  | 0x03 => pure ⟨name, .global (← readIdx)⟩
  | 0x04 => pure ⟨name, .tag (← readIdx)⟩
  | _ => decodeError s!"export {name} is outside the profile"

/-- An implementation limit on the data segments of a module (V8 and wasm-tools use
the same bound); engines reject larger modules, so the decoder passes them through. -/
def maxDataSegments : Nat := 100000

/-- A byte vector: a count, then that many raw bytes. -/
def readByteVec : DecodeM ByteArray := do
  readBytes (← readCount)

/-- A data segment (`encData`): kind `0` (active in memory 0), `1` (passive) or `2`
(active, explicit memory index). -/
def readData : DecodeM Data := do
  match ← readU 32 with
  | 0 =>
    let e ← readExpr
    pure ⟨← readByteVec, .active ⟨0⟩ e⟩
  | 1 => pure ⟨← readByteVec, .passive⟩
  | 2 =>
    let x ← readIdx
    let e ← readExpr
    pure ⟨← readByteVec, .active x e⟩
  | k => decodeError s!"data segment kind {k} outside the fragment"

/-- A code entry (`encCode`): its size, locals groups (expanded), the body. -/
def readCode : DecodeM (List ValType × Expr) := do
  let size ← readU 32
  let start := (← get).pos
  unless size ≤ (← remaining) do decodeError "code entry past the end"
  let groups ← readVec do
    let n ← readU 32
    let t ← readValType
    pure (n, t)
  let total := groups.foldl (fun s p => s + p.1) 0
  unless total ≤ maxLocals do decodeError s!"{total} locals exceed the limit {maxLocals}"
  let locals := groups.flatMap fun p => List.replicate p.1 p.2
  let body ← readExpr
  unless (← get).pos == start + size do decodeError "code entry size mismatch"
  pure (locals, body)

/-- The sections of the fragment, as read. -/
structure Sections where
  types : List RecType := []
  imports : List Import := []
  funcTypes : List TypeIdx := []
  tables : List Table := []
  memories : List MemoryType := []
  tags : List TagType := []
  globals : List Global := []
  exports : List Export := []
  start : Option FuncIdx := none
  elems : List Elem := []
  code : List (List ValType × Expr) := []
  data : List Data := []
  dataCount : Option Nat := none

/-- The contents of a supported section (1–13). -/
def readSectionBody (id : Nat) (s : Sections) : DecodeM Sections := do
  match id with
  | 1 => pure { s with types := ← readVec readRecType }
  | 2 => pure { s with imports := ← readVec readImport }
  | 3 => pure { s with funcTypes := ← readVec readIdx }
  | 4 => pure { s with tables := ← readVec readTable }
  | 5 => pure { s with memories := ← readVec readMemory }
  | 13 => pure { s with tags := ← readVec readTagType }
  | 6 => pure { s with globals := ← readVec readGlobal }
  | 7 => pure { s with exports := ← readVec readExport }
  | 8 => pure { s with start := some (← readIdx) }
  | 9 => pure { s with elems := ← readVec readElem }
  | 10 => pure { s with code := ← readVec readCode }
  | 11 =>
    let data ← readVec readData
    unless data.length ≤ maxDataSegments do
      decodeError s!"{data.length} data segments exceed the limit {maxDataSegments}"
    pure { s with data := data }
  | 12 =>
    let n ← readU 32
    unless n ≤ maxDataSegments do
      decodeError s!"data count {n} exceeds the limit {maxDataSegments}"
    pure { s with dataCount := some n }
  | _ => decodeError s!"section {id} outside the fragment"

/-- The position of a section in binary order: tags (13) come between memories (5)
and globals (6); data count (12) comes between elements (9) and code (10). -/
def sectionRank (id : Nat) : Nat :=
  if id == 13 then 6 else if id == 12 then 11
  else if id ≥ 6 && id ≤ 9 then id + 1
  else if id == 10 || id == 11 then id + 2 else id

/-- The module header (`header`). -/
def readHeader : DecodeM Unit := do
  let h ← readBytes 8
  unless h.data.toList == header do decodeError "bad magic or version"

/-- The decoder proper. -/
def readModule : DecodeM Module := do
  readHeader
  let mut s : Sections := {}
  let mut last := 0
  for _ in [0:(← get).bytes.size] do
    if (← remaining) == 0 then break
    let id := (← readByte).toNat
    let size ← readU 32
    unless size ≤ (← remaining) do decodeError s!"section {id} past the end"
    let start := (← get).pos
    if id == 0 then
      -- custom section: skipped
      let _ ← readBytes size
    else
      unless last < sectionRank id do decodeError s!"section {id} out of order or repeated"
      last := sectionRank id
      s ← readSectionBody id s
      unless (← get).pos == start + size do decodeError s!"section {id} size mismatch"
  unless s.funcTypes.length == s.code.length do
    decodeError s!"{s.funcTypes.length} function declarations but {s.code.length} bodies"
  pure {
    types := s.types
    imports := s.imports
    tables := s.tables
    memories := s.memories
    tags := s.tags
    globals := s.globals
    funcs := List.zipWith (fun t (c : List ValType × Expr) => ⟨t, c.1, c.2⟩) s.funcTypes s.code
    data := s.data
    start := s.start
    elems := s.elems
    exports := s.exports }

/-- **The decoder** for the encoder's fragment (milestone D1). -/
def decodeModule (b : ByteArray) : Except String Module :=
  readModule.run' ⟨b, 0⟩

/-- Drop custom sections (id 0), which carry no abstract syntax (milestone D2). The
other sections are copied verbatim, with their original size encodings. Input that
does not parse as a header and a sequence of sections is returned unchanged. -/
def stripCustom (b : ByteArray) : ByteArray :=
  match go.run' ⟨b, 0⟩ with
  | .ok r => r
  | .error _ => b
where
  go : DecodeM ByteArray := do
    readHeader
    let mut out := b.extract 0 8
    for _ in [0:b.size] do
      if (← remaining) == 0 then break
      let start := (← get).pos
      let id ← readByte
      let size ← readU 32
      let _ ← readBytes size
      if id != 0 then out := out ++ b.extract start (← get).pos
    pure out

/-! ## Round-trip check and policy (milestone D3) -/

/-- How the re-encoding of a decoded module compares with the input. -/
inductive RoundTrip where
  /-- `encodeModule? m = .ok input` (`decode_checked`), or the padded encoding
  `encodeModuleP? h m = .ok input` (`encodeModuleP?_sound`): `Encodes input m`. -/
  | exact
  /-- Equal once custom sections are removed from the input. -/
  | customStripped
  /-- The bytes first differ at `offset` (of the custom-stripped input). -/
  | mismatch (offset : Nat)
  /-- The encoder rejected the decoded module. -/
  | encodeFailed (reason : String)
  deriving Repr, DecidableEq

/-- The policy: optimise only after an exact or custom-stripped round trip. -/
def RoundTrip.trusted : RoundTrip → Bool
  | .exact | .customStripped => true
  | _ => false

def RoundTrip.describe : RoundTrip → String
  | .exact => "exact"
  | .customStripped => "exact after removing custom sections"
  | .mismatch o => s!"re-encoding differs from the input at byte {o}"
  | .encodeFailed e => s!"re-encoding failed: {e}"

/-- First index at which two byte lists differ (the shorter length if one is a
prefix of the other). -/
def firstDiff : List UInt8 → List UInt8 → Nat → Nat
  | a :: as, b :: bs, i => if a == b then firstDiff as bs (i + 1) else i
  | _, _, i => i

/-- Compare the re-encoding of `m` with `input`: first the canonical encoding, then
the padded encoding (`encodeModuleP?`) with the LEB128 widths of the custom-stripped
input, which admits linker output with padded relocation LEBs. Both encoders are
certified, so either equality gives `Encodes`. -/
def checkRoundTrip (input : ByteArray) (m : Module) : RoundTrip :=
  match encodeModule? m with
  | .error e => .encodeFailed e
  | .ok bs =>
    if bs == input.data.toList then .exact
    else
      let stripped := stripCustom input
      if bs == stripped.data.toList then .customStripped
      else
        match encodeModuleP? stripped m with
        | .ok ps =>
          if ps == input.data.toList then .exact
          else if ps == stripped.data.toList then .customStripped
          else .mismatch (firstDiff bs stripped.data.toList 0)
        | .error _ => .mismatch (firstDiff bs stripped.data.toList 0)

/-- Decode and check: the module and the round-trip verdict. The driver should
optimise only when `(decodeChecked input).map (·.2.trusted)` is `.ok true` and pass
the input through otherwise. -/
def decodeChecked (input : ByteArray) : Except String (Module × RoundTrip) := do
  let m ← decodeModule input
  pure (m, checkRoundTrip input m)

end Silmaril.Wasm.Binaryen.Exe
