module

public import Silmaril.Wasm.Binary.Core.Modules

@[expose] public section

/-! # An executable decoder for the Core 3.0 binary format

`decode? : ByteArray → Option Wasm.Module` is meant to be **sound** against the
specification's grammar `Encodes` (`Modules.lean`):

```
decode?_sound : decode? b = some m → Encodes b.data.toList m      (DecodeSound.lean)
```

Together with the functionality of the grammar (`Binary.Core.functional`), soundness
says that `m` is *the* module that `b` encodes, with no runtime round-trip check.

## Starting point

The decoder is a copy of the untrusted front end of `binaryen-lean`
(`Silmaril/Wasm/Binaryen/Exe/Decode.lean`, `decodeModule`), so it covers exactly the
Binaryen profile (the image of `encodeModule?`) from the start:

* the header `\0asm` version 1; custom sections anywhere;
* section 1 (types): `0x60` function types, each a singleton final group;
* section 2 (imports): function imports; sections 3 and 10 (functions and code), zipped;
* sections 6 (globals), 7 (function and global exports), 8 (start);
* value types `i32`/`i64`; block types `0x40`, a value type, or a non-negative `s33`;
* the scalar integer instructions of `encInstr`, `block`/`loop`/`if`, branches, calls,
  locals and globals.

Beyond the profile: memories and data (sections 5, 11 and 12 in the Core 3.0 section
order, memory imports and exports, limits with 32- and 64-bit addresses, loads and
stores through `memOp?` with a `memarg`, `memory.size/grow/init/copy/fill`, `data.drop`).

Also supported: table imports/exports, section 4 (including explicit initializers),
element segment kinds 0–7, call_indirect and table instructions, ref.null/ref.is_null/ref.func.

One change from the copy, needed for soundness: a custom section must begin with a
valid `name` that fits in the section (`Custom` in `Basic.lean`); the copy skipped its
bytes unchecked.

Everything here may be rewritten to make the proofs easier or to cover more of
Core 3.0 (the statement of `decode?_sound` and the signature of `decode?` are fixed).
Recursion over instructions is structural on a fuel argument equal to the input size
(each nested call consumes a byte first); vectors recurse on their checked count and
sections on fuel equal to the input size. No `partial` definitions.
-/

namespace Silmaril.Wasm.Binary.Core.Decode

open Silmaril.Wasm

/-- Decoder state: the input and a position. -/
structure Cursor where
  bytes : ByteArray
  pos : Nat

/-- The decoding monad. -/
abbrev DecodeM := StateT Cursor (Except String)

/-- The bytes from the cursor to the end of the input. -/
def Cursor.rest (c : Cursor) : List UInt8 := c.bytes.data.toList.drop c.pos

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

/-- A vector of `f`s, using structural recursion on the checked count. -/
def readVec {α : Type} (f : DecodeM α) : DecodeM (List α) := do
  let rec go : Nat → DecodeM (List α)
    | 0 => pure []
    | n + 1 => do
      let x ← f
      let xs ← go n
      pure (x :: xs)
  go (← readCount)

/-- `n` raw bytes. -/
def readBytes (n : Nat) : DecodeM ByteArray := do
  let c ← get
  if c.pos + n ≤ c.bytes.size then
    set { c with pos := c.pos + n }
    pure (c.bytes.extract c.pos (c.pos + n))
  else decodeError s!"{n} bytes requested past the end"

/-- A name: a byte vector holding UTF-8. -/
def readName : DecodeM String := do
  let n ← readCount
  let bs ← readBytes n
  match String.fromUTF8? bs with
  | some s => pure s
  | none => decodeError "name is not valid UTF-8"

/-- Reference types: abstract shorthands, or a nullable/non-null prefix and a heap type. -/
def readRefType : DecodeM Wasm.RefType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x63 =>
    let _ ← readByte
    pure ⟨true, ← heapType⟩
  | some 0x64 =>
    let _ ← readByte
    pure ⟨false, ← heapType⟩
  | _ => pure ⟨true, .abstract (← absHeapType)⟩
where
  absHeapType : DecodeM Wasm.AbsHeapType := do
    match (← readByte).toNat with
    | 0x69 => pure .exn
    | 0x6A => pure .array
    | 0x6B => pure .struct
    | 0x6C => pure .i31
    | 0x6D => pure .eq
    | 0x6E => pure .any
    | 0x6F => pure .extern
    | 0x70 => pure .func
    | 0x71 => pure .none
    | 0x72 => pure .noextern
    | 0x73 => pure .nofunc
    | 0x74 => pure .noexn
    | _ => decodeError "bad abstract heap type"
  heapType : DecodeM Wasm.HeapType := do
    match (← peekByte).map UInt8.toNat with
    | some n =>
      if 0x69 ≤ n ∧ n ≤ 0x74 then pure (.abstract (← absHeapType))
      else
        let x ← readS 33
        if h : 0 ≤ x ∧ x.toNat < 2 ^ 32 then pure (.typeIdx ⟨⟨x.toNat, h.2⟩⟩)
        else decodeError "heap type index out of range"
    | none => decodeError "missing heap type"

/-- Number and reference value types. -/
def readValType : DecodeM Wasm.ValType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x7F => let _ ← readByte; pure (.num (.int .i32))
  | some 0x7E => let _ ← readByte; pure (.num (.int .i64))
  | some 0x7D => let _ ← readByte; pure (.num (.float .f32))
  | some 0x7C => let _ ← readByte; pure (.num (.float .f64))
  | some 0x7B => let _ ← readByte; pure (.vec .v128)
  | _ => pure (.ref (← readRefType))

/-- Block types: `0x40`, a supported value type, or a non-negative `s33`. -/
def readBlockType : DecodeM Wasm.BlockType := do
  let b ← peekByte
  if b == some 0x40 then
    let _ ← readByte
    pure .empty
  else if (b.map UInt8.toNat).any (fun n => 0x63 ≤ n && n ≤ 0x7F) then
    pure (.value (← readValType))
  else
    let x ← readS 33
    if h : 0 ≤ x ∧ x.toNat < 2 ^ 32 then pure (.typeIdx ⟨⟨x.toNat, h.2⟩⟩)
    else decodeError s!"block type {x} outside the profile"

/-- Limits: flags `0x00`/`0x01` (32-bit addresses) or `0x04`/`0x05`
(64-bit addresses). Core 3.0 uses `u64` bounds for both address types; semantic
validation separately checks the address-specific maximum. In particular, small
i32 bounds may use valid six- to ten-byte non-minimal unsigned encodings. -/
def readLimits : DecodeM (AddrType × Wasm.Limits) := do
  match (← readByte).toNat with
  | 0x00 => pure (.i32, ⟨← readBound 64, none⟩)
  | 0x01 =>
    let n ← readBound 64
    let m ← readBound 64
    pure (.i32, ⟨n, some m⟩)
  | 0x04 => pure (.i64, ⟨← readBound 64, none⟩)
  | 0x05 =>
    let n ← readBound 64
    let m ← readBound 64
    pure (.i64, ⟨n, some m⟩)
  | f => decodeError s!"limits flags 0x{String.ofList (Nat.toDigits 16 f)} outside the profile"
where
  /-- A bound in `UN N`, `N ≤ 64`. -/
  readBound (N : Nat) : DecodeM (Fin (2 ^ 64)) := do
    let n ← readU N
    if h : n < 2 ^ 64 then pure ⟨n, h⟩ else decodeError "limit out of range"

/-- A table type: its element reference type, then its limits. -/
def readTableType : DecodeM Wasm.TableType := do
  let rt ← readRefType
  let (a, lim) ← readLimits
  pure ⟨a, lim, rt⟩

/-- A memory type: its limits. -/
def readMemType : DecodeM Wasm.MemoryType := do
  let (a, l) ← readLimits
  pure ⟨a, l⟩

/-- A `memarg`: the alignment exponent, with bit 6 set when an explicit memory index
follows, then a `u64` offset. -/
def readMemArg : DecodeM (MemIdx × Wasm.MemArg) := do
  let n ← readU 32
  if h : n < 2 ^ 6 then
    let o ← readU 64
    if ho : o < 2 ^ 64 then pure (⟨0⟩, ⟨⟨n, by omega⟩, ⟨o, ho⟩⟩)
    else decodeError "memarg offset out of range"
  else if h' : n < 2 ^ 7 then
    let x ← readIdx
    let o ← readU 64
    if ho : o < 2 ^ 64 then pure (x, ⟨⟨n - 2 ^ 6, by omega⟩, ⟨o, ho⟩⟩)
    else decodeError "memarg offset out of range"
  else decodeError s!"memarg flags {n} out of range"

/-- Relational operators in opcode order after `eqz`. -/
def relOps : List IntRelOp :=
  [.eq, .ne, .lt .signed, .lt .unsigned, .gt .signed, .gt .unsigned,
   .le .signed, .le .unsigned, .ge .signed, .ge .unsigned]

/-- Binary operators in opcode order. -/
def binOps : List IntBinOp :=
  [.add, .sub, .mul, .div .signed, .div .unsigned, .rem .signed, .rem .unsigned,
   .and, .or, .xor, .shl, .shr .signed, .shr .unsigned, .rotl, .rotr]

/-- Bit-counting unary operators in opcode order. -/
def unOps : List IntUnOp := [.clz, .ctz, .popcnt]

/-- The opcode `op` falls in the block `[base, base + ops.length)`. -/
def opIn {α : Type} (ops : List α) (base op : Nat) : Option α :=
  if base ≤ op then ops[op - base]? else none

/-- Instructions named by their opcode alone (`plainOp?`), and loads and stores, whose
opcode (`memOp?`) is followed by a `memarg`. -/
def readOpOnly (op : Nat) : DecodeM Wasm.Instr := do
  if let some i := plainOp? op.toUInt8 then pure i
  else if let some mk := memOp? op.toUInt8 then
    let (x, ao) ← readMemArg
    pure (mk x ao)
  else decodeError s!"opcode 0x{String.ofList (Nat.toDigits 16 op)} outside the profile"

/-- Vector instructions after the `0xFD` prefix: the `u32` sub-opcode, then the
immediates of its class (`fdKind`): none (`prefixFDOp?`), a `memarg` (`vecMemOp?`),
a `memarg` and a lane (`vecMemLaneOp?`), a lane (`vecLaneOp?`), or 16 bytes
(`v128.const` 12, `i8x16.shuffle` 13). Every sub-opcode is below `512`. -/
def readVecInstr : DecodeM Wasm.Instr := do
  let n ← readU 32
  if let some i := if n < 512 then prefixFDOp? n else none then pure i
  else if let some mk := vecMemOp? n then
    let (x, ao) ← readMemArg
    pure (mk x ao)
  else if let some mk := vecMemLaneOp? n then
    let (x, ao) ← readMemArg
    let l ← readByte
    pure (mk x ao (laneOf l))
  else if let some mk := vecLaneOp? n then
    let l ← readByte
    pure (mk (laneOf l))
  else if n = 12 then
    let bs ← readBytes 16
    pure (.vecConst (BitVec.ofNat 128 (littleEndian bs.data.toList)))
  else if n = 13 then
    let bs ← readBytes 16
    pure (.vecShuffle (bs.data.toList.map laneOf))
  else decodeError s!"opcode 0xFD {n} outside the profile"

/-- The two nullability bits of a branch cast; other flag bytes are invalid. -/
def readCastOp : DecodeM (Bool × Bool) := do
  match (← readByte).toNat with
  | 0 => pure (false, false)
  | 1 => pure (true, false)
  | 2 => pure (false, true)
  | 3 => pure (true, true)
  | _ => decodeError "bad cast flags"

/-- GC instructions after the `0xFB` prefix. -/
def readGCInstr : DecodeM Wasm.Instr := do
  match ← readU 32 with
  | 0 => pure (.structNew (← readIdx))
  | 1 => pure (.structNewDefault (← readIdx))
  | 2 =>
    let x ← readIdx
    let y ← readIdx
    pure (.structGet none x y)
  | 3 =>
    let x ← readIdx
    let y ← readIdx
    pure (.structGet (some .signed) x y)
  | 4 =>
    let x ← readIdx
    let y ← readIdx
    pure (.structGet (some .unsigned) x y)
  | 5 =>
    let x ← readIdx
    let y ← readIdx
    pure (.structSet x y)
  | 6 => pure (.arrayNew (← readIdx))
  | 7 => pure (.arrayNewDefault (← readIdx))
  | 8 =>
    let x ← readIdx
    let n ← readIdx (k := .type_)
    pure (.arrayNewFixed x n.value)
  | 9 =>
    let x ← readIdx
    let y ← readIdx
    pure (.arrayNewData x y)
  | 10 =>
    let x ← readIdx
    let y ← readIdx
    pure (.arrayNewElem x y)
  | 11 => pure (.arrayGet none (← readIdx))
  | 12 => pure (.arrayGet (some .signed) (← readIdx))
  | 13 => pure (.arrayGet (some .unsigned) (← readIdx))
  | 14 => pure (.arraySet (← readIdx))
  | 16 => pure (.arrayFill (← readIdx))
  | 17 =>
    let x ← readIdx
    let y ← readIdx
    pure (.arrayCopy x y)
  | 18 =>
    let x ← readIdx
    let y ← readIdx
    pure (.arrayInitData x y)
  | 19 =>
    let x ← readIdx
    let y ← readIdx
    pure (.arrayInitElem x y)
  | 20 => pure (.refTest ⟨false, ← readRefType.heapType⟩)
  | 21 => pure (.refTest ⟨true, ← readRefType.heapType⟩)
  | 22 => pure (.refCast ⟨false, ← readRefType.heapType⟩)
  | 23 => pure (.refCast ⟨true, ← readRefType.heapType⟩)
  | 24 =>
    let (n₁, n₂) ← readCastOp
    let l ← readIdx
    let h₁ ← readRefType.heapType
    let h₂ ← readRefType.heapType
    pure (.brOnCast l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩)
  | 25 =>
    let (n₁, n₂) ← readCastOp
    let l ← readIdx
    let h₁ ← readRefType.heapType
    let h₂ ← readRefType.heapType
    pure (.brOnCastFail l ⟨n₁, h₁⟩ ⟨n₂, h₂⟩)
  | n =>
    if let some i := prefixFBOp? n then pure i
    else decodeError s!"opcode 0xFB {n} outside the profile"

/-- Non-structured instructions whose opcode `op` has been read. -/
def readPlain (op : Nat) : DecodeM Wasm.Instr := do
  match op with
  | 0x08 => pure (.throw (← readIdx))
  | 0x0C => pure (.br (← readIdx))
  | 0x0D => pure (.brIf (← readIdx))
  | 0x0E =>
    let ls ← readVec readIdx
    let l ← readIdx
    pure (.brTable ls l)
  | 0x10 => pure (.call (← readIdx))
  | 0x11 =>
    let y ← readIdx
    let x ← readIdx
    pure (.callIndirect x y)
  | 0x12 => pure (.returnCall (← readIdx))
  | 0x13 =>
    let y ← readIdx
    let x ← readIdx
    pure (.returnCallIndirect x y)
  | 0x14 => pure (.callRef (← readIdx))
  | 0x15 => pure (.returnCallRef (← readIdx))
  | 0x1C => pure (.select (some (← readVec readValType)))
  | 0x20 => pure (.localGet (← readIdx))
  | 0x21 => pure (.localSet (← readIdx))
  | 0x22 => pure (.localTee (← readIdx))
  | 0x23 => pure (.globalGet (← readIdx))
  | 0x24 => pure (.globalSet (← readIdx))
  | 0x25 => pure (.tableGet (← readIdx))
  | 0x26 => pure (.tableSet (← readIdx))
  | 0xD0 => pure (.refNull (← readRefType.heapType))
  | 0xD2 => pure (.refFunc (← readIdx))
  | 0xD5 => pure (.brOnNull (← readIdx))
  | 0xD6 => pure (.brOnNonNull (← readIdx))
  | 0x41 => do let v ← readS 32; pure (.intConst .i32 (BitVec.ofInt 32 v))
  | 0x42 => do let v ← readS 64; pure (.intConst .i64 (BitVec.ofInt 64 v))
  | 0x43 => do
    let bs ← readBytes 4
    pure (.floatConst .f32 (BitVec.ofNat 32 (littleEndian bs.data.toList)))
  | 0x44 => do
    let bs ← readBytes 8
    pure (.floatConst .f64 (BitVec.ofNat 64 (littleEndian bs.data.toList)))
  | 0x3F => pure (.memorySize (← readIdx))
  | 0x40 => pure (.memoryGrow (← readIdx))
  | 0xFC => do
    match ← readU 32 with
    | 8 =>
      let y ← readIdx
      let x ← readIdx
      pure (.memoryInit x y)
    | 9 => pure (.dataDrop (← readIdx))
    | 10 =>
      let x₁ ← readIdx
      let x₂ ← readIdx
      pure (.memoryCopy x₁ x₂)
    | 11 => pure (.memoryFill (← readIdx))
    | 12 =>
      let y ← readIdx
      let x ← readIdx
      pure (.tableInit x y)
    | 13 => pure (.elemDrop (← readIdx))
    | 14 =>
      let dst ← readIdx
      let src ← readIdx
      pure (.tableCopy dst src)
    | 15 => pure (.tableGrow (← readIdx))
    | 16 => pure (.tableSize (← readIdx))
    | 17 => pure (.tableFill (← readIdx))
    | n =>
      if let some i := prefixFCOp? n then pure i
      else decodeError s!"opcode 0xFC {n} outside the profile"
  | 0xFB => readGCInstr
  | 0xFD => readVecInstr
  | op => readOpOnly op

/-- One of the four catch clauses of `try_table`. -/
def readCatch : DecodeM Wasm.Catch := do
  match (← readByte).toNat with
  | 0x00 =>
    let x ← readIdx
    let l ← readIdx
    pure (.catch_ x l)
  | 0x01 =>
    let x ← readIdx
    let l ← readIdx
    pure (.catchRef x l)
  | 0x02 => pure (.catchAll (← readIdx))
  | 0x03 => pure (.catchAllRef (← readIdx))
  | _ => decodeError "bad catch clause"

mutual
/-- One instruction whose opcode `op` has been read. Structural on `fuel`. -/
def readInstr (fuel : Nat) (op : Nat) : DecodeM Wasm.Instr :=
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
def readSeq (fuel : Nat) : DecodeM (List Wasm.Instr × UInt8) :=
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

/-- An expression: instructions, then `end`. -/
def readExpr : DecodeM Wasm.Expr := do
  let (is, t) ← readSeq ((← remaining) + 1)
  if t == 0x0B then pure is else decodeError "`else` outside `if`"

/-- An implementation limit on the locals of one function (wasm-tools and V8 use the
same bound); the format allows `2 ^ 32 - 1`, which would exhaust memory on
`List.replicate`. -/
def maxLocals : Nat := 50000

/-- A field's storage type: a value type or a packed integer. -/
def readStorageType : DecodeM Wasm.StorageType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x77 => let _ ← readByte; pure (.packed .i16)
  | some 0x78 => let _ ← readByte; pure (.packed .i8)
  | _ => pure (.val (← readValType))

/-- A storage type followed by its mutability. -/
def readFieldType : DecodeM Wasm.FieldType := do
  let t ← readStorageType
  match (← readByte).toNat with
  | 0 => pure ⟨.const, t⟩
  | 1 => pure ⟨.var, t⟩
  | _ => decodeError "bad field mutability"

/-- Array, struct and function composite types. -/
def readCompType : DecodeM Wasm.CompositeType := do
  match (← readByte).toNat with
  | 0x5E => pure (.array (← readFieldType))
  | 0x5F => pure (.struct (← readVec readFieldType))
  | 0x60 =>
    let params ← readVec readValType
    let results ← readVec readValType
    pure (.func ⟨params, results⟩)
  | _ => decodeError "bad composite type"

/-- A subtype, with optional finality and supertype indices. -/
def readSubType : DecodeM Wasm.SubType := do
  match (← peekByte).map UInt8.toNat with
  | some 0x4F =>
    let _ ← readByte
    let supers ← readVec readIdx
    pure ⟨true, supers, ← readCompType⟩
  | some 0x50 =>
    let _ ← readByte
    let supers ← readVec readIdx
    pure ⟨false, supers, ← readCompType⟩
  | _ => pure ⟨true, [], ← readCompType⟩

/-- A recursive group (`0x4E`) or a singleton subtype. -/
def readRecType : DecodeM Wasm.RecType := do
  if (← peekByte) == some 0x4E then
    let _ ← readByte
    pure ⟨← readVec readSubType⟩
  else pure ⟨[← readSubType]⟩

/-- A table, with an implicit null initializer or the explicit `0x40 0x00` form. -/
def readTable : DecodeM Wasm.Table := do
  if (← peekByte) == some 0x40 then
    let _ ← readByte
    unless (← readByte) == 0x00 do decodeError "bad table initializer prefix"
    let t ← readTableType
    let init ← readExpr
    pure ⟨t, init⟩
  else
    let t ← readTableType
    pure ⟨t, [.refNull t.element.heap]⟩

/-- A tag: the reserved attribute byte `0x00`, then a function type index. -/
def readTag : DecodeM Wasm.TagType := do
  unless (← readByte) == 0x00 do decodeError "bad tag attribute"
  readIdx

/-- A function, table, memory, global or tag import. -/
def readImport : DecodeM Wasm.Import := do
  let moduleName ← readName
  let name ← readName
  match (← readByte).toNat with
  | 0x00 => pure ⟨moduleName, name, .func (← readIdx)⟩
  | 0x01 => pure ⟨moduleName, name, .table (← readTableType)⟩
  | 0x02 => pure ⟨moduleName, name, .memory (← readMemType)⟩
  | 0x03 =>
    let t ← readValType
    let m ← match (← readByte).toNat with
      | 0x00 => pure Mutability.const
      | 0x01 => pure Mutability.var
      | _ => decodeError "bad global mutability"
    pure ⟨moduleName, name, .global ⟨m, t⟩⟩
  | 0x04 => pure ⟨moduleName, name, .tag (← readTag)⟩
  | _ => decodeError s!"import {moduleName}.{name} has an unsupported kind"

/-- A global. -/
def readGlobal : DecodeM Wasm.Global := do
  let t ← readValType
  let m ← match (← readByte).toNat with
    | 0x00 => pure Mutability.const
    | 0x01 => pure Mutability.var
    | _ => decodeError "bad global mutability"
  let init ← readExpr
  pure ⟨⟨m, t⟩, init⟩

/-- A function, table, memory, global or tag export. -/
def readExport : DecodeM Wasm.Export := do
  let name ← readName
  match (← readByte).toNat with
  | 0x00 => pure ⟨name, .func (← readIdx)⟩
  | 0x01 => pure ⟨name, .table (← readIdx)⟩
  | 0x02 => pure ⟨name, .memory (← readIdx)⟩
  | 0x03 => pure ⟨name, .global (← readIdx)⟩
  | 0x04 => pure ⟨name, .tag (← readIdx)⟩
  | _ => decodeError s!"export {name} has an unsupported kind"

/-- A code entry: its size, locals groups (expanded), the body. -/
def readCode : DecodeM (List Wasm.ValType × Wasm.Expr) := do
  let size ← readU 32
  let r₀ ← remaining
  unless size ≤ r₀ do decodeError "code entry past the end"
  let groups ← readVec do
    let n ← readU 32
    let t ← readValType
    pure (n, t)
  let total := groups.foldl (fun s p => s + p.1) 0
  unless total ≤ maxLocals do decodeError s!"{total} locals exceed the limit {maxLocals}"
  let locals := groups.flatMap fun p => List.replicate p.1 p.2
  let body ← readExpr
  unless r₀ - (← remaining) == size do decodeError "code entry size mismatch"
  pure (locals, body)

/-- A data segment: kind `0` (active in memory 0), `1` (passive) or `2` (active in an
explicit memory), then its offset expression if active, then its bytes. -/
def readData : DecodeM Wasm.Data := do
  match ← readU 32 with
  | 0 =>
    let e ← readExpr
    let bs ← readByteVec
    pure ⟨bs, .active ⟨0⟩ e⟩
  | 1 => pure ⟨← readByteVec, .passive⟩
  | 2 =>
    let x ← readIdx
    let e ← readExpr
    let bs ← readByteVec
    pure ⟨bs, .active x e⟩
  | k => decodeError s!"data segment kind {k} out of range"
where
  /-- A vector of bytes. -/
  readByteVec : DecodeM ByteArray := do
    let n ← readCount
    readBytes n

/-- All eight element segment kinds. Function-index segments use non-null
`ref func`; kind 4 has the implicit nullable `funcref` element type. -/
def readElem : DecodeM Wasm.Elem := do
  match ← readU 32 with
  | 0 =>
    let offset ← readExpr
    let ys ← readVec readIdx
    pure ⟨⟨false, .abstract .func⟩, refFuncs ys, .active ⟨0⟩ offset⟩
  | 1 => pure ⟨⟨false, .abstract .func⟩, ← funcInits, .passive⟩
  | 2 =>
    let x ← readIdx
    let offset ← readExpr
    let es ← funcInits
    pure ⟨⟨false, .abstract .func⟩, es, .active x offset⟩
  | 3 => pure ⟨⟨false, .abstract .func⟩, ← funcInits, .declarative⟩
  | 4 =>
    let offset ← readExpr
    let es ← readVec readExpr
    pure ⟨⟨true, .abstract .func⟩, es, .active ⟨0⟩ offset⟩
  | 5 =>
    let rt ← readRefType
    let es ← readVec readExpr
    pure ⟨rt, es, .passive⟩
  | 6 =>
    let x ← readIdx
    let offset ← readExpr
    let rt ← readRefType
    let es ← readVec readExpr
    pure ⟨rt, es, .active x offset⟩
  | 7 =>
    let rt ← readRefType
    let es ← readVec readExpr
    pure ⟨rt, es, .declarative⟩
  | k => decodeError s!"element segment kind {k} out of range"
where
  funcInits : DecodeM (List Wasm.Expr) := do
    unless (← readByte) == 0x00 do decodeError "bad element kind"
    pure (refFuncs (← readVec readIdx))

/-- The contents of a custom section of `size` bytes: a name, then any bytes. -/
def readCustom (size : Nat) : DecodeM Unit := do
  let before ← remaining
  let _ ← readName
  let used := before - (← remaining)
  unless used ≤ size do decodeError "custom section name past the section end"
  let _ ← readBytes (size - used)

/-- The sections of the fragment, as read. -/
structure Sections where
  types : List Wasm.RecType := []
  imports : List Wasm.Import := []
  funcTypes : List TypeIdx := []
  tables : List Wasm.Table := []
  memories : List Wasm.MemoryType := []
  tags : List Wasm.TagType := []
  globals : List Wasm.Global := []
  exports : List Wasm.Export := []
  start : Option FuncIdx := none
  elems : List Wasm.Elem := []
  dataCount : Option Nat := none
  code : List (List Wasm.ValType × Wasm.Expr) := []
  data : List Wasm.Data := []

/-- The contents of a supported non-custom section. -/
def readSectionBody (id : Nat) (s : Sections) : DecodeM Sections := do
  match id with
  | 1 => pure { s with types := ← readVec readRecType }
  | 2 => pure { s with imports := ← readVec readImport }
  | 3 => pure { s with funcTypes := ← readVec readIdx }
  | 4 => pure { s with tables := ← readVec readTable }
  | 5 => pure { s with memories := ← readVec readMemType }
  | 6 => pure { s with globals := ← readVec readGlobal }
  | 7 => pure { s with exports := ← readVec readExport }
  | 8 => pure { s with start := some (← readIdx) }
  | 9 => pure { s with elems := ← readVec readElem }
  | 10 => pure { s with code := ← readVec readCode }
  | 11 => pure { s with data := ← readVec readData }
  | 12 => pure { s with dataCount := some (← readU 32) }
  | 13 => pure { s with tags := ← readVec readTag }
  | _ => decodeError s!"section {id} outside the fragment"

/-- The position of a non-custom section in the required order
1, 2, 3, 4, 5, 13, 6, 7, 8, 9, 12, 10, 11; `0` for an unknown id. -/
def sectionRank (id : Nat) : Nat :=
  match id with
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 13 => 6 | 6 => 7 | 7 => 8 | 8 => 9
  | 9 => 10 | 12 => 11 | 10 => 12 | 11 => 13
  | _ => 0

/-- The module header: `magic ++ version`. -/
def readHeader : DecodeM Unit := do
  let h ← readBytes 8
  unless h.data.toList == magic ++ version do decodeError "bad magic or version"

/-- The decoder proper. -/
def readModule : DecodeM Wasm.Module := do
  readHeader
  let s ← readModule.go (← get).bytes.size 0 {}
  unless (← remaining) == 0 do decodeError "trailing bytes"
  unless s.funcTypes.length == s.code.length do
    decodeError s!"{s.funcTypes.length} function declarations but {s.code.length} bodies"
  unless s.dataCount.all (· == s.data.length) do decodeError "data count mismatch"
  unless s.dataCount.isSome || (codesDataIdxs s.code).isEmpty do
    decodeError "data index in code without a data count section"
  pure {
    types := s.types
    imports := s.imports
    tags := s.tags
    globals := s.globals
    tables := s.tables
    memories := s.memories
    elems := s.elems
    funcs := zipFuncs s.funcTypes s.code
    data := s.data
    start := s.start
    exports := s.exports }

where
  /-- At most `fuel` sections after the section of rank `last`; structural on `fuel`. -/
  go (fuel last : Nat) (s : Sections) : DecodeM Sections :=
    match fuel with
    | 0 => pure s
    | fuel + 1 => do
      if (← remaining) == 0 then return s
      let id := (← readByte).toNat
      let size ← readU 32
      let r₀ ← remaining
      unless size ≤ r₀ do decodeError s!"section {id} past the end"
      if id == 0 then
        readCustom size
        go fuel last s
      else
        unless last < sectionRank id do decodeError s!"section {id} out of order or repeated"
        let s ← readSectionBody id s
        unless r₀ - (← remaining) == size do decodeError s!"section {id} size mismatch"
        go fuel (sectionRank id) s

/-- The decoder with its error message. -/
def decodeModule (b : ByteArray) : Except String Wasm.Module :=
  readModule.run' ⟨b, 0⟩

end Decode

/-- **The decoder.** `some m` only if `b` encodes `m` (`decode?_sound`, DecodeSound.lean). -/
def decode? (b : ByteArray) : Option Wasm.Module :=
  match Decode.decodeModule b with
  | .ok m => some m
  | .error _ => none

end Silmaril.Wasm.Binary.Core
