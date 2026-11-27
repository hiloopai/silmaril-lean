module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas

/-! # Bounded RFC 7932 Brotli raw meta-blocks

This profile admits one standard window header, zero or more non-last
uncompressed meta-blocks, and one empty last meta-block. All alignment
bits are zero. The decoder takes an exact stream, including its final
partial byte, and rejects entropy-coded and metadata meta-blocks.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli

structure Limits where
  input : Nat
  output : Nat
  window : Nat
  /-- Number of meta-blocks, including the empty terminal block. -/
  steps : Nat
  deriving DecidableEq, Repr

inductive Error where
  | inputLimit
  | outputLimit
  | windowLimit
  | stepLimit
  | truncated
  | reservedWindow
  | reservedMetadata
  | unsupportedMetadata
  | unsupportedCompressed
  | noncanonicalLength
  | nonzeroPadding
  | trailingInput
  deriving DecidableEq, Repr

/-- RFC 7932 §9.1 gives the window in bytes, including the sixteen-byte adjustment. -/
def windowSize (wbits : Nat) : Nat := 2 ^ wbits - 16

inductive WindowWire : Nat → List Bool → Prop where
  | sixteen : WindowWire 16 [false]
  | short {code : Nat} : 0 < code → code < 8 →
      WindowWire (17 + code) ([true] ++ natBits code 3)
  | seventeen : WindowWire 17 ([true] ++ natBits 0 3 ++ natBits 0 3)
  | long {code : Nat} : 2 ≤ code → code < 8 →
      WindowWire (8 + code) ([true] ++ natBits 0 3 ++ natBits code 3)

/-- The MNIBBLES selector and the encoded MLEN minus one. -/
structure RawLength where
  selector : Nat
  minusOne : Nat
  deriving DecidableEq, Repr

def RawLength.width (raw : RawLength) : Nat := 4 * (4 + raw.selector)
def RawLength.size (raw : RawLength) : Nat := raw.minusOne + 1

def RawLength.Valid (raw : RawLength) : Prop :=
  raw.selector < 3 ∧ raw.minusOne < 2 ^ raw.width ∧
    (raw.selector = 0 ∨ 2 ^ (raw.width - 4) ≤ raw.minusOne)

inductive MetaHeader where
  | raw (length : RawLength)
  | terminal
  deriving DecidableEq, Repr

def MetaHeader.bits : MetaHeader → List Bool
  | .raw length => [false] ++ natBits length.selector 2 ++ natBits length.minusOne length.width ++ [true]
  | .terminal => [true, true]

def MetaHeader.Valid : MetaHeader → Prop
  | .raw length => length.Valid
  | .terminal => True

def padding (position : Nat) : List Bool :=
  List.replicate ((8 - position % 8) % 8) false

def bodyStart (position : Nat) (header : MetaHeader) : Nat :=
  let after := position + header.bits.length
  after + (padding after).length

/-- The wire argument is the exact suffix through the terminal fill bits.
    Raw bodies start at the next byte boundary. Steps count the terminal. -/
inductive BlocksWire : Nat → List Bool → List (List UInt8) → Nat → Prop where
  | terminal {position : Nat} :
      BlocksWire position (MetaHeader.terminal.bits ++ padding (position + MetaHeader.terminal.bits.length)) [] 1
  | raw {position steps : Nat} {raw : RawLength} {body : List UInt8}
      {tail : List Bool} {chunks : List (List UInt8)} :
      raw.Valid → body.length = raw.size →
      BlocksWire (bodyStart position (.raw raw) + 8 * body.length) tail chunks steps →
      BlocksWire position
        ((.raw raw : MetaHeader).bits ++ padding (position + (.raw raw : MetaHeader).bits.length) ++
          bytesBits body ++ tail)
        (body :: chunks) (steps + 1)

def StreamWire (input output : List UInt8) (wbits steps : Nat) : Prop :=
  ∃ code wire chunks,
    WindowWire wbits code ∧ bytesBits input = code ++ wire ∧
    BlocksWire code.length wire chunks steps ∧ output = chunks.flatten

namespace Internal

/-- The buffered tail and absolute position share the same byte boundary. -/
def Cursor (reader : LSBReader) (bits : List Bool) : Prop :=
  reader.Rep bits ∧ reader.count < 8 ∧ (reader.totalRead + reader.count) % 8 = 0

def start (input : List UInt8) : LSBReader := ⟨0, 0, input, 0⟩

def take (reader : LSBReader) (width : Nat) : Except Error (Nat × LSBReader) :=
  match reader.readBits width with
  | some result => .ok result
  | none => .error .truncated

def readWindow (reader : LSBReader) : Except Error (Nat × LSBReader) := do
  let (first, reader) ← take reader 1
  if first = 0 then return (16, reader)
  else
    let (short, reader) ← take reader 3
    if short ≠ 0 then return (17 + short, reader)
    else
      let (long, reader) ← take reader 3
      if long = 0 then return (17, reader)
      else if long = 1 then .error .reservedWindow
      else return (8 + long, reader)

def readLength (reader : LSBReader) : Except Error (RawLength × LSBReader) := do
  let (selector, reader) ← take reader 2
  if selector = 3 then
    let (reserved, _) ← take reader 1
    if reserved = 0 then .error .unsupportedMetadata else .error .reservedMetadata
  else
    let (minusOne, reader) ← take reader (4 * (4 + selector))
    let raw : RawLength := ⟨selector, minusOne⟩
    if selector ≠ 0 ∧ minusOne < 2 ^ (raw.width - 4) then .error .noncanonicalLength
    else return (raw, reader)

def readHeader (reader : LSBReader) : Except Error (MetaHeader × LSBReader) := do
  let (last, reader) ← take reader 1
  if last = 0 then
    let (length, reader) ← readLength reader
    let (raw, reader) ← take reader 1
    if raw = 1 then return (.raw length, reader)
    else .error .unsupportedCompressed
  else
    let (empty, reader) ← take reader 1
    if empty = 1 then return (.terminal, reader)
    else
      let _ ← readLength reader
      .error .unsupportedCompressed

/-- Check the buffered fill bits before advancing to the next byte. -/
def alignZero (reader : LSBReader) : Except Error LSBReader :=
  if reader.buffer = 0 then .ok reader.alignToByte else .error .nonzeroPadding

/-- The caller provides a byte-aligned reader. -/
def takeBody (size : Nat) (reader : LSBReader) : Except Error (List UInt8 × LSBReader) :=
  let (body, rest) := reader.input.splitAt size
  if body.length = size then
    .ok (body, { reader with input := rest, totalRead := reader.totalRead + 8 * size })
  else .error .truncated

def readBlocks : Nat → Nat → LSBReader → List (List UInt8) → Except Error (List (List UInt8))
  | 0, _, _, _ => .error .stepLimit
  | fuel + 1, remaining, reader, reversed => do
    let (header, reader) ← readHeader reader
    let aligned ← alignZero reader
    match header with
    | .terminal =>
      if aligned.input.isEmpty then return reversed.reverse else .error .trailingInput
    | .raw raw =>
      if remaining < raw.size then .error .outputLimit
      else
        let (body, next) ← takeBody raw.size aligned
        readBlocks fuel (remaining - raw.size) next (body :: reversed)

end Internal

/-- Decode an exact stream in the raw-meta-block profile. -/
def decode (limits : Limits) (input : List UInt8) : Except Error (List UInt8) :=
  if limits.input < input.length then .error .inputLimit
  else do
    let (wbits, reader) ← Internal.readWindow (Internal.start input)
    if limits.window < windowSize wbits then .error .windowLimit
    else
      let chunks ← Internal.readBlocks limits.steps limits.output reader []
      return chunks.flatten

end Silmaril.Formats.Compression.Brotli
