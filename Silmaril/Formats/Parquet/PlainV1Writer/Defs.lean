module

public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs

/-! One flat, uncompressed PLAIN INT32 data page with a Compact V1 header. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.PlainV1Writer

inductive Input where
  | required (values : List Int32)
  | optional (slots : List (Option Int32))
  deriving Repr

structure Limits where
  header : Page.HeaderLimits
  headerBytes : Nat
  scalar : ScalarPage.Limits

inductive Error where
  | bodyBudget
  | headerBudget
  | headerInteger
  | header (error : Page.HeaderError)
  | headerMismatch
  deriving DecidableEq, Repr

def Input.slots : Input → List (Option Int32)
  | .required values => values.map some
  | .optional slots => slots

def Input.numValues : Input → Nat
  | .required values => values.length
  | .optional slots => slots.length

def Input.schema : Input → FlatPage.LevelSchema
  | .required _ => ⟨0, 0⟩
  | .optional _ => ⟨0, 1⟩

def Input.definitionSize : Input → Nat
  | .required _ => 0
  | .optional slots => 2 * slots.length

def Input.bodySize : Input → Nat
  | .required values => 4 * values.length
  | .optional slots => 4 + 2 * slots.length + 4 * slots.countP Option.isSome

/-- Check all body bounds before materializing any level or scalar bytes. -/
def Input.Fits (input : Input) (limits : Limits) : Prop :=
  input.numValues < Hybrid.runLimit ∧ input.numValues ≤ limits.scalar.levels.values ∧
    input.definitionSize ≤ limits.scalar.levels.bytes ∧ input.bodySize < 2 ^ 31 ∧
    input.bodySize ≤ limits.scalar.compressedBytes ∧ input.bodySize ≤ limits.scalar.uncompressedBytes

instance (input : Input) (limits : Limits) : Decidable (input.Fits limits) := by
  unfold Input.Fits
  infer_instance

/-- A width-one singleton RLE run per definition slot, with no trailing padding. -/
def definitionOctets {α : Type} (slots : List (Option α)) : List UInt8 :=
  slots.flatMap fun slot => (Hybrid.Run.repeated 1 (if slot.isSome then 1 else 0)).wire 1

def Input.body : Input → Bytes
  | .required values => Plain.encodeInt32 values
  | .optional slots =>
    let definitions := definitionOctets slots
    (Bytes.ofList (KBytes.unpack 4 definitions.length ++ definitions)).append
      (Plain.encodeInt32 (slots.filterMap id))

def Input.parameters (input : Input) : ScalarPage.Parameters :=
  ⟨⟨input.bodySize, input.bodySize⟩, input.schema, input.numValues,
    Payload.Codec.uncompressed.id, 0, .v1 3 3⟩

def Input.header (input : Input) : Page.Header :=
  ⟨input.bodySize, input.bodySize, none, .dataV1 ⟨input.numValues, 0, 3, 3⟩⟩

/-- Emit a fixed Compact PageHeader shape. The inline i32 fields have delta
one, and the V1 struct has delta two after compressed_page_size. -/
def encodeHeader (count size : Nat) : Option Bytes := do
  let sizeWord ← ThriftCompact.encodeSigned? .i32 size
  let countWord ← ThriftCompact.encodeSigned? .i32 count
  return Bytes.ofList ([0x15, 0, 0x15] ++ sizeWord.toList ++ [0x15] ++ sizeWord.toList ++
    [0x2c, 0x15] ++ countWord.toList ++ [0x15, 0, 0x15, 6, 0x15, 6, 0, 0])

/-- Add field 4 as Compact signed i32, keeping the CRC's unsigned bit
pattern. The V1 detail follows it at field delta one. -/
def encodeHeaderWithChecksum (count size : Nat) (crc : Option UInt32) : Option Bytes :=
  match crc with
  | none => encodeHeader count size
  | some digest => do
    let sizeWord ← ThriftCompact.encodeSigned? .i32 size
    let countWord ← ThriftCompact.encodeSigned? .i32 count
    let crcWord ← ThriftCompact.encodeSigned? .i32 digest.toInt32.toInt
    return Bytes.ofList ([0x15, 0, 0x15] ++ sizeWord.toList ++ [0x15] ++ sizeWord.toList ++
      [0x15] ++ crcWord.toList ++ [0x1c, 0x15] ++ countWord.toList ++
      [0x15, 0, 0x15, 6, 0x15, 6, 0, 0])

structure Encoded where
  header : Page.Header
  headerBytes : Bytes
  body : Bytes
  deriving DecidableEq

def Encoded.wire (page : Encoded) : Bytes := page.headerBytes.append page.body

/-- The wire writer checks exact PageHeader recovery and the body bounds.
The page has no CRC, statistics, dictionary, repetition section or file envelope. -/
def emit (limits : Limits) (input : Input) : Except Error Encoded :=
  if input.Fits limits then
    match encodeHeader input.numValues input.bodySize with
    | none => .error .headerInteger
    | some headerBytes =>
      if limits.headerBytes < headerBytes.length then .error .headerBudget
      else
        let page : Encoded := ⟨input.header, headerBytes, input.body⟩
        match Page.readHeaderPrefix limits.header page.wire with
        | .error error => .error (.header error)
        | .ok parsed =>
          if parsed = (page.header, headerBytes.length) then .ok page else .error .headerMismatch
  else .error .bodyBudget

end Silmaril.Formats.Parquet.PlainV1Writer
