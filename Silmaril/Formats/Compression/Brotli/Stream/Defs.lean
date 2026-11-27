module

public import Silmaril.Formats.Compression.Brotli.Defs
public import Silmaril.Formats.Compression.Brotli.Execute.Defs

/-! # Exact standard-window Brotli stream profile

RFC 7932 §§9.1–9.3 framing, including raw and metadata blocks. Compressed
blocks admit one block type per category and backward references into the
stream output. Static dictionary references have a distinct typed error.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Stream

structure Limits where
  input : Nat
  output : Nat
  window : Nat
  bits : Nat
  blocks : Nat
  /-- Header caps apply to each compressed meta-block. -/
  mapEntries : Nat
  trees : Nat
  deriving DecidableEq, Repr

inductive Cause where
  | framing (reason : Brotli.Error)
  | bitLimit
  | header (reason : CompressedHeader.Error)
  | command (reason : Execute.Error)
  | commandFuel
  deriving DecidableEq, Repr

/-- Absolute start bit of the failing operation in the original stream.
    Block and command indices are zero-based when present. -/
structure Error where
  bit : Nat
  block : Option Nat
  command : Option Nat
  cause : Cause
  deriving DecidableEq, Repr

/-- The MSKIPBYTES selector and length-minus-one, or the empty encoding. -/
structure MetadataLength where
  selector : Nat
  minusOne : Nat
  deriving DecidableEq, Repr

def MetadataLength.width (length : MetadataLength) : Nat := 8 * length.selector

def MetadataLength.size (length : MetadataLength) : Nat :=
  if length.selector = 0 then 0 else length.minusOne + 1

def MetadataLength.Valid (length : MetadataLength) : Prop :=
  length.selector < 4 ∧ length.minusOne < 2 ^ length.width ∧
    (length.selector ≤ 1 ∨ 2 ^ (length.width - 8) ≤ length.minusOne)

inductive Header where
  | terminal
  | raw (length : RawLength)
  | metadata (last : Bool) (length : MetadataLength)
  | compressed (last : Bool) (length : RawLength)
  deriving DecidableEq, Repr

def Header.last : Header → Bool
  | .terminal => true
  | .raw _ => false
  | .metadata last _ | .compressed last _ => last

def Header.outputSize : Header → Nat
  | .terminal | .metadata _ _ => 0
  | .raw length | .compressed _ length => length.size

def Header.Valid : Header → Prop
  | .terminal => True
  | .raw length | .compressed _ length => length.Valid
  | .metadata _ length => length.Valid

def lastBits (last : Bool) : List Bool := if last then [true, false] else [false]

def Header.bits : Header → List Bool
  | .terminal => [true, true]
  | .raw length => (MetaHeader.raw length).bits
  | .metadata last length =>
    lastBits last ++ [true, true, false] ++ natBits length.selector 2 ++
      natBits length.minusOne length.width
  | .compressed last length =>
    lastBits last ++ natBits length.selector 2 ++ natBits length.minusOne length.width ++
      (if last then [] else [false])

/-- Producing a command consumes output fuel even when all its fields are
    implicit or singleton coded. The stream history is passed through each
    individual command witness. -/
inductive CommandsWire (header : CompressedHeader.Header) (block : Execute.Block) :
    Execute.State → List Bool → List (List UInt8) → Execute.State → Prop where
  | done {state : Execute.State} : state.output.size = block.endOutput →
      CommandsWire header block state [] [] state
  | step {initial final : Execute.State} {result : Execute.Result} {head tail : List Bool}
      {chunk : List UInt8} {chunks : List (List UInt8)} :
      Execute.Wire header block initial head result →
      result.state.output.toList = initial.output.toList ++ chunk →
      0 < chunk.length →
      CommandsWire header block result.state tail chunks final →
      CommandsWire header block initial (head ++ tail) (chunk :: chunks) final

/-- One block body from immediately after its framing header. For raw and
    metadata bodies the checked alignment is part of the wire relation. -/
inductive BodyWire (window position : Nat) :
    Header → Execute.State → List Bool → List UInt8 → Execute.State → Prop where
  | terminal (initial : Execute.State) : BodyWire window position .terminal initial [] [] initial
  | raw {length : RawLength} {initial : Execute.State} {bytes : List UInt8} :
      bytes.length = length.size →
      BodyWire window position (.raw length) initial (padding position ++ bytesBits bytes)
        bytes { initial with output := initial.output ++ bytes.toArray }
  | metadata {last : Bool} {length : MetadataLength} (initial : Execute.State)
      {bytes : List UInt8} : bytes.length = length.size →
      BodyWire window position (.metadata last length) initial (padding position ++ bytesBits bytes) [] initial
  | compressed {last : Bool} {length : RawLength} {header : CompressedHeader.Header}
      {work : Nat} {initial final : Execute.State} {tableBits commandBits : List Bool}
      {chunks : List (List UInt8)} :
      CompressedHeader.Wire work tableBits header → Execute.oneType header = true →
      CommandsWire header ⟨window, initial.output.size, length.size⟩ initial commandBits chunks final →
      BodyWire window position (.compressed last length) initial (tableBits ++ commandBits) chunks.flatten final

/-- The first last flag ends the block chain, and its zero fill consumes
    the remainder of the supplied input. -/
inductive BlocksWire (window : Nat) :
    Nat → Execute.State → List Bool → List (List UInt8) → Execute.State → Prop where
  | last {position : Nat} {initial final : Execute.State} {header : Header}
      {body : List Bool} {chunk : List UInt8} :
      header.Valid → header.last = true →
      BodyWire window (position + header.bits.length) header initial body chunk final →
      BlocksWire window position initial
        (header.bits ++ body ++ padding (position + header.bits.length + body.length)) [chunk] final
  | more {position : Nat} {initial next final : Execute.State} {header : Header}
      {body tail : List Bool} {chunk : List UInt8} {chunks : List (List UInt8)} :
      header.Valid → header.last = false →
      BodyWire window (position + header.bits.length) header initial body chunk next →
      BlocksWire window (position + header.bits.length + body.length) next tail chunks final →
      BlocksWire window position initial (header.bits ++ body ++ tail) (chunk :: chunks) final

def Wire (input : List UInt8) (window : Nat) (chunks : List (List UInt8)) (final : Execute.State) : Prop :=
  ∃ code blocks, WindowWire window code ∧ bytesBits input = code ++ blocks ∧
    BlocksWire window code.length Execute.State.start blocks chunks final

namespace Internal

open Brotli.Internal (start take readWindow alignZero takeBody)

def readLength (selector : Nat) (before : LSBReader) : Except Brotli.Error (RawLength × LSBReader) := do
  let (minusOne, after) ← take before (4 * (4 + selector))
  let length : RawLength := ⟨selector, minusOne⟩
  if selector ≠ 0 ∧ minusOne < 2 ^ (length.width - 4) then .error .noncanonicalLength
  else .ok (length, after)

def readMetadata (before : LSBReader) : Except Brotli.Error (MetadataLength × LSBReader) := do
  let (reserved, reader) ← take before 1
  if reserved ≠ 0 then .error .reservedMetadata
  else
    let (selector, reader) ← take reader 2
    let (minusOne, reader) ← take reader (8 * selector)
    let length : MetadataLength := ⟨selector, minusOne⟩
    if 1 < selector ∧ minusOne < 2 ^ (length.width - 8) then .error .noncanonicalLength
    else .ok (length, reader)

def readFlags (before : LSBReader) : Except Brotli.Error (Option Bool × LSBReader) := do
  let (last, reader) ← take before 1
  if last = 0 then return (some false, reader)
  let (empty, reader) ← take reader 1
  return (if empty = 0 then some true else none, reader)

def readHeader (before : LSBReader) : Except Brotli.Error (Header × LSBReader) := do
  let (flags, reader) ← readFlags before
  match flags with
  | none => return (.terminal, reader)
  | some last =>
    let (selector, reader) ← take reader 2
    if selector = 3 then
      let (length, after) ← readMetadata reader
      return (.metadata last length, after)
    let (length, reader) ← readLength selector reader
    if last then return (.compressed true length, reader)
    let (raw, after) ← take reader 1
    return (if raw = 0 then .compressed false length else .raw length, after)

/-- Fixed framing fields use at most 31 scratch bits before this commit
    check. The byte bodies and entropy decoders receive residual caps. -/
def withinBits (limits : Limits) (after : LSBReader) : Except Cause Unit :=
  if after.totalRead ≤ limits.bits then .ok () else .error .bitLimit

def alignedBody (limits : Limits) (size : Nat) (before : LSBReader) :
    Except Cause (List UInt8 × LSBReader) := do
  let aligned ← (alignZero before).mapError Cause.framing
  if limits.bits < aligned.totalRead + 8 * size then .error .bitLimit
  else (takeBody size aligned).mapError Cause.framing

def runCommands (limits : Limits) (header : CompressedHeader.Header) (block : Execute.Block)
    (index : Nat) : Nat → Nat → Execute.State → LSBReader → Except Error (Execute.State × LSBReader)
  | fuel, command, initial, before =>
    if initial.output.size = block.endOutput then .ok (initial, before)
    else match fuel with
    | 0 => .error ⟨before.totalRead, some index, some command, .commandFuel⟩
    | fuel + 1 => do
      let (result, after) ← (Execute.read header block ⟨limits.output, limits.bits - before.totalRead⟩
        initial before).mapError (fun cause => ⟨before.totalRead, some index, some command, .command cause⟩)
      runCommands limits header block index fuel (command + 1) result.state after

def readBody (limits : Limits) (window index : Nat) (header : Header)
    (initial : Execute.State) (before : LSBReader) : Except Error (Execute.State × LSBReader) := do
  let failure : Cause → Error := fun cause => ⟨before.totalRead, some index, none, cause⟩
  match header with
  | .terminal => pure (initial, before)
  | .metadata _ length =>
    let (_, after) ← (alignedBody limits length.size before).mapError failure
    pure (initial, after)
  | .raw length =>
    if limits.output < initial.output.size + length.size then .error (failure (.framing .outputLimit))
    else
      let (bytes, after) ← (alignedBody limits length.size before).mapError failure
      pure ({ initial with output := initial.output ++ bytes.toArray }, after)
  | .compressed _ length =>
    if limits.output < initial.output.size + length.size then .error (failure (.framing .outputLimit))
    else
      let (parsed, payload) ← (CompressedHeader.read
        ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before).mapError
          (fun reason => failure (.header reason))
      if !Execute.oneType parsed then .error (failure (.command .blockTypes))
      else runCommands limits parsed ⟨window, initial.output.size, length.size⟩ index length.size 0 initial payload

def finish (limits : Limits) (before : LSBReader) : Except Cause LSBReader := do
  let aligned ← (alignZero before).mapError Cause.framing
  withinBits limits aligned
  if aligned.input.isEmpty then .ok aligned else .error (.framing .trailingInput)

def readBlocks (limits : Limits) (window : Nat) :
    Nat → Nat → Execute.State → LSBReader → Except Error Execute.State
  | 0, index, _, before => .error ⟨before.totalRead, some index, none, .framing .stepLimit⟩
  | fuel + 1, index, initial, before => do
    let failure : Cause → Error := fun cause => ⟨before.totalRead, some index, none, cause⟩
    let (header, payload) ← (readHeader before).mapError (failure ∘ Cause.framing)
    (withinBits limits payload).mapError failure
    let (next, after) ← readBody limits window index header initial payload
    if header.last then
      let _ ← (finish limits after).mapError (fun cause => ⟨after.totalRead, some index, none, cause⟩)
      return next
    else readBlocks limits window fuel (index + 1) next after

end Internal

/-- Decode one exact dictionary-free standard-window stream.
    There is no returned partial state on failure. -/
def decode (limits : Limits) (input : List UInt8) : Except Error Execute.State := do
  let failure : Cause → Error := fun cause => ⟨0, none, none, cause⟩
  if limits.input < input.length then .error (failure (.framing .inputLimit))
  else
    let (window, reader) ← (Brotli.Internal.readWindow (Brotli.Internal.start input)).mapError
      (failure ∘ Cause.framing)
    (Internal.withinBits limits reader).mapError failure
    if limits.window < windowSize window then .error (failure (.framing .windowLimit))
    else Internal.readBlocks limits window limits.blocks 0 Execute.State.start reader

/-- The lower operation that produced a failure, at its actual start cursor.
    A caller cap or an unsupported profile branch has its own guard witness. -/
inductive FailedOperation (limits : Limits) : LSBReader → Cause → Prop where
  | inputLimit {bytes : List UInt8} : limits.input < bytes.length →
      FailedOperation limits (Brotli.Internal.start bytes) (.framing .inputLimit)
  | window {before : LSBReader} {reason : Brotli.Error} :
      Brotli.Internal.readWindow before = .error reason → FailedOperation limits before (.framing reason)
  | windowLimit {before after : LSBReader} {window : Nat} :
      Brotli.Internal.readWindow before = .ok (window, after) → limits.window < windowSize window →
      FailedOperation limits before (.framing .windowLimit)
  | stepLimit (before : LSBReader) : FailedOperation limits before (.framing .stepLimit)
  | framing {before : LSBReader} {reason : Brotli.Error} :
      Internal.readHeader before = .error reason → FailedOperation limits before (.framing reason)
  | windowBits {before after : LSBReader} {window : Nat} :
      Brotli.Internal.readWindow before = .ok (window, after) →
      Internal.withinBits limits after = .error .bitLimit → FailedOperation limits before .bitLimit
  | framingBits {before after : LSBReader} {header : Header} :
      Internal.readHeader before = .ok (header, after) →
      Internal.withinBits limits after = .error .bitLimit → FailedOperation limits before .bitLimit
  | outputLimit (before : LSBReader) {initial : Execute.State} {length : RawLength} :
      limits.output < initial.output.size + length.size →
      FailedOperation limits before (.framing .outputLimit)
  | byteBody {before : LSBReader} {size : Nat} {reason : Cause} :
      Internal.alignedBody limits size before = .error reason → FailedOperation limits before reason
  | header {before : LSBReader} {reason : CompressedHeader.Error} :
      CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
        .error reason → FailedOperation limits before (.header reason)
  | blockTypes {before after : LSBReader} {header : CompressedHeader.Header} :
      CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
        .ok (header, after) → Execute.oneType header = false →
      FailedOperation limits before (.command .blockTypes)
  | command {before : LSBReader} {header : CompressedHeader.Header} {block : Execute.Block}
      {initial : Execute.State} {reason : Execute.Error} :
      Execute.read header block ⟨limits.output, limits.bits - before.totalRead⟩ initial before = .error reason →
      FailedOperation limits before (.command reason)
  | finish {before : LSBReader} {reason : Cause} :
      Internal.finish limits before = .error reason → FailedOperation limits before reason

/-- A failed operation begins at an exact suffix of the original bits. -/
def FailureWire (limits : Limits) (origin : Nat) (bits : List Bool) (error : Error) : Prop :=
  ∃ consumedBits suffix reader, bits = consumedBits ++ suffix ∧ Brotli.Internal.Cursor reader suffix ∧
    reader.totalRead = origin + consumedBits.length ∧ error.bit = reader.totalRead ∧
    FailedOperation limits reader error.cause

/-- Successful commands before the failing command of a compressed block. -/
inductive PassedCommands (limits : Limits) (header : CompressedHeader.Header) (block : Execute.Block) :
    Execute.State → LSBReader → Nat → Execute.State → LSBReader → Prop where
  | none (state : Execute.State) (reader : LSBReader) : PassedCommands limits header block state reader 0 state reader
  | next {before after stop : LSBReader} {initial final : Execute.State} {result : Execute.Result} {passed : Nat} :
      Execute.read header block ⟨limits.output, limits.bits - before.totalRead⟩ initial before = .ok (result, after) →
      PassedCommands limits header block result.state after passed final stop →
      PassedCommands limits header block initial before (passed + 1) final stop

def CommandSite (limits : Limits) (window : Nat) (initial : Execute.State) (framing : Header)
    (before : LSBReader) (error : Error) (command : Nat) : Prop :=
  ∃ last length header payload state reader reason,
    framing = .compressed last length ∧
    CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
      .ok (header, payload) ∧
    PassedCommands limits header ⟨window, initial.output.size, length.size⟩ initial payload command state reader ∧
    command < length.size ∧
    Execute.read header ⟨window, initial.output.size, length.size⟩
      ⟨limits.output, limits.bits - reader.totalRead⟩ state reader = .error reason ∧
    error.bit = reader.totalRead ∧ error.cause = .command reason

/-- Successful non-last blocks, indexed by the checked walk's counter. -/
inductive PassedBlocks (limits : Limits) (window : Nat) :
    Nat → Execute.State → LSBReader → Nat → Execute.State → LSBReader → Prop where
  | none (index : Nat) (state : Execute.State) (reader : LSBReader) :
      PassedBlocks limits window index state reader index state reader
  | next {index current : Nat} {before payload after stop : LSBReader}
      {initial next final : Execute.State} {header : Header} :
      Internal.readHeader before = .ok (header, payload) → Internal.withinBits limits payload = .ok () →
      Internal.readBody limits window index header initial payload = .ok (next, after) → header.last = false →
      PassedBlocks limits window (index + 1) next after current final stop →
      PassedBlocks limits window index initial before current final stop

def IndexedFailure (limits : Limits) (window index : Nat) (initial : Execute.State)
    (before : LSBReader) (error : Error) : Prop :=
  ∃ current state reader, PassedBlocks limits window index initial before current state reader ∧
    error.block = some current ∧
    ∀ command, error.command = some command → ∃ header payload,
      Internal.readHeader reader = .ok (header, payload) ∧ CommandSite limits window state header payload error command

end Silmaril.Formats.Compression.Brotli.Stream
