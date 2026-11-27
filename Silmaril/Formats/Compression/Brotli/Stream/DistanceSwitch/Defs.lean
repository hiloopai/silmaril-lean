module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs

/-! Exact standard-window Brotli streams with all three block-switch
    categories and dictionary-free copies. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch

inductive Error where
  | envelope (reason : Stream.Error)
  | block (index : Nat) (reason : Execute.DistanceSwitch.BlockError)
  deriving DecidableEq, Repr

def Error.bit : Error → Nat
  | .envelope reason => reason.bit
  | .block _ reason => reason.bit

def payloadLimits (limits : Limits) (before : LSBReader) : Execute.Limits :=
  ⟨limits.output, limits.bits - before.totalRead⟩

/-- Each compressed meta-block starts fresh category runs and receives
    the output and recent-distance ring from the previous meta-block. -/
def Payload : PayloadWire :=
  fun header block initial bits chunk final =>
    ∃ chunks runs,
      Execute.DistanceSwitch.CommandsWire header ⟨block.windowBits, initial.output.size, block.length⟩
        (Execute.InsertCopy.State.start header initial) bits chunks ⟨final, runs⟩ ∧ chunk = chunks.flatten

def Wire (input : List UInt8) (window : Nat) (chunks : List (List UInt8)) (final : Execute.State) : Prop :=
  WireWith Payload input window chunks final

namespace Internal

def readPayload : Stream.Internal.ReadPayload Error :=
  fun limits index _ header block initial before => do
    let (final, after) ←
      (Execute.DistanceSwitch.readBlock header block.windowBits block.length (payloadLimits limits before)
        initial before).mapError (Error.block index)
    return (final.execution, after)

def readBody : Stream.Internal.ReadBody Error :=
  Stream.Internal.readBodyWith Error.envelope readPayload

end Internal

/-- Decode one exact dictionary-free standard-window stream with L, I
    and D switching. Errors retain their typed cause and original bit. -/
def decode (limits : Limits) (input : List UInt8) : Except Error Execute.State :=
  Stream.Internal.decodeWith Error.envelope Internal.readBody limits input

/-- The body either failed at an envelope operation or reached a checked
    compressed table header and failed at the witnessed command. -/
inductive BodyFailure (limits : Limits) (window index : Nat) (framing : Header) (initial : Execute.State)
    (before : LSBReader) (input : List Bool) : Error → Prop where
  | envelope {cause : Cause} : FailedOperation limits before cause →
      BodyFailure limits window index framing initial before input
        (.envelope ⟨before.totalRead, some index, none, cause⟩)
  | command {last : Bool} {length : RawLength} {header : CompressedHeader.Header} {payload : LSBReader}
      {used suffix : List Bool} {command : Nat} {reason : Execute.DistanceSwitch.Error} :
      framing = .compressed last length →
      CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
        .ok (header, payload) →
      Literal.Switch.Source before payload input used suffix →
      Execute.DistanceSwitch.BlockFailure header ⟨window, initial.output.size, length.size⟩
        (payloadLimits limits payload) payload command reason length.size 0
        (Execute.InsertCopy.State.start header initial) payload suffix →
      BodyFailure limits window index framing initial before input (.block index (.command command reason))

/-- Successful original framing and body reads at one block position. -/
structure PassedBlock (limits : Limits) (window index : Nat) (header : Header)
    (initial final : Execute.State) (before after : LSBReader) (input tail : List Bool) : Prop where
  parts : ∃ payload used,
    Stream.Internal.readHeader before = .ok (header, payload) ∧
    Stream.Internal.withinBits limits payload = .ok () ∧
    Internal.readBody limits window index header initial payload = .ok (final, after) ∧
    Literal.Switch.Source before after input used tail

/-- The walk to the first failed operation. Every preceding block
    succeeded and cleared its last flag. Fuel and indices follow that walk. -/
inductive FailedBlocks (limits : Limits) (window : Nat) :
    Nat → Nat → Execute.State → LSBReader → List Bool → Error → Prop where
  | fuel {index : Nat} {initial : Execute.State} {before : LSBReader} {input : List Bool} :
      FailedBlocks limits window 0 index initial before input
        (.envelope ⟨before.totalRead, some index, none, .framing .stepLimit⟩)
  | framing {fuel index : Nat} {initial : Execute.State} {before : LSBReader} {input : List Bool}
      {reason : Brotli.Error} :
      Stream.Internal.readHeader before = .error reason →
      FailedBlocks limits window (fuel + 1) index initial before input
        (.envelope ⟨before.totalRead, some index, none, .framing reason⟩)
  | framingBits {fuel index : Nat} {initial : Execute.State} {before payload : LSBReader}
      {input : List Bool} {header : Header} {cause : Cause} :
      Stream.Internal.readHeader before = .ok (header, payload) →
      Stream.Internal.withinBits limits payload = .error cause →
      FailedBlocks limits window (fuel + 1) index initial before input
        (.envelope ⟨before.totalRead, some index, none, cause⟩)
  | body {fuel index : Nat} {initial : Execute.State} {before payload : LSBReader}
      {input used tail : List Bool} {header : Header} {error : Error} :
      Stream.Internal.readHeader before = .ok (header, payload) →
      Stream.Internal.withinBits limits payload = .ok () →
      Literal.Switch.Source before payload input used tail →
      Internal.readBody limits window index header initial payload = .error error →
      BodyFailure limits window index header initial payload tail error →
      FailedBlocks limits window (fuel + 1) index initial before input error
  | finish {fuel index : Nat} {initial final : Execute.State} {before after : LSBReader}
      {input tail : List Bool} {header : Header} {cause : Cause} :
      PassedBlock limits window index header initial final before after input tail →
      header.last = true → Stream.Internal.finish limits after = .error cause →
      FailedBlocks limits window (fuel + 1) index initial before input
        (.envelope ⟨after.totalRead, some index, none, cause⟩)
  | next {fuel index : Nat} {initial final : Execute.State} {before after : LSBReader}
      {input tail : List Bool} {header : Header} {error : Error} :
      PassedBlock limits window index header initial final before after input tail →
      header.last = false →
      FailedBlocks limits window fuel (index + 1) final after tail error →
      FailedBlocks limits window (fuel + 1) index initial before input error

/-- The input and window checks precede the bounded meta-block walk. -/
inductive FailureWire (limits : Limits) (input : List UInt8) : Error → Prop where
  | inputLimit : limits.input < input.length →
      FailureWire limits input (.envelope ⟨0, none, none, .framing .inputLimit⟩)
  | window {reason : Brotli.Error} :
      input.length ≤ limits.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .error reason →
      FailureWire limits input (.envelope ⟨0, none, none, .framing reason⟩)
  | windowBits {window : Nat} {reader : LSBReader} {cause : Cause} :
      input.length ≤ limits.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, reader) →
      Stream.Internal.withinBits limits reader = .error cause →
      FailureWire limits input (.envelope ⟨0, none, none, cause⟩)
  | windowLimit {window : Nat} {reader : LSBReader} :
      input.length ≤ limits.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, reader) →
      Stream.Internal.withinBits limits reader = .ok () →
      limits.window < windowSize window →
      FailureWire limits input (.envelope ⟨0, none, none, .framing .windowLimit⟩)
  | blocks {window : Nat} {reader : LSBReader} {code tail : List Bool} {error : Error} :
      input.length ≤ limits.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, reader) →
      Stream.Internal.withinBits limits reader = .ok () →
      windowSize window ≤ limits.window → WindowWire window code →
      Literal.Switch.Source (Brotli.Internal.start input) reader (bytesBits input) code tail →
      FailedBlocks limits window limits.blocks 0 Execute.State.start reader tail error →
      FailureWire limits input error

end Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch
