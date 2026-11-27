module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
public import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs

/-! Exact standard-window Brotli streams with literal and insert-and-copy
    block switching, a single distance type, and dictionary-free copies. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch

inductive Error where
  | envelope (reason : Stream.Error)
  | block (index : Nat) (reason : Execute.LiteralSwitch.BlockError)
  deriving DecidableEq, Repr

def Error.bit : Error → Nat
  | .envelope reason => reason.bit
  | .block _ (.command _ reason) => reason.bit
  | .block _ (.initialOutput bit) | .block _ (.fuel _ bit) => bit

def payloadLimits (limits : Limits) (before : LSBReader) : Execute.Limits :=
  ⟨limits.output, limits.bits - before.totalRead⟩

/-- A compressed block starts with fresh category runs initialized by
    its header. Output bytes and recent distances come from the stream. -/
def Payload : PayloadWire :=
  fun header block initial bits chunk final =>
    ∃ chunks runs,
      Execute.LiteralSwitch.CommandsWire header ⟨block.windowBits, initial.output.size, block.length⟩
        (Execute.InsertCopy.State.start header initial) bits chunks ⟨final, runs⟩ ∧ chunk = chunks.flatten

def Wire (input : List UInt8) (window : Nat) (chunks : List (List UInt8)) (final : Execute.State) : Prop :=
  WireWith Payload input window chunks final

namespace Internal

def readPayload : Stream.Internal.ReadPayload Error :=
  fun limits index _ header block initial before => do
    let (final, after) ←
      (Execute.LiteralSwitch.readBlock header block.windowBits block.length (payloadLimits limits before)
        initial before).mapError (Error.block index)
    return (final.execution, after)

def readBody : Stream.Internal.ReadBody Error :=
  Stream.Internal.readBodyWith Error.envelope readPayload

end Internal

/-- Decode one exact stream. A failure carries the original operation
    coordinate and typed cause. -/
def decode (limits : Limits) (input : List UInt8) : Except Error Execute.State :=
  Stream.Internal.decodeWith Error.envelope Internal.readBody limits input

/-- The later cursor represents the untouched suffix of these source bits. -/
def Source (before after : LSBReader) (input tail : List Bool) : Prop :=
  ∃ used, input = used ++ tail ∧ after.totalRead = before.totalRead + used.length ∧ Brotli.Internal.Cursor after tail

/-- A failed compressed payload after a checked table header, with the
    block executor's witness for its first failed command. -/
def BodyCommandFailure (limits : Limits) (window : Nat) (framing : Header) (initial : Execute.State)
    (before : LSBReader) (input : List Bool) (command : Nat) (reason : Execute.LiteralSwitch.Error) : Prop :=
  ∃ last length header payload tail,
    framing = .compressed last length ∧
    CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
      .ok (header, payload) ∧
    Source before payload input tail ∧
    Execute.LiteralSwitch.BlockFailure header ⟨window, initial.output.size, length.size⟩
      (payloadLimits limits payload) payload command reason length.size 0
      (Execute.InsertCopy.State.start header initial) payload tail

/-- All earlier blocks finished successfully with a clear last flag.
    The failing command uses the cursor and state reached on the supplied input. -/
inductive CommandFailure (limits : Limits) (window block command : Nat)
    (reason : Execute.LiteralSwitch.Error) : Nat → Execute.State → LSBReader → List Bool → Prop where
  | here {initial : Execute.State} {before payload : LSBReader} {input tail : List Bool} {header : Header} :
      Stream.Internal.readHeader before = .ok (header, payload) →
      Stream.Internal.withinBits limits payload = .ok () →
      Source before payload input tail →
      BodyCommandFailure limits window header initial payload tail command reason →
      CommandFailure limits window block command reason block initial before input
  | more {index : Nat} {initial final : Execute.State} {before payload after : LSBReader}
      {input tail : List Bool} {header : Header} :
      Stream.Internal.readHeader before = .ok (header, payload) →
      Stream.Internal.withinBits limits payload = .ok () →
      Internal.readBody limits window index header initial payload = .ok (final, after) →
      header.last = false → Source before after input tail →
      CommandFailure limits window block command reason (index + 1) final after tail →
      CommandFailure limits window block command reason index initial before input

def CommandFailureWire (limits : Limits) (input : List UInt8) (block command : Nat)
    (reason : Execute.LiteralSwitch.Error) : Prop :=
  ∃ window reader code tail,
    Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, reader) ∧
    WindowWire window code ∧ bytesBits input = code ++ tail ∧ reader.totalRead = code.length ∧
    CommandFailure limits window block command reason 0 Execute.State.start reader tail

end Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch
