module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
public import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Defs

/-! Opt-in exact Brotli streams with insert-and-copy switching. One
    literal type and one distance type are required in each compressed
    meta-block. The command state starts afresh at every header. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Stream.InsertCopy

open Execute.InsertCopy (State Result)

inductive Error where
  | envelope (reason : Stream.Error)
  /-- Zero-based block and command indices, with the lower absolute bit coordinate. -/
  | command (block command : Nat) (reason : Execute.InsertCopy.Error)
  deriving DecidableEq, Repr

def commandBit : Execute.InsertCopy.Error → Nat
  | .literalBlockTypes bit | .distanceBlockTypes bit | .commandTree bit _ | .execute bit _ => bit
  | .switch reason => reason.bit

def Error.bit : Error → Nat
  | .envelope reason => reason.bit
  | .command _ _ reason => commandBit reason

def commandLimits (limits : Limits) (before : LSBReader) : Execute.Limits :=
  ⟨limits.output, limits.bits - before.totalRead⟩

inductive CommandsWire (header : CompressedHeader.Header) (block : Execute.Block) :
    State → List Bool → List (List UInt8) → State → Prop where
  | done {state : State} : state.execution.output.size = block.endOutput →
      CommandsWire header block state [] [] state
  | step {initial final : State} {result : Result} {head tail : List Bool}
      {chunk : List UInt8} {chunks : List (List UInt8)} :
      Execute.InsertCopy.Wire header block initial head result →
      result.execution.state.output.toList = initial.execution.output.toList ++ chunk →
      0 < chunk.length →
      CommandsWire header block result.state tail chunks final →
      CommandsWire header block initial (head ++ tail) (chunk :: chunks) final

/-- Every compressed payload starts with fresh category state. The
    execution state containing stream bytes and the distance ring is inherited. -/
def Payload : PayloadWire :=
  fun header block initial bits chunk final =>
    ∃ chunks runs, CommandsWire header block (State.start header initial) bits chunks ⟨final, runs⟩ ∧
      chunk = chunks.flatten

def Wire (input : List UInt8) (window : Nat) (chunks : List (List UInt8)) (final : Execute.State) : Prop :=
  WireWith Payload input window chunks final

namespace Internal

def runCommands (limits : Limits) (header : CompressedHeader.Header) (block : Execute.Block)
    (index : Nat) : Nat → Nat → State → LSBReader → Except Error (State × LSBReader)
  | fuel, command, initial, before =>
    if initial.execution.output.size = block.endOutput then .ok (initial, before)
    else match fuel with
    | 0 => .error (.envelope ⟨before.totalRead, some index, some command, .commandFuel⟩)
    | fuel + 1 => do
      let (result, after) ←
        (Execute.InsertCopy.read header block (commandLimits limits before) initial before).mapError
          (Error.command index command)
      runCommands limits header block index fuel (command + 1) result.state after

def readPayload : Stream.Internal.ReadPayload Error :=
  fun limits index _ header block initial before => do
    let (final, after) ← runCommands limits header block index block.length 0 (State.start header initial) before
    return (final.execution, after)

def readBody : Stream.Internal.ReadBody Error :=
  Stream.Internal.readBodyWith Error.envelope readPayload

end Internal

/-- Decode one exact standard-window stream in the insert-and-copy
    switching profile. Errors carry no partial output. -/
def decode : Limits → List UInt8 → Except Error Execute.State :=
  Stream.Internal.decodeWith Error.envelope Internal.readBody

/-- Successful commands preceding the first failure at the given cursor. -/
inductive PassedCommands (limits : Limits) (header : CompressedHeader.Header) (block : Execute.Block) :
    State → LSBReader → Nat → State → LSBReader → Prop where
  | none (state : State) (reader : LSBReader) : PassedCommands limits header block state reader 0 state reader
  | next {initial final : State} {result : Result} {before after stop : LSBReader} {passed : Nat} :
      Execute.InsertCopy.read header block (commandLimits limits before) initial before = .ok (result, after) →
      PassedCommands limits header block result.state after passed final stop →
      PassedCommands limits header block initial before (passed + 1) final stop

/-- Exact source suffix at a later cursor. -/
def Source (origin : Nat) (input : List Bool) (reader : LSBReader) (tail : List Bool) : Prop :=
  ∃ used, input = used ++ tail ∧ reader.totalRead = origin + used.length ∧ Brotli.Internal.Cursor reader tail

/-- A failed command reached from the real compressed table header.
    The lower witness pinpoints the operation within that command. -/
def BodyFailure (limits : Limits) (window : Nat) (framing : Header) (initial : Execute.State)
    (before : LSBReader) (input : List Bool) (command : Nat) (reason : Execute.InsertCopy.Error) : Prop :=
  ∃ last length header payload state reader tail,
    framing = .compressed last length ∧
    CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
      .ok (header, payload) ∧
    PassedCommands limits header ⟨window, initial.output.size, length.size⟩
      (State.start header initial) payload command state reader ∧
    command < length.size ∧ Source before.totalRead input reader tail ∧
    Execute.InsertCopy.Failure header ⟨window, initial.output.size, length.size⟩
      (commandLimits limits reader) state reader tail reason

/-- Every preceding meta-block completed successfully and had a clear
    last flag. The failing body is reached at its original cursor. -/
inductive CommandFailure (limits : Limits) (window : Nat) (block command : Nat)
    (reason : Execute.InsertCopy.Error) :
    Nat → Execute.State → LSBReader → List Bool → Prop where
  | here {initial : Execute.State} {before payload : LSBReader} {input tail : List Bool} {header : Header} :
      Stream.Internal.readHeader before = .ok (header, payload) →
      Stream.Internal.withinBits limits payload = .ok () →
      Source before.totalRead input payload tail →
      BodyFailure limits window header initial payload tail command reason →
      CommandFailure limits window block command reason block initial before input
  | more {index : Nat} {initial final : Execute.State} {before payload after : LSBReader}
      {input tail : List Bool} {header : Header} :
      Stream.Internal.readHeader before = .ok (header, payload) →
      Stream.Internal.withinBits limits payload = .ok () →
      Internal.readBody limits window index header initial payload = .ok (final, after) →
      header.last = false → Source before.totalRead input after tail →
      CommandFailure limits window block command reason (index + 1) final after tail →
      CommandFailure limits window block command reason index initial before input

def FailureWire (limits : Limits) (input : List UInt8) (block command : Nat)
    (reason : Execute.InsertCopy.Error) : Prop :=
  ∃ window reader code tail,
    Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, reader) ∧
    WindowWire window code ∧ bytesBits input = code ++ tail ∧ reader.totalRead = code.length ∧
    CommandFailure limits window block command reason 0 Execute.State.start reader tail

end Silmaril.Formats.Compression.Brotli.Stream.InsertCopy
