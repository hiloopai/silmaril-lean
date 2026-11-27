module

public import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Defs

/-! Exact standard-window RFC 7932 streams with the static dictionary. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Stream.Dictionary

open Literal.Switch (Source)
open Execute.DistanceSwitch (BlockError)

structure Limits where
  framing : Stream.Limits
  /-- Total compressed command slots across all meta-blocks. -/
  commands : Nat
  deriving DecidableEq, Repr

structure State where
  execution : Execute.State
  remainingCommands : Nat

namespace Internal

def body : Stream.Internal.ReadBodyState DistanceSwitch.Error State :=
  fun limits window index frame state before =>
    let remaining := state.remainingCommands
    Stream.Internal.readBodyWithResult DistanceSwitch.Error.envelope
      (fun execution cursor => (⟨execution, remaining⟩, cursor))
      (fun limits index _ header block initial payload => do
        let result ← (Execute.DistanceSwitch.Dictionary.readBlockCounted header block.windowBits block.length
          remaining (DistanceSwitch.payloadLimits limits payload) initial payload).mapError
            (DistanceSwitch.Error.block index)
        return (⟨result.state.execution, result.remainingCommands⟩, result.cursor))
      limits window index frame state.execution before

end Internal

/-- Decode one exact Brotli stream and return the unused command slots.
    Output, bit and block caps include the entire original stream. -/
def decode (limits : Limits) (input : List UInt8) : Except DistanceSwitch.Error State :=
  Stream.Internal.decodeWithState DistanceSwitch.Error.envelope Internal.body
    ⟨Execute.State.start, limits.commands⟩ limits.framing input

open Execute.DistanceSwitch.Dictionary (FailurePath)

inductive BodyWire (limits : Stream.Limits) (window position : Nat) :
    Header → State → List Bool → List UInt8 → Nat → State → Prop where
  | terminal (state : State) : BodyWire limits window position .terminal state [] [] 0 state
  | raw {length : RawLength} {state : State} {bytes : List UInt8} : bytes.length = length.size →
      BodyWire limits window position (.raw length) state (padding position ++ bytesBits bytes) bytes 0
        { state with execution := { state.execution with output := state.execution.output ++ bytes.toArray } }
  | metadata {last : Bool} {length : MetadataLength} (state : State) {bytes : List UInt8} :
      bytes.length = length.size →
      BodyWire limits window position (.metadata last length) state (padding position ++ bytesBits bytes) [] 0 state
  | compressed {last : Bool} {length : RawLength} {header : CompressedHeader.Header} {work remaining : Nat}
      {initial : State} {final : Execute.InsertCopy.State} {payload after : LSBReader}
      {tableBits commandBits input suffix : List Bool} {chunks : List (List UInt8)} :
      CompressedHeader.Wire work tableBits header →
      payload.totalRead = position + tableBits.length →
      Execute.DistanceSwitch.Dictionary.CommandsWire header ⟨window, initial.execution.output.size, length.size⟩
        (DistanceSwitch.payloadLimits limits payload) payload
        (Execute.InsertCopy.State.start header initial.execution) payload input suffix chunks final after →
      Source payload after input commandBits suffix →
      chunks.length + remaining = initial.remainingCommands →
      BodyWire limits window position (.compressed last length) initial (tableBits ++ commandBits)
        chunks.flatten chunks.length ⟨final.execution, remaining⟩

inductive BodyFailure (limits : Stream.Limits) (window index : Nat) (frame : Header)
    (initial : State) (before : LSBReader) (input : List Bool) : DistanceSwitch.Error → Prop where
  | envelope {cause : Cause} : FailedOperation limits before cause →
      BodyFailure limits window index frame initial before input
        (.envelope ⟨before.totalRead, some index, none, cause⟩)
  | payload {last : Bool} {length : RawLength} {header : CompressedHeader.Header} {payload : LSBReader}
      {tableBits suffix used unread : List Bool} {reason : BlockError} :
      frame = .compressed last length →
      CompressedHeader.read ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before =
        .ok (header, payload) →
      Source before payload input tableBits suffix →
      FailurePath header ⟨window, initial.execution.output.size, length.size⟩
        (DistanceSwitch.payloadLimits limits payload) payload initial.remainingCommands 0
        (Execute.InsertCopy.State.start header initial.execution) payload suffix reason →
      suffix = used ++ unread → reason.bit = payload.totalRead + used.length →
      BodyFailure limits window index frame initial before input (.block index reason)

/-- The original header and body reads, with the unmodified continuation. -/
structure Passed (limits : Stream.Limits) (window index : Nat) (frame : Header)
    (initial next : State) (before after : LSBReader) (input tail : List Bool)
    (chunk : List UInt8) (commands : Nat) : Prop where
  parts : ∃ body used,
    Stream.Internal.readHeader before = .ok (frame, body) ∧ Stream.Internal.withinBits limits body = .ok () ∧
    frame.Valid ∧ input = (frame.bits ++ used) ++ tail ∧
    after.totalRead = before.totalRead + (frame.bits ++ used).length ∧
    BodyWire limits window (before.totalRead + frame.bits.length) frame initial used chunk commands next ∧
    Internal.body limits window index frame initial body = .ok (next, after)

/-- A walk through actual meta-blocks to the first failure or exact end. -/
inductive Walk (limits : Stream.Limits) (window : Nat) :
    Nat → Nat → State → LSBReader → List Bool → Except DistanceSwitch.Error State → Prop where
  | fuel {index : Nat} {state : State} {before : LSBReader} {input : List Bool} :
      Walk limits window 0 index state before input
        (.error (.envelope ⟨before.totalRead, some index, none, .framing .stepLimit⟩))
  | header {fuel index : Nat} {state : State} {before : LSBReader} {input : List Bool} {reason : Brotli.Error} :
      Stream.Internal.readHeader before = .error reason →
      Walk limits window (fuel + 1) index state before input
        (.error (.envelope ⟨before.totalRead, some index, none, .framing reason⟩))
  | headerBits {fuel index : Nat} {state : State} {before body : LSBReader} {input : List Bool}
      {frame : Header} {cause : Cause} :
      Stream.Internal.readHeader before = .ok (frame, body) → Stream.Internal.withinBits limits body = .error cause →
      Walk limits window (fuel + 1) index state before input
        (.error (.envelope ⟨before.totalRead, some index, none, cause⟩))
  | body {fuel index : Nat} {state : State} {before body : LSBReader} {input tail : List Bool}
      {frame : Header} {error : DistanceSwitch.Error} :
      Stream.Internal.readHeader before = .ok (frame, body) → Stream.Internal.withinBits limits body = .ok () →
      Source before body input frame.bits tail →
      Internal.body limits window index frame state body = .error error →
      BodyFailure limits window index frame state body tail error →
      Walk limits window (fuel + 1) index state before input (.error error)
  | finishError {fuel index commands : Nat} {initial next : State} {before after : LSBReader}
      {input tail : List Bool} {chunk : List UInt8} {frame : Header} {cause : Cause} :
      Passed limits window index frame initial next before after input tail chunk commands →
      frame.last = true → Stream.Internal.finish limits after = .error cause →
      Walk limits window (fuel + 1) index initial before input
        (.error (.envelope ⟨after.totalRead, some index, none, cause⟩))
  | last {fuel index commands : Nat} {initial next : State} {before after endCursor : LSBReader}
      {input tail : List Bool} {chunk : List UInt8} {frame : Header} :
      Passed limits window index frame initial next before after input tail chunk commands →
      frame.last = true → Stream.Internal.finish limits after = .ok endCursor →
      tail = padding after.totalRead → before.totalRead + input.length ≤ limits.bits →
      next.execution.output.size ≤ limits.output →
      Walk limits window (fuel + 1) index initial before input (.ok next)
  | more {fuel index commands : Nat} {initial next : State} {before after : LSBReader}
      {input tail : List Bool} {chunk : List UInt8} {frame : Header} {outcome : Except DistanceSwitch.Error State} :
      Passed limits window index frame initial next before after input tail chunk commands →
      frame.last = false → Walk limits window fuel (index + 1) next after tail outcome →
      Walk limits window (fuel + 1) index initial before input outcome

inductive Wire (limits : Limits) (input : List UInt8) : Except DistanceSwitch.Error State → Prop where
  | inputLimit : limits.framing.input < input.length →
      Wire limits input (.error (.envelope ⟨0, none, none, .framing .inputLimit⟩))
  | window {reason : Brotli.Error} :
      input.length ≤ limits.framing.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .error reason →
      Wire limits input (.error (.envelope ⟨0, none, none, .framing reason⟩))
  | windowBits {window : Nat} {cursor : LSBReader} {cause : Cause} :
      input.length ≤ limits.framing.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, cursor) →
      Stream.Internal.withinBits limits.framing cursor = .error cause →
      Wire limits input (.error (.envelope ⟨0, none, none, cause⟩))
  | windowLimit {window : Nat} {cursor : LSBReader} :
      input.length ≤ limits.framing.input →
      Brotli.Internal.readWindow (Brotli.Internal.start input) = .ok (window, cursor) →
      Stream.Internal.withinBits limits.framing cursor = .ok () → limits.framing.window < windowSize window →
      Wire limits input (.error (.envelope ⟨0, none, none, .framing .windowLimit⟩))
  | blocks {window : Nat} {cursor : LSBReader} {code tail : List Bool} {outcome : Except DistanceSwitch.Error State} :
      input.length ≤ limits.framing.input →
      WindowWire window code → windowSize window ≤ limits.framing.window →
      Source (Brotli.Internal.start input) cursor (bytesBits input) code tail →
      Walk limits.framing window limits.framing.blocks 0 ⟨Execute.State.start, limits.commands⟩ cursor tail outcome →
      Wire limits input outcome

end Silmaril.Formats.Compression.Brotli.Stream.Dictionary
