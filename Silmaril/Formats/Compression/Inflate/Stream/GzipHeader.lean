module

public import Silmaril.Formats.Compression.Inflate.Stream.ContainerFields
public import Silmaril.Formats.Compression.Inflate.Stream.RawContainers

/-!
# An incremental gzip header controller

Each active step consumes at most one byte. Optional
EXTRA, NAME and COMMENT fields retain their own continuation state, so arbitrary
chunk boundaries never restart header parsing. Neither an eventual input length
nor semantic parsing fuel is stored. `covered` is a mathematical trace of the
header bytes covered by FHCRC; a later representation proof can replace it by
an incremental CRC accumulator. FHCRC's own bytes are excluded from that trace.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.GzipHeader

open Silmaril.Formats.Compression

inductive Phase where
  | magic1 | magic2 | method | flags
  | fixedTail (remainingAfterByte : Nat)
  | xlenLow | xlenHigh (low : UInt8)
  | extra (remainingAfterByte : Nat)
  | name | comment
  | hcrcLow | hcrcHigh (low : UInt8)
  | done | bad
  deriving Repr, DecidableEq

structure Control where
  phase : Phase
  flags : UInt8
  covered : List UInt8
  deriving Repr, DecidableEq

def afterComment (flags : UInt8) : Phase :=
  if flags &&& gzipFHCRC ≠ 0 then .hcrcLow else .done

def afterName (flags : UInt8) : Phase :=
  if flags &&& gzipFCOMMENT ≠ 0 then .comment else afterComment flags

def afterExtra (flags : UInt8) : Phase :=
  if flags &&& gzipFNAME ≠ 0 then .name else afterName flags

def afterFixed (flags : UInt8) : Phase :=
  if flags &&& gzipFEXTRA ≠ 0 then .xlenLow else afterExtra flags

def Control.active (control : Control) : Bool :=
  control.phase != .done && control.phase != .bad

def Control.advance (control : Control) (byte : UInt8) : Control :=
  let append (phase : Phase) : Control :=
    { control with phase := phase, covered := control.covered ++ [byte] }
  match control.phase with
  | .magic1 => append (if byte = 0x1f then .magic2 else .bad)
  | .magic2 => append (if byte = 0x8b then .method else .bad)
  | .method => append (if byte = 8 then .flags else .bad)
  | .flags =>
    { phase := if byte &&& gzipFRESERVED = 0 then .fixedTail 5 else .bad,
      flags := byte, covered := control.covered ++ [byte] }
  | .fixedTail 0 => append (afterFixed control.flags)
  | .fixedTail (remaining + 1) => append (.fixedTail remaining)
  | .xlenLow => append (.xlenHigh byte)
  | .xlenHigh low =>
    let length := low.toNat + 256 * byte.toNat
    append (if length = 0 then afterExtra control.flags else .extra (length - 1))
  | .extra 0 => append (afterExtra control.flags)
  | .extra (remaining + 1) => append (.extra remaining)
  | .name => append (if byte = 0 then afterName control.flags else .name)
  | .comment => append (if byte = 0 then afterComment control.flags else .comment)
  | .hcrcLow => { control with phase := .hcrcHigh byte }
  | .hcrcHigh low =>
    { control with phase :=
      if low.toNat + 256 * byte.toNat = crc32List (control.covered.map UInt8.toNat) % 65536
      then .done else .bad }
  | .done | .bad => control

def initialControl : Control := ⟨.magic1, 0, []⟩

/-- Logical continuation meaning, recursive only in the available logical
input. This evaluator is used in proofs; physical steps retain their phase. -/
def evaluate (control : Control) (input : List UInt8) : Option (List UInt8) :=
  match control.phase with
  | .done => some input
  | .bad => none
  | _ =>
    match input with
    | [] => none
    | byte :: rest => evaluate (control.advance byte) rest
termination_by input

structure Machine where
  control : Control
  reservoir : Reservoir
  deriving Repr, DecidableEq

namespace Machine

def start (input : List UInt8) : Machine := ⟨initialControl, Reservoir.ofBytes input⟩

def feed (machine : Machine) (added : List UInt8) : Machine :=
  { machine with reservoir := machine.reservoir.feed added }

def isDone (machine : Machine) : Bool := machine.control.phase == .done
def isBad (machine : Machine) : Bool := machine.control.phase == .bad

/-- One physical header-byte step; lack of input preserves the exact phase. -/
def step (machine : Machine) : Machine :=
  if machine.control.active then
    match Reservoir.readBits 8 machine.reservoir with
    | .needInput rest => { machine with reservoir := rest }
    | .value value rest => ⟨machine.control.advance (UInt8.ofNat value), rest⟩
  else machine

def runSteps (machine : Machine) (steps : Nat) : Machine :=
  match steps with
  | 0 => machine
  | steps + 1 => (machine.step).runSteps steps

def denote (machine : Machine) (reader : LSBReader) : Option (List UInt8) :=
  evaluate machine.control reader.input

/-- Successful byte-boundary observation retains the complete logical cursor,
so the raw DEFLATE controller can continue without resetting `totalRead`. -/
def denoteReader (machine : Machine) (reader : LSBReader) : Option LSBReader :=
  (machine.denote reader).map fun rest =>
    ContainerFields.alignedReader rest
      (reader.totalRead + 8 * (reader.input.length - rest.length))

end Machine

end Silmaril.Formats.Compression.Inflate.Stream.GzipHeader
