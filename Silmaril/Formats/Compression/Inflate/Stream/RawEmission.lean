module

public import Silmaril.Formats.Compression.Inflate.Stream.RawMachine
public import Silmaril.Formats.Compression.Inflate.Stream.Checksums

/-!
# Output prefixes and incremental checksums of the raw controller

Every controller step appends at most the offered
capacity, even if its state or input is malformed. The emitted suffix is the
newly produced byte sequence; checksums can therefore advance from that suffix
alone. These are logical-output laws, not C pointer or buffer-ownership claims.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawEmission

open Silmaril.Formats.Compression

def stepEmitted (version : Version) (machine : RawMachine) (fuel capacity : Nat) : List UInt8 :=
  (RawMachine.step version machine fuel capacity).output.drop machine.output.length

/-- Feeding changes no already-produced bytes. This is the suffix produced
by the controller work in one caller invocation. -/
def callEmitted (version : Version) (machine : RawMachine) (call : RawMachine.Call) : List UInt8 :=
  stepEmitted version (machine.feed call.input) call.schedulerFuel call.capacity

def runEmitted (version : Version) (machine : RawMachine) (calls : List RawMachine.Call) : List UInt8 :=
  (RawMachine.runCalls version machine calls).output.drop machine.output.length

/-- A checksum accumulator that hashes only each invocation's new bytes. -/
def runChecksum (kind : Protocol.ChecksumKind) (version : Version) :
    RawMachine → Nat → List RawMachine.Call → Nat
  | _, seed, [] => seed
  | machine, seed, call :: calls =>
    runChecksum kind version (RawMachine.applyCall version machine call)
      (Checksums.update kind seed (callEmitted version machine call)) calls

end Silmaril.Formats.Compression.Inflate.Stream.RawEmission
