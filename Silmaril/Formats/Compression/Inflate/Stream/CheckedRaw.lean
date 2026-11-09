module

public import Silmaril.Formats.Compression.Inflate.Stream.RawEmission
public import Silmaril.Formats.Compression.Inflate.Stream.RawRuns

/-!
# Raw decoding with incrementally accumulated checksum and size

A checked state carries the current data checksum
and the output size modulo 2^32. Each step hashes only that step's emitted
suffix, preserving the existing raw continuation under all future input.
These are mathematical member-data counters, not public C cursors or an
incremental header/trailer implementation. Dictionary installation needs a
separate initial-history interface.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw

open Silmaril.Formats.Compression

structure State where
  machine : RawMachine
  check : Nat
  size : Nat

def State.output (state : State) : List UInt8 := state.machine.output
def State.reservoir (state : State) : Reservoir := state.machine.reservoir
def State.window (state : State) : Window := state.machine.window

/-- Initializing from an existing logical machine accounts for all its prior
output. Normal decoding starts from `start`, whose output is empty. -/
def ofMachine (kind : Protocol.ChecksumKind) (machine : RawMachine) : State :=
  ⟨machine, Checksums.checksum kind machine.output, machine.output.length % Protocol.word32⟩

def start (kind : Protocol.ChecksumKind) (input : List UInt8) : State :=
  ofMachine kind (RawMachine.start input)

def feed (state : State) (input : List UInt8) : State :=
  { state with machine := state.machine.feed input }

/-- The checksum update reads only newly emitted bytes, rather than hashing
the old logical output again at a trailer boundary. -/
def step (kind : Protocol.ChecksumKind) (version : Version) (state : State)
    (fuel capacity : Nat) : State :=
  let emitted := RawEmission.stepEmitted version state.machine fuel capacity
  ⟨RawMachine.step version state.machine fuel capacity,
    Checksums.update kind state.check emitted,
    (state.size + emitted.length) % Protocol.word32⟩

def Invariant (kind : Protocol.ChecksumKind) (state : State) : Prop :=
  state.check = Checksums.checksum kind state.machine.output ∧
    state.size = state.machine.output.length % Protocol.word32

end Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw
