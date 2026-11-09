module

public import Silmaril.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Formats.Compression.Deflate.Stored
public import Silmaril.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Formats.Compression.Deflate.LZ77
public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Formats.Compression.Gzip.Basic

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

/-!
# Bounded history and suspendable overlapping MATCH copies

This candidate mathematical machine reads copied bytes from an explicitly
indexed, bounded chronological window. Each write updates that window before
the next read, so overlap is implemented rather than assumed. The unbounded
`output` field is an observable trace used by the correctness relation, not an
additional source buffer. The executable read depends only on `Window.bytes`.

The representation proved here is a chronological window, not zlib's physical
ring layout. A source bridge must separately relate saved ring memory and the
current caller buffer to it, account for pointers and capacities, and prove
the corresponding C/Ail/Core/IR execution. No such source claim is made here.
-/

/-- The maximum history distance admitted by DEFLATE. -/
def windowLimit : Nat := 32768

/-- Retain exactly the last available window's worth of bytes. -/
def keepWindow (bytes : List UInt8) : List UInt8 :=
  bytes.drop (bytes.length - windowLimit)

structure Window where
  bytes : List UInt8
deriving Repr, DecidableEq

def Window.Valid (w : Window) : Prop := w.bytes.length ≤ windowLimit

/-- The physical mathematical window contains the suffix of the logical trace. -/
def Window.Represents (w : Window) (output : List UInt8) : Prop :=
  w.bytes = keepWindow output

def Window.ofOutput (output : List UInt8) : Window := ⟨keepWindow output⟩

def Window.push (w : Window) (byte : UInt8) : Window :=
  ⟨keepWindow (w.bytes ++ [byte])⟩

/-- Index from the back of the available bounded window. The checked MATCH
entry below rejects zero and unavailable distances before using this lookup. -/
def Window.back (w : Window) (distance : Nat) : UInt8 :=
  w.bytes.getD (w.bytes.length - distance) 0

/-- The copy's next lookup uses the window after the previous byte's write. -/
def copyWindow (distance : Nat) : Nat → Window → List UInt8 → Window × List UInt8
  | 0, window, output => (window, output)
  | count + 1, window, output =>
    let byte := window.back distance
    copyWindow distance count (window.push byte) (output ++ [byte])

structure PendingMatch where
  distance : Nat
  remaining : Nat
  window : Window
  output : List UInt8
deriving Repr, DecidableEq

/-- Window/trace representation and the admitted distance. `remaining` is
arbitrary: the reusable copy rule does not need the token's separate ≤258 bound. -/
def PendingMatch.Valid (s : PendingMatch) : Prop :=
  s.window.Represents s.output ∧ 0 < s.distance ∧
    s.distance ≤ windowLimit ∧ s.distance ≤ s.output.length

/-- Checked availability depends only on the bounded machine state, not on
the unbounded observation trace. -/
def PendingMatch.DistanceAvailable (s : PendingMatch) : Prop :=
  0 < s.distance ∧ s.distance ≤ windowLimit ∧ s.distance ≤ s.window.bytes.length

instance (s : PendingMatch) : Decidable s.DistanceAvailable := inferInstanceAs
  (Decidable (0 < s.distance ∧ s.distance ≤ windowLimit ∧
    s.distance ≤ s.window.bytes.length))

/-- Perform exactly this many bytewise iterations. The public suspended step
below chooses a count bounded by both the pending length and offered capacity. -/
def PendingMatch.copyN (s : PendingMatch) (count : Nat) : PendingMatch :=
  let result := copyWindow s.distance count s.window s.output
  { s with remaining := s.remaining - count, window := result.1, output := result.2 }

def PendingMatch.advance (s : PendingMatch) (capacity : Nat) : PendingMatch :=
  s.copyN (min s.remaining capacity)

/-- New bytes offered to the caller in this chunk; the old trace is not copied
into a caller buffer again. -/
def PendingMatch.emitted (s : PendingMatch) (capacity : Nat) : List UInt8 :=
  (s.advance capacity).output.drop s.output.length

inductive MatchError where
  | invalidDistance
deriving Repr, DecidableEq

/-- Validate an active pending match, then spend the offered output capacity.
Validation is eager, even at zero capacity; this is a mathematical helper's
interface, not a claim about the ordering of C's error and buffer exits. -/
def PendingMatch.step (s : PendingMatch) (capacity : Nat) : Except MatchError PendingMatch :=
  if s.DistanceAvailable then .ok (s.advance capacity) else .error .invalidDistance

/-- Separate saved history from bytes produced in the current caller buffer.
The saved window is in chronological order, abstracting away a physical ring's
write index and the split at its wrap point. -/
structure BufferedHistory where
  saved : Window
  current : List UInt8
deriving Repr, DecidableEq

def BufferedHistory.window (s : BufferedHistory) : Window :=
  Window.ofOutput (s.saved.bytes ++ s.current)

/-- Publish the old current buffer into saved history before starting a fresh
caller buffer. No logical-history bytes change at this boundary. -/
def BufferedHistory.nextBuffer (s : BufferedHistory) : BufferedHistory :=
  ⟨s.window, []⟩

end Silmaril.Formats.Compression.Inflate.Stream
