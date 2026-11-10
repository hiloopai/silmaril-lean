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
public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Formats.Compression.Vectors

/-!
# Streaming inflater bit reservoir

A mathematical implementation of the inflater's
`PULLBYTE`, `NEEDBITS`, `BITS`, `DROPBITS` and `BYTEBITS` idioms. The accumulator
is an unbounded natural number; a machine-word correspondence must additionally
bound shifts and exclude overflow. No C, Ail, Core or machine-code correspondence
is claimed here.

Refilling changes the physical split between the accumulator and input, without
changing the logical unread bitstream. Suspension retains all partially pulled
bytes. `BYTEBITS` drops only the partial byte, retaining prefetched whole bytes.
`Normalizes` connects this representation to the canonical format reader via its
logical bitstream, rather than casting the accumulator record to that reader.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

/-- Low bits of `hold` precede the remaining input bytes. `consumed` is a logical
bit counter; pulling bytes does not increment it. -/
structure Reservoir where
  hold : Nat
  bits : Nat
  input : List UInt8
  consumed : Nat
  deriving Repr, DecidableEq

namespace Reservoir

def Valid (s : Reservoir) : Prop := s.hold < 2 ^ s.bits

def unread (s : Reservoir) : List Bool :=
  natBits s.hold s.bits ++ bytesBits s.input

def ofBytes (bytes : List UInt8) : Reservoir := ⟨0, 0, bytes, 0⟩

def feed (s : Reservoir) (bytes : List UInt8) : Reservoir :=
  { s with input := s.input ++ bytes }

/-- Mathematical `PULLBYTE`, appending a byte above the buffered low bits. -/
def pullByte (s : Reservoir) : Option Reservoir :=
  match s.input with
  | [] => none
  | byte :: rest =>
    some { s with
      hold := s.hold + byte.toNat * 2 ^ s.bits
      bits := s.bits + 8
      input := rest }

/-- Mathematical `BITS(n)`, including the useful total extension at zero bits. -/
def lowBits (s : Reservoir) (n : Nat) : Nat := s.hold % 2 ^ n

/-- Mathematical `DROPBITS(n)`. Its semantic contract requires `n ≤ s.bits`. -/
def dropBits (s : Reservoir) (n : Nat) : Reservoir :=
  { s with hold := s.hold / 2 ^ n, bits := s.bits - n, consumed := s.consumed + n }

/-- Mathematical `BYTEBITS()`: preserve every complete prefetched byte. -/
def byteBits (s : Reservoir) : Reservoir := s.dropBits (s.bits % 8)

end Reservoir

inductive NeedResult where
  | ready (state : Reservoir)
  | needInput (state : Reservoir)
  deriving Repr, DecidableEq

def NeedResult.state : NeedResult → Reservoir
  | .ready s | .needInput s => s

namespace Reservoir

/-- Structural recursion on available input is the execution bound. -/
def needBitsAux (required consumed : Nat) : List UInt8 → Nat → Nat → NeedResult
  | [], hold, bits =>
    let s : Reservoir := ⟨hold, bits, [], consumed⟩
    if required ≤ bits then .ready s else .needInput s
  | byte :: rest, hold, bits =>
    if required ≤ bits then .ready ⟨hold, bits, byte :: rest, consumed⟩
    else needBitsAux required consumed rest (hold + byte.toNat * 2 ^ bits) (bits + 8)

/-- `NEEDBITS`: on suspension the result contains the partially refilled state. -/
def needBits (required : Nat) (s : Reservoir) : NeedResult :=
  needBitsAux required s.consumed s.input s.hold s.bits

end Reservoir

inductive ReadResult where
  | value (value : Nat) (state : Reservoir)
  | needInput (state : Reservoir)
  deriving Repr, DecidableEq

namespace Reservoir

def readBits (n : Nat) (s : Reservoir) : ReadResult :=
  match needBits n s with
  | .ready filled => .value (filled.lowBits n) (filled.dropBits n)
  | .needInput filled => .needInput filled

/-! ## `NEEDBITS` contracts -/

/-- A result preserves all unread bits and the consumed counter. Ready states
have enough bits; suspended states have exhausted input and still need bits. -/
def NeedSound (required : Nat) (before : Reservoir) (result : NeedResult) : Prop :=
  result.state.Valid ∧ result.state.unread = before.unread ∧
    result.state.consumed = before.consumed ∧ result.state.bits % 8 = before.bits % 8 ∧
    match result with
    | .ready s => required ≤ s.bits
    | .needInput s => s.input = [] ∧ s.bits < required

/-- A successful read consumes exactly its value's bits; a suspended read
consumes no logical bits and retains the partial reservoir. -/
def ReadSound (n : Nat) (before : Reservoir) (result : ReadResult) : Prop :=
  match result with
  | .value value after =>
    after.Valid ∧ value < 2 ^ n ∧
      before.unread = natBits value n ++ after.unread ∧
      after.consumed = before.consumed + n ∧
      after.bits % 8 = (before.bits + 7 * n) % 8
  | .needInput after =>
    after.Valid ∧ after.unread = before.unread ∧ after.consumed = before.consumed ∧
      after.bits % 8 = before.bits % 8 ∧ after.input = [] ∧ after.bits < n

/-! ## An explicit canonical-reader normalization -/

/-- Re-encode buffered complete bytes in low-to-high order. -/
def bufferedBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofNat v :: bufferedBytes n (v / 256)

def normalize (s : Reservoir) : LSBReader :=
  { buffer := s.hold % 2 ^ (s.bits % 8), count := s.bits % 8,
    input := bufferedBytes (s.bits / 8) (s.hold / 2 ^ (s.bits % 8)) ++ s.input,
    totalRead := s.consumed }

/-- A canonical reader keeps at most one partial byte. Prefetched complete
bytes have moved into its logical input, preserving both bits and position. -/
def Normalizes (s : Reservoir) (r : LSBReader) : Prop :=
  s.Valid ∧ r.count = s.bits % 8 ∧ r.Rep s.unread ∧ r.totalRead = s.consumed

/-! ## Successful canonical reads remain valid after input extension -/

def readerFeed (r : LSBReader) (added : List UInt8) : LSBReader :=
  { r with input := r.input ++ added }

end Reservoir
end Silmaril.Formats.Compression.Inflate.Stream
