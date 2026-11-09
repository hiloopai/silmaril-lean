module

public import Silmaril.Formats.Compression.Deflate.Stored

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate.StoredWriter

/-!
# An aligned stored-block writer contract

These byte-level contracts are intended as the specification boundary for a C
stored-block writer. They do not assert that the C implementation meets it.

Unlike `storedBytes`, `blocksBytes` accepts arbitrary block boundaries. This
matters for streaming implementations, whose boundaries depend on the caller's
input and output buffer capacities. The decoder theorem needs only the 16-bit
payload bound for each block; it does not require a canonical partition.
-/

/-- With an initially empty bit buffer, `send_bits(last, 3); bi_windup()`
emits exactly this byte: BFINAL followed by BTYPE=00 and zero padding. -/
def headerByte (final : Bool) : UInt8 := if final then 1 else 0

/-- The five bytes emitted before copying an aligned stored-block payload. -/
def headerBytes (final : Bool) (len : Nat) : List UInt8 :=
  headerByte final :: storedLenBytes len

/-- An aligned writer appends a header and payload to the pending output.
The caller supplies the capacity and memory interpretation in a refinement. -/
def appendBlock (pending : List UInt8) (final : Bool) (chunk : List UInt8) : List UInt8 :=
  pending ++ (headerBytes final chunk.length ++ chunk)

/-- Serialize a chosen partition, marking only its last block final.
An empty partition emits one empty final block. -/
def blocksBytes : List (List UInt8) → List UInt8
  | [] => storedBlockBytes true []
  | chunk :: rest =>
      if rest = [] then storedBlockBytes true chunk
      else storedBlockBytes false chunk ++ blocksBytes rest

/-- The number of emitted blocks: even empty input needs a final block. -/
def blockCount (chunks : List (List UInt8)) : Nat := max 1 chunks.length

/-- A partition's validity is solely the 16-bit length bound on each payload. -/
def Valid (chunks : List (List UInt8)) : Prop :=
  ∀ chunk ∈ chunks, chunk.length ≤ storedMax

end Silmaril.Formats.Compression.Deflate.StoredWriter
