module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberMachine

/-!
# Executed incremental member-controller witnesses

These kernel-checked examples execute the combined
header/body/checksum/trailer controller for both abstract version dispatchers.
The stored-A wrappers have independently been decoded by native zlib; its
Adler-32 is 0x00420042 and its CRC-32 is 0xd3d99e8b. Headers and trailers arrive
in separate buffers, including buffers splitting individual checksum fields.
These witnesses are not C execution or source compilation certificates.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberExamples

open Silmaril.Formats.Compression

def call (input : List UInt8) (capacity : Nat) : RawMachine.Call := ⟨input, 64, capacity⟩

def copyRemaining : MemberMachine → Option Nat
  | .body _ checked =>
    match checked.machine with
    | .storedCopy _ remaining _ => some remaining
    | _ => none
  | _ => none

def trailerRejected : MemberMachine → Bool
  | .bad .trailer _ => true
  | _ => false

/-! ## Split zlib header, an output stall, and a split Adler-32 trailer -/

def zlibNeedsHeader (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (MemberMachine.start .zlib [0x78]) (call [] 0)

def zlibEntered (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (zlibNeedsHeader version) (call [0x01, 1, 1, 0, 0xfe, 0xff, 65] 0)

def zlibCopyReady (version : Version) : MemberMachine :=
  MemberMachine.runCalls version (zlibEntered version) (List.replicate 2 (call [] 0))

def zlibOutputStall (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (zlibCopyReady version) (call [] 0)

def zlibNeedsTrailer (version : Version) : MemberMachine :=
  MemberMachine.runCalls version (zlibOutputStall version) [call [] 1, call [] 0, call [] 0]

def zlibSplitTrailer (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (zlibNeedsTrailer version) (call [0, 66] 0)

def zlibDone (version : Version) (tail : List UInt8) : MemberMachine :=
  MemberMachine.applyCall version (zlibSplitTrailer version) (call ([0, 66] ++ tail) 0)

def zlibTrailerTail : Parser (Option Unit) :=
  ContainerFields.byte.bind fun b2 => ContainerFields.byte.bind fun b3 =>
    .pure (if be32Val 0 66 b2 b3 = 0x00420042 then some () else none)

/-! ## Gzip's byte-at-a-time header and a trailer split inside CRC and ISIZE -/

def gzipFirstMagic (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (MemberMachine.start .gzip [31]) (call [] 0)

def gzipNeedsHeader (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipFirstMagic version) (call [] 0)

def gzipHeaderRest (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipNeedsHeader version)
    (call [139, 8, 0, 0, 0, 0, 0, 0, 255, 1, 1, 0, 0xfe, 0xff, 65] 0)

def gzipEntered (version : Version) : MemberMachine :=
  MemberMachine.runCalls version (gzipHeaderRest version) (List.replicate 9 (call [] 0))

def gzipCopyReady (version : Version) : MemberMachine :=
  MemberMachine.runCalls version (gzipEntered version) (List.replicate 2 (call [] 0))

def gzipOutputStall (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipCopyReady version) (call [] 0)

def gzipNeedsTrailer (version : Version) : MemberMachine :=
  MemberMachine.runCalls version (gzipOutputStall version) [call [] 1, call [] 0, call [] 0]

def gzipSplitCRC (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipNeedsTrailer version) (call [139, 158, 217] 0)

def gzipSplitISIZE (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipSplitCRC version) (call [211, 1, 0] 0)

def gzipDone (version : Version) (tail : List UInt8) : MemberMachine :=
  MemberMachine.applyCall version (gzipSplitISIZE version) (call ([0, 0] ++ tail) 0)

def gzipTrailerTail : Parser (Option Unit) :=
  ContainerFields.byte.bind fun i2 => ContainerFields.byte.bind fun i3 =>
    .pure (if le32Val 139 158 217 211 = 0xd3d99e8b ∧
      le32Val 1 0 i2 i3 = 1 % 4294967296 then some () else none)

def gzipWrongCRC (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipNeedsTrailer version)
    (call [138, 158, 217, 211, 1, 0, 0, 0] 0)

def gzipWrongISIZE (version : Version) : MemberMachine :=
  MemberMachine.applyCall version (gzipNeedsTrailer version)
    (call [139, 158, 217, 211, 2, 0, 0, 0] 0)

/-! ## Fixed Huffman with an overlapping match and one-byte output calls -/

/-- Two literal As followed by a length-six, distance-one overlapping match.
The wrappers and checksums were independently decoded by native zlib 1.2.12.
The final AA/BB bytes belong to the caller, beyond this member. -/
def fixedZlib (version : Version) : MemberMachine :=
  MemberMachine.runCalls version
    (MemberMachine.start .zlib [120, 1, 115, 116, 132, 0, 0, 9, 44, 2, 9, 0xaa, 0xbb])
    (List.replicate 32 (call [] 1))

def fixedGzip (version : Version) : MemberMachine :=
  MemberMachine.runCalls version
    (MemberMachine.start .gzip
      [31, 139, 8, 0, 0, 0, 0, 0, 0, 255, 115, 116, 132, 0, 0,
        10, 28, 183, 121, 8, 0, 0, 0, 0xaa, 0xbb])
    (List.replicate 32 (call [] 1))

end Silmaril.Formats.Compression.Inflate.Stream.MemberExamples
