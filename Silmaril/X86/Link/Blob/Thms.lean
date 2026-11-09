module

public import Silmaril.X86.Link.Blob.Defs
import Silmaril.Proofs.X86.Link.Blob

/-! # Byte blobs and kernel-fast ELF readers: theorems (header)

`Silmaril.Proofs.X86.Link.Blob` (PROVED, standard axioms): the fast readers are
the public certified readers on `Blob.bytesOf n len`:
`readLE_bytesOf`, `readHeader_bytesOf`, `readSectionHeaders_bytesOf`,
`readProgramHeaders_bytesOf`, `sectionData_bytesOf`,
`readObject_bytesOf : readObject (bytesOf n len) = readObjectN n len`,
`parse_bytesOf : ELFImage.parse policy (bytesOf n len) = parseN policy n len` (via
`recordsValidN_iff`: `parseN` checks `RecordsValid` on the file size and segment shapes
only, without materialising the file);
and `bytes_ofBytes : (Blob.ofBytes b).bytes = b`, so every byte array is a blob.
-/

@[expose] public section

namespace Silmaril.X86.Link.Blob

open Silmaril.Formats.ELF
open Silmaril.Process.LPS

theorem readLE_bytesOf (n len off w : Nat) :
    readLE (bytesOf n len) off w = readLEN n len off w :=
  Proofs.X86.Link.Blob.readLE_bytesOf n len off w

theorem readHeader_bytesOf (n len : Nat) : readHeader (bytesOf n len) = readHeaderN n len :=
  Proofs.X86.Link.Blob.readHeader_bytesOf n len

theorem readSectionHeaders_bytesOf (n len : Nat) (header : Header) :
    readSectionHeaders (bytesOf n len) header = readSectionHeadersN n len header :=
  Proofs.X86.Link.Blob.readSectionHeaders_bytesOf n len header

theorem readProgramHeaders_bytesOf (n len : Nat) (header : Header) :
    readProgramHeaders (bytesOf n len) header = readProgramHeadersN n len header :=
  Proofs.X86.Link.Blob.readProgramHeaders_bytesOf n len header

theorem sectionData_bytesOf (n len : Nat) (part : SectionHeader) :
    sectionData (bytesOf n len) part = sectionDataN n len part :=
  Proofs.X86.Link.Blob.sectionData_bytesOf n len part

/-- The public certified object reader, evaluated by arithmetic. -/
theorem readObject_bytesOf (n len : Nat) : readObject (bytesOf n len) = readObjectN n len :=
  Proofs.X86.Link.Blob.readObject_bytesOf n len

theorem recordsValidN_iff (policy : ELFImage.Policy) (n len : Nat) (records : ELFImage.Records) :
    RecordsValidN policy len records ↔ ELFImage.RecordsValid policy (bytesOf n len) records :=
  Proofs.X86.Link.Blob.recordsValidN_iff policy n len records

/-- The public checked ELF image extraction, evaluated by arithmetic. -/
theorem parse_bytesOf (policy : ELFImage.Policy) (n len : Nat) :
    ELFImage.parse policy (bytesOf n len) = parseN policy n len :=
  Proofs.X86.Link.Blob.parse_bytesOf policy n len

/-- Every byte array is the denotation of the blob `ofBytes` builds. -/
theorem bytes_ofBytes (b : Bytes) : (ofBytes b).bytes = b :=
  Proofs.X86.Link.Blob.bytes_ofBytes b

end Silmaril.X86.Link.Blob
