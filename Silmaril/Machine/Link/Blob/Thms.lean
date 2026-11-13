module

public import Silmaril.Machine.Link.Blob.Defs
public import Silmaril.Proofs.Machine.Link.Blob

/-! # Byte blobs and kernel-fast ELF readers: theorems (header)

`Silmaril.Proofs.Machine.Link.Blob` (PROVED, standard axioms): the fast readers are
the public certified readers on `Blob.bytesOf n len`:
`readLE_bytesOf`, `readHeader_bytesOf`, `readSectionHeaders_bytesOf`,
`readProgramHeaders_bytesOf`, `sectionData_bytesOf`,
`readObject_bytesOf : readObject (bytesOf n len) = readObjectN n len`,
`parse_bytesOf : ELFImage.parse policy (bytesOf n len) = parseN policy n len` (via
`recordsValidN_iff`: `parseN` checks `RecordsValid` on the file size and segment shapes
only, without materialising the file);
and `bytes_ofBytes : (Blob.ofBytes b).bytes = b`, so every byte array is a blob.
-/
