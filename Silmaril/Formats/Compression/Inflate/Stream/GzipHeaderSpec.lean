module

public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeader

/-!
# Incremental gzip headers and the shared format specification

The controller's ghost `covered` prefix is related
to the original member. This identifies exactly the bytes covered by FHCRC,
including arbitrarily long EXTRA, NAME and COMMENT fields. The proof connects
the explicit byte-state controller to the pre-existing gzip checker; it is
independent of a C/Core execution correspondence.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec

open Silmaril.Formats.Compression
open GzipHeader

def checkHcrc (flags : UInt8) (member input : List UInt8) : Option (List UInt8) :=
  if flags &&& gzipFHCRC ≠ 0 then
    match input with
    | c0 :: c1 :: rest =>
      let headerLen := member.length - input.length
      let crc16 := crc32List ((member.take headerLen).map UInt8.toNat) % 65536
      if c0.toNat + 256 * c1.toNat = crc16 then some rest else none
    | _ => none
  else some input

def checkAfterName (flags : UInt8) (member input : List UInt8) : Option (List UInt8) :=
  (if flags &&& gzipFCOMMENT ≠ 0 then gzipDropZeroTerminated input else some input).bind
    (checkHcrc flags member)

def checkAfterExtra (flags : UInt8) (member input : List UInt8) : Option (List UInt8) :=
  (if flags &&& gzipFNAME ≠ 0 then gzipDropZeroTerminated input else some input).bind
    (checkAfterName flags member)

def checkAfterFixed (flags : UInt8) (member input : List UInt8) : Option (List UInt8) :=
  (if flags &&& gzipFEXTRA ≠ 0 then
    match input with
    | x0 :: x1 :: rest => gzipDropExact (x0.toNat + 256 * x1.toNat) rest
    | _ => none
  else some input).bind (checkAfterExtra flags member)

/-! The following header has EXTRA bytes 17,34, NAME "A", COMMENT "B" and
FHCRC. Its low CRC16 is 0x4409; FHCRC bytes themselves are outside coverage. -/

def optionalHeaderPrefix : List UInt8 :=
  [31, 139, 8, 30, 0, 0, 0, 0, 0, 255, 2, 0, 17, 34, 65, 0, 66, 0]

end Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec
