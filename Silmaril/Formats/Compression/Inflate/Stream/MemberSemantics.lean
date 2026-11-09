module

public import Silmaril.Formats.Compression.Inflate.Stream.ContainerFields
public import Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset
public import Silmaril.Formats.Compression.Inflate.Stream.RawContainers
public import Silmaril.Formats.Compression.Inflate.Stream.Protocol

/-!
# Shared mathematical meaning of zlib and gzip members

Raw continuation semantics is composed with the
resumable trailer parsers and related to the existing container specifications.
Absolute reader positions can include an already consumed header; resetting
that counter is unnecessary. These observations describe one member, with its
untouched suffix, and exclude preset dictionaries as the shared zlib spec does.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics

open Silmaril.Formats.Compression

inductive Kind where
  | zlib
  | gzip
  deriving Repr, DecidableEq

def Kind.checksumKind : Kind → Protocol.ChecksumKind
  | .zlib => .adler32
  | .gzip => .crc32

def trailer : Kind → List UInt8 → Parser (Option Unit)
  | .zlib, output => ContainerFields.zlibTrailer output
  | .gzip, output => ContainerFields.gzipTrailer output

abbrev Result := Option (List UInt8 × LSBReader)

/-- Validate the member trailer at the raw decoder's exact final reader.
Incomplete fields and validation failures both have the shared `none` view. -/
def afterRaw (kind : Kind) : RawSemantics.Result → Result
  | .error _ => none
  | .ok (output, reader) =>
    (ContainerFields.validationReader ((trailer kind output).eval reader)).map
      (fun rest => (output, rest))

def body (kind : Kind) (reader : LSBReader) : Result :=
  afterRaw kind (RawSemantics.format reader [])

def inputView (result : Result) : Option (List UInt8 × List UInt8) :=
  result.map (fun pair => (pair.1, pair.2.input))

def checkTrailer : Kind → List UInt8 → List UInt8 → Option (List UInt8)
  | .zlib, output, input => zlibCheckTrailer output input
  | .gzip, output, input => gzipCheckTrailer output input

/-- The byte-list observation of raw decoding followed by trailer validation. -/
def finishView (kind : Kind) :
    Except Deflate.DecompressError (List UInt8 × List UInt8) → Option (List UInt8 × List UInt8)
  | .error _ => none
  | .ok (output, input) => (checkTrailer kind output input).map (fun rest => (output, rest))

end Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics
