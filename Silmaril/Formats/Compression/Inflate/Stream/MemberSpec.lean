module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec

/-!
# Incremental member execution against the shared specifications

The actual header/body/trailer controller retains exactly `zlibTake` or
`gzipMember` after every finite schedule, including unfinished schedules.
Terminal success gives exact output and suffix; terminal failure rejects every
future input extension. Distinct chunks, versions and budgets can therefore
produce no disagreement when they complete on the same logical member input.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberMachine

open Silmaril.Formats.Compression
open MemberSemantics

def shared : Kind → List UInt8 → Option (List UInt8 × List UInt8)
  | .zlib, input => zlibTake input
  | .gzip, input => gzipMember input

end Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
