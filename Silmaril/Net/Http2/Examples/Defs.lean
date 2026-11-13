module

public import Silmaril.Net.Http2.Frame.Thms
public import Silmaril.Net.Http2.Fields.Thms
public import Silmaril.Net.Hpack.Block.Thms

@[expose] public section

/-!
# HTTP/2 examples: a request from octets to validated fields

The pieces composed on one input: a HEADERS frame is read (`readFrame`, RFC 9113 §4.1), its
field block is decoded against the connection's HPACK table (RFC 7541 §3.2) and the resulting
header section is checked (RFC 9113 §8.3.1). The frame carries the first request of RFC 7541
Appendix C.3.1 on stream 1, with END_STREAM and END_HEADERS and no padding or priority.

`headersBlock` is a deliberately small HEADERS reader (no PADDED or PRIORITY flags, no
CONTINUATION); the full HEADERS/CONTINUATION payload grammar of §6.2 and §6.10 is roadmap work.
-/

namespace Silmaril.Net.Http2.Examples

open Silmaril.Net.Hpack

/-- The field block of a HEADERS frame that has END_HEADERS and neither PADDED nor PRIORITY. -/
def headersBlock (f : Frame) : Option (List UInt8) :=
  if f.header.type = FrameType.headers.code ∧ hasFlag f.header.flags flagEndHeaders ∧
      !hasFlag f.header.flags flagPadded ∧ !hasFlag f.header.flags flagPriority ∧
      f.header.streamId ≠ 0
  then some f.payload else none

/-- Read a HEADERS frame and decode and validate its request header section. -/
def readRequest (t : DynTable) (xs : List UInt8) : Option (List Entry × DynTable) :=
  match readFrame 16384 xs with
  | .error _ => none
  | .ok (f, _) =>
    match headersBlock f with
    | none => none
    | some block =>
      match decodeBlock t block with
      | some (fs, t') => if validRequest fs then some (fs, t') else none
      | none => none

/-- The HEADERS frame: C.3.1's block (20 octets), END_STREAM | END_HEADERS, stream 1. -/
def frame : List UInt8 :=
  encodeFrame ⟨⟨c31.length, FrameType.headers.code, flagEndStream + flagEndHeaders, 1⟩, c31⟩

example : (readRequest (.empty 4096) frame).map (·.1) =
    some [Entry.ofStrings ":method" "GET", Entry.ofStrings ":scheme" "http",
      Entry.ofStrings ":path" "/", Entry.ofStrings ":authority" "www.example.com"] := by
  decide +kernel

/-- The same block on stream 0 is refused (§6.2). -/
example : readRequest (.empty 4096)
    (encodeFrame ⟨⟨c31.length, FrameType.headers.code, flagEndStream + flagEndHeaders, 0⟩, c31⟩) =
    none := by decide +kernel

end Silmaril.Net.Http2.Examples
