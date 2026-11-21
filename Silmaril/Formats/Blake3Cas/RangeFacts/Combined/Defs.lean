module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Defs

@[expose] public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Combined

open Silmaril.Crypto.Blake3

/-- The fully disclosed schedule, with one field per original 1 KiB chunk. -/
def chunkPlan : Shape → Bao.Plan
  | .leaf first width => .leaf ⟨first, 1⟩ width
  | .fork left right => .fork (shapeSpan (.fork left right)) (chunkPlan left) (chunkPlan right)

def part (original : Bytes) (start width : Nat) : Bytes := (original.drop start).take width

/-- Source data for the official combined slot encoder. Parent fields contain the
two non-root CVs, in order, at their absolute chunk counters. -/
def source (original : Bytes) : Bao.Slot → Option Bytes
  | .data span width => some (part original span.byteStart width)
  | .pair span => do
    let left := span.split.1
    let right := span.split.2
    let leftWidth := left.byteSize original.length
    let rightWidth := right.byteSize original.length
    let lcv ← subtreeCV? false (geometry left.first leftWidth) (part original left.byteStart leftWidth)
    let rcv ← subtreeCV? false (geometry right.first rightWidth) (part original right.byteStart rightWidth)
    return digestBytes lcv ++ digestBytes rcv

/-- Encode full data in official Bao combined layout. This reference source
recomputes each requested child CV rather than caching it. -/
def encode? (original : Bytes) : Option Bytes := Bao.encode .combined original.length (source original)

end Silmaril.Formats.Blake3Cas.RangeFacts.Combined
