module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Defs

@[expose] public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Projection

open Silmaril.Crypto.Blake3 (Bytes)

/-- Data fields in wire order occupy one contiguous interval starting at `base`.
The interval need not start at zero or reach the end of the object. -/
inductive Contiguous {size : Nat} {digest : Bytes} : Nat → List (SpanFact size digest) → Bytes → Prop where
  | nil (base : Nat) : Contiguous base [] []
  | cons {base : Nat} {fact : SpanFact size digest} {tail : List (SpanFact size digest)} {rest : Bytes}
      (offset : fact.offset = base) (next : Contiguous (base + fact.bytes.length) tail rest) :
      Contiguous base (fact :: tail) (fact.bytes ++ rest)

/-- The next requested byte after consuming data up to this absolute position. -/
def cursorAt (request : Bao.RangeRequest) (position : Nat) : Nat :=
  min (request.start + request.count) (max request.start position)

/-- The bytes of the intersection of the request and an available contiguous span. -/
def clip (request : Bao.RangeRequest) (base : Nat) (bytes : Bytes) : Bytes :=
  (bytes.drop (request.start - base)).take
    (min (request.start + request.count) (base + bytes.length) - max request.start base)

end Silmaril.Formats.Blake3Cas.RangeFacts.Projection
