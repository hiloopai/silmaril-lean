module

public import Silmaril.Crypto.Blake3.Range.EOF.Defs
public import Silmaril.Semantics.Naming.ByteRange.Extension.Defs

@[expose] public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming.ByteRange (Fact Observations)

/-- Forget the range checker's extent claim, but retain a checked EOF or whole
as an explicit length fact. This translation does not itself imply compatibility. -/
def Certified (rel : Compression) (digest : Bytes) : Fact → Prop
  | .range offset fragment => ∃ claim, Checked rel claim digest offset fragment
  | .whole bytes => Named rel digest bytes
  | .eof length => CheckedEOF rel length digest

/-- A sufficient common-geometry guard, not an inference from range headers. -/
def CertifiedAt (rel : Compression) (digest : Bytes) (extent : Nat) : Fact → Prop
  | .range offset fragment => Checked rel extent digest offset fragment
  | .whole bytes => bytes.length = extent ∧ Named rel digest bytes
  | .eof length => length = extent ∧ CheckedEOF rel length digest

namespace Compression

def Extends (base rel : Compression) : Prop :=
  ∀ ⦃input output⦄, base input output → rel input output

/-- A conflict in either direction of a partial injective compression table. -/
def CompatibleWith (left right : Compression) : Prop :=
  (∀ ⦃input lhs rhs⦄, left input lhs → right input rhs → lhs = rhs) ∧
    ∀ ⦃lhs rhs output⦄, left lhs output → right rhs output → lhs = rhs

/-- A chosen whole and witness support for each queried digest. Different
witnesses may use different transitions and do not need the same total length.
The agreement tests include each witness with itself. -/
def WitnessFamily (base : Compression) (seen : Observations Bytes)
    (pick : Bytes → Bytes) (support : Bytes → Compression) : Prop :=
  (∀ digest, seen.Queried digest → seen.Fits digest (pick digest) ∧ Named (support digest) digest (pick digest)) ∧
  (∀ digest, seen.Queried digest → base.CompatibleWith (support digest)) ∧
  ∀ left right, seen.Queried left → seen.Queried right → (support left).CompatibleWith (support right)

def witnessUnion (base : Compression) (seen : Observations Bytes)
    (support : Bytes → Compression) : Compression :=
  fun input output => base input output ∨ ∃ digest, seen.Queried digest ∧ support digest input output

/-- Realization inside the compression model, stronger than an abstract naming model. -/
def Realizes (rel : Compression) (seen : Observations Bytes) : Prop :=
  ∀ digest, seen.Queried digest → ∃ bytes, Named rel digest bytes ∧ seen.Fits digest bytes

end Compression
end Silmaril.Crypto.Blake3
