module

public import Silmaril.Formats.Csv.Typed.Defs

/-! Canonical uppercase hexadecimal for opaque cells. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Codecs.Hex

def digit (n : Nat) : UInt8 :=
  UInt8.ofNat (if n < 10 then 48 + n else 55 + n)

def digitValue (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55)
  else none

/-- Two uppercase digits per octet, high nibble first. -/
def encode (bytes : List UInt8) : Field :=
  bytes.flatMap fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)]

def decodeRev : Field → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | high :: low :: rest, acc => do
    let hi ← digitValue high
    let lo ← digitValue low
    decodeRev rest (UInt8.ofNat (16 * hi + lo) :: acc)
  | [_], _ => none

/-- Reject odd lengths and any byte outside the canonical alphabet. -/
def decode (text : Field) : Option (List UInt8) :=
  decodeRev text []

def codec : CellCodec (List UInt8) := ⟨some ∘ encode, decode⟩

end Silmaril.Formats.Csv.Typed.Codecs.Hex
