module

public import Init

/-!
# ASN.1: big-endian digit strings

X.690 spells natural numbers big-endian in two radices, both minimal (no
leading zero digit):

* base 256, for the long form of the length octets (§8.1.3.5) and for INTEGER
  contents (§8.3.2): `beBytes` and its inverse `beNat`;
* base 128 with a continuation bit in bit 8 of every octet but the last, for
  high tag numbers (§8.1.2.4.2) and OBJECT IDENTIFIER subidentifiers
  (§8.19.2): `base128`, the reader `readBase128`, and `Base128Octets`, a
  transcription of the clause.

The generic `digitsBE b n` is the minimal radix-`b` spelling of `n` (empty for
zero) and `ofDigitsBE b l` the value of a digit list. Their laws are in
`Silmaril.Formats.ASN1.Digits.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

/-! ## Generic digits -/

/-- The value of a big-endian digit list in radix `b`. -/
def ofDigitsBE (b : Nat) (l : List Nat) : Nat := l.foldl (fun a d => a * b + d) 0

/-- The minimal big-endian digits of `n` in radix `b` (empty for `n = 0`, and
for the degenerate radices `b ≤ 1`). -/
def digitsBE (b : Nat) (n : Nat) : List Nat :=
  if _h : n = 0 ∨ b ≤ 1 then [] else digitsBE b (n / b) ++ [n % b]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ## Base 256 -/

/-- The value of a big-endian octet string. -/
def beNat (l : List UInt8) : Nat := l.foldl (fun a d => a * 256 + d.toNat) 0

/-- The minimal big-endian octets of `n` (empty for zero). -/
def beBytes (n : Nat) : List UInt8 := (digitsBE 256 n).map Nat.toUInt8

/-! ## Base 128 with continuation bits -/

/-- The base-128 octets of `n`: big-endian 7-bit groups with bit 8 set on every
octet except the last, and no leading `0x80` octet. Zero is the single octet
`0x00`. -/
def base128 (n : Nat) : List UInt8 :=
  (digitsBE 128 (n / 128)).map (fun d => (d + 128).toUInt8) ++ [(n % 128).toUInt8]

/-- X.690 §8.1.2.4.2 and §8.19.2, transcribed: `ds` spells `n` in base 128
with bit 8 set on every octet but the last, and the leading octet is not
`0x80`. -/
def Base128Octets (n : Nat) (ds : List UInt8) : Prop :=
  ∃ hi lo, ds = hi ++ [lo] ∧ (∀ d ∈ hi, 128 ≤ d.toNat) ∧ lo.toNat < 128 ∧
    hi.head? ≠ some 0x80 ∧ n = ofDigitsBE 128 (hi.map (fun d => d.toNat - 128) ++ [lo.toNat])

/-- Read one base-128 number, accumulating into `acc`, up to and including the
first octet without bit 8. -/
def readBase128Aux (acc : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: r =>
      if b.toNat < 128 then some (acc * 128 + b.toNat, r)
      else readBase128Aux (acc * 128 + (b.toNat - 128)) r

/-- Read one minimal base-128 number from the front of the input, returning the
rest. A leading `0x80` octet (a redundant zero group) is rejected. -/
def readBase128 : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: r => if b = 0x80 then none else readBase128Aux 0 (b :: r)

end Silmaril.Formats.ASN1
