module

public import Silmaril.Formats.ASN1.Codec.Defs

/-!
# ASN.1: universal types under DER

Contents codecs (`Codec (List UInt8) α`, namespace `Content`) for the universal
types used by the X.509 profile, with the DER restrictions of X.690 §10–§11, and
the corresponding value codecs in the primitive form (§10.2):

* BOOLEAN: `0xFF` for TRUE and `0x00` for FALSE (§8.2, §11.1);
* INTEGER: two's complement in the minimum number of octets (§8.3.2), to and
  from `Int`; `natural` is INTEGER (0..MAX) as `Nat`;
* BIT STRING: an initial octet with the number of unused bits in `0..7`, zero
  when there are no bits, and the unused bits zero (§8.6.2, §11.2.1);
* OCTET STRING (§8.7) and NULL (§8.8);
* OBJECT IDENTIFIER: minimal base-128 subidentifiers, the first combining the
  first two arcs as `40 * X + Y` (§8.19), to and from the arc list;
* UTF8String (valid UTF-8, to and from `String`), PrintableString and IA5String
  (character set checked, kept as octets; X.680 §41).

`SEQUENCE`, `SEQUENCE OF` and `SET OF` (DER-sorted) are the universal
constructed forms of `Codec.cons`. Lawfulness is proved in
`Silmaril.Formats.ASN1.Universal.Thms`.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

namespace Content

/-! ## BOOLEAN, NULL, OCTET STRING -/

/-- BOOLEAN contents (X.690 §8.2, DER §11.1). -/
def boolean : Codec (List UInt8) Bool where
  WF _ := True
  enc b := [if b then 0xFF else 0x00]
  dec bs := match bs with
    | [b] => if b = 0xFF then some true else if b = 0x00 then some false else none
    | _ => none

/-- NULL contents (§8.8): empty. -/
def null : Codec (List UInt8) Unit where
  WF _ := True
  enc _ := []
  dec bs := match bs with
    | [] => some ()
    | _ :: _ => none

/-- OCTET STRING contents (§8.7), primitive form. -/
def octets : Codec (List UInt8) (List UInt8) where
  WF _ := True
  enc bs := bs
  dec bs := some bs

/-! ## INTEGER -/

/-- The minimal two's-complement octets of a natural number: its minimal
big-endian octets, with a `0x00` sign octet when the top bit would be set. -/
def natContent (n : Nat) : List UInt8 :=
  match beBytes n with
  | [] => [0]
  | b :: bs => if b.toNat < 128 then b :: bs else 0 :: b :: bs

/-- Octet complement. -/
def compl (b : UInt8) : UInt8 := 255 - b

/-- The leading octet `b` is a redundant sign octet `0x00` (§8.3.2). -/
def redundantZero (b : UInt8) (bs : List UInt8) : Bool :=
  b == 0 && match bs with
    | c :: _ => decide (c.toNat < 128)
    | [] => false

/-- Read minimal non-negative two's-complement octets. -/
def natOfContent? (bs : List UInt8) : Option Nat :=
  match bs with
  | [] => none
  | b :: r => if b.toNat < 128 ∧ redundantZero b r = false then some (beNat (b :: r)) else none

/-- The minimal two's-complement octets of an integer. A negative `z` is spelled
as the complement of the non-negative `-z - 1`. -/
def intContent (z : Int) : List UInt8 :=
  if 0 ≤ z then natContent z.toNat else (natContent (-z - 1).toNat).map compl

/-- Read minimal two's-complement octets: empty contents and a redundant
leading `0x00` or `0xFF` octet are rejected. -/
def intOfContent? (bs : List UInt8) : Option Int :=
  match bs with
  | [] => none
  | b :: _ =>
      if b.toNat < 128 then (natOfContent? bs).map Int.ofNat
      else (natOfContent? (bs.map compl)).map (fun (n : Nat) => -(n : Int) - 1)

/-- INTEGER contents (§8.3), minimal. -/
def integer : Codec (List UInt8) Int where
  WF _ := True
  enc := intContent
  dec := intOfContent?

end Content

/-! ## BIT STRING -/

/-- A BIT STRING value: the contents octets after the initial octet, and the
number of unused bits in the last one. -/
structure BitString where
  unused : Nat
  bytes : List UInt8
  deriving DecidableEq, Repr

namespace BitString

/-- The DER constraints of X.690 §8.6.2 and §11.2.1: at most 7 unused bits,
none when there are no octets, and the unused bits are zero. -/
def ok (b : BitString) : Bool :=
  decide (b.unused < 8) &&
    match b.bytes.getLast? with
    | none => b.unused == 0
    | some l => l.toNat % 2 ^ b.unused == 0

/-- The number of bits. -/
def length (b : BitString) : Nat := 8 * b.bytes.length - b.unused

/-- Bit `i`, numbered from the most significant bit of the first octet (bit 0
in the named-bit notation of X.680 §22). -/
def bit (b : BitString) (i : Nat) : Bool :=
  i < b.length && match b.bytes[i / 8]? with
    | some x => x.toNat / 2 ^ (7 - i % 8) % 2 == 1
    | none => false

end BitString

namespace Content

/-- BIT STRING contents, primitive form. -/
def bitString : Codec (List UInt8) BitString where
  WF b := b.ok = true
  enc b := b.unused.toUInt8 :: b.bytes
  dec bs := match bs with
    | [] => none
    | u :: r => if (BitString.mk u.toNat r).ok then some ⟨u.toNat, r⟩ else none

/-! ## OBJECT IDENTIFIER -/

/-- An arc list has an encoding (X.690 §8.19.4): at least two arcs,
the first in `0..2`, and the second below 40 unless the first is 2. -/
def oidWF (arcs : List Nat) : Prop :=
  match arcs with
  | a :: b :: _ => a ≤ 2 ∧ (a < 2 → b < 40)
  | _ => False

instance (arcs : List Nat) : Decidable (oidWF arcs) := by
  unfold oidWF; split <;> infer_instance

/-- OBJECT IDENTIFIER contents (§8.19): the subidentifiers `40 * X + Y`, then
the remaining arcs, each in base 128. -/
def oidContent (arcs : List Nat) : List UInt8 :=
  match arcs with
  | a :: b :: rest => ((40 * a + b) :: rest).flatMap base128
  | _ => []

/-- Read a sequence of subidentifiers (`fuel` bounds the recursion; the input
length suffices). -/
def readArcs : Nat → List UInt8 → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, s@(_ :: _) =>
      match readBase128 s with
      | some (n, r) => (readArcs fuel r).map (n :: ·)
      | none => none

/-- Split the first subidentifier into the first two arcs (§8.19.4). -/
def splitFirst (x : Nat) (rest : List Nat) : List Nat :=
  if x < 40 then 0 :: x :: rest else if x < 80 then 1 :: (x - 40) :: rest else 2 :: (x - 80) :: rest

/-- Read OBJECT IDENTIFIER contents; empty contents are rejected. -/
def oidOfContent? (bs : List UInt8) : Option (List Nat) :=
  match readArcs bs.length bs with
  | some (x :: rest) => some (splitFirst x rest)
  | _ => none

/-- OBJECT IDENTIFIER contents. -/
def oid : Codec (List UInt8) (List Nat) where
  WF := oidWF
  enc := oidContent
  dec := oidOfContent?

/-! ## Character strings -/

/-- IA5String contents: ASCII, kept as octets. -/
def ia5 : Codec (List UInt8) (List UInt8) := octets.refine (fun bs => ∀ b ∈ bs, b.toNat < 128)

/-- The PrintableString character set (X.680 §41.4, Table 10): letters,
digits, space and `'()+,-./:=?`. -/
def printableChar (b : UInt8) : Bool :=
  let n := b.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) ||
    [32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63].contains n

/-- PrintableString contents, kept as octets. -/
def printable : Codec (List UInt8) (List UInt8) :=
  octets.refine (fun bs => ∀ b ∈ bs, printableChar b = true)

/-- UTF8String contents: valid UTF-8. -/
def utf8 : Codec (List UInt8) String where
  WF _ := True
  enc s := s.toByteArray.data.toList
  dec bs := String.fromUTF8? bs.toByteArray

end Content

/-! ## Value codecs -/

/-- BOOLEAN. -/
def boolean : Codec Value Bool := Codec.prim Tag.boolean Content.boolean
/-- INTEGER. -/
def integer : Codec Value Int := Codec.prim Tag.integer Content.integer
/-- BIT STRING, primitive form. -/
def bitString : Codec Value BitString := Codec.prim Tag.bitString Content.bitString
/-- OCTET STRING, primitive form. -/
def octetString : Codec Value (List UInt8) := Codec.prim Tag.octetString Content.octets
/-- NULL. -/
def null : Codec Value Unit := Codec.prim Tag.null Content.null
/-- OBJECT IDENTIFIER. -/
def oid : Codec Value (List Nat) := Codec.prim Tag.oid Content.oid
/-- UTF8String, primitive form. -/
def utf8String : Codec Value String := Codec.prim Tag.utf8String Content.utf8
/-- PrintableString, primitive form. -/
def printableString : Codec Value (List UInt8) := Codec.prim Tag.printableString Content.printable
/-- IA5String, primitive form. -/
def ia5String : Codec Value (List UInt8) := Codec.prim Tag.ia5String Content.ia5

/-- INTEGER (0..MAX) as a natural number. -/
def natural : Codec Value Nat := (integer.refine (0 ≤ ·)).iso Int.toNat Int.ofNat

/-- `SEQUENCE { … }` with the given components. -/
def sequence {α : Type} (c : Codec (List Value) α) : Codec Value α := Codec.cons Tag.sequence c

/-- `SEQUENCE OF T`. -/
def sequenceOf {α : Type} (c : Codec Value α) : Codec Value (List α) :=
  Codec.cons Tag.sequence (Codec.seqOf c)

/-- `SET OF T`, in DER order. -/
def setOf {α : Type} (c : Codec Value α) : Codec Value (List α) := Codec.cons Tag.set (Codec.setOf c)

end Silmaril.Formats.ASN1
