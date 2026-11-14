module

public import Silmaril.Formats.ASN1.Universal.Defs

/-!
# ASN.1: UTCTime and GeneralizedTime under DER and RFC 5280

DER fixes one spelling of each time (X.690 §11.7, §11.8): UTC with the `Z`
designator, seconds present, and for GeneralizedTime no trailing zeros in
fractional seconds. RFC 5280 §4.1.2.5.1–2 further forbids fractional seconds,
so the contents codecs here accept exactly

* UTCTime `YYMMDDHHMMSSZ` (13 octets), for years 1950–2049 (`YY < 50` means
  `20YY`, otherwise `19YY`);
* GeneralizedTime `YYYYMMDDHHMMSSZ` (15 octets), for years 0–9999,

for valid Gregorian dates and times of day (no leap second).

`time` is the RFC 5280 `Time` CHOICE. RFC 5280 §4.1.2.5 also requires
certificate validity dates in 1950–2049 to be UTCTime and all others to be
GeneralizedTime; `rfc5280Time` adds that rule.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

/-- A calendar date and time of day, UTC. -/
structure DateTime where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  deriving DecidableEq, Repr

namespace DateTime

/-- Gregorian leap years. -/
def leap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- The number of days in month `m` (1-based) of year `y`. -/
def daysInMonth (y m : Nat) : Nat :=
  if m = 2 then (if leap y then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30 else 31

/-- A valid date and time of day. -/
def valid (t : DateTime) : Bool :=
  decide (1 ≤ t.month ∧ t.month ≤ 12 ∧ 1 ≤ t.day ∧ t.day ≤ daysInMonth t.year t.month ∧
    t.hour < 24 ∧ t.minute < 60 ∧ t.second < 60)

end DateTime

namespace Content

/-- The ASCII digit `n` (for `n < 10`). -/
def digit (n : Nat) : UInt8 := (48 + n).toUInt8

/-- The value of an ASCII digit. -/
def readDigit (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48) else none

/-- The value of two ASCII digits. -/
def read2 (a b : UInt8) : Option Nat :=
  match readDigit a, readDigit b with
  | some x, some y => some (10 * x + y)
  | _, _ => none

/-- A two-digit field (for `n < 100`). -/
def digits2 (n : Nat) : List UInt8 := [digit (n / 10), digit (n % 10)]

/-- The common `MMDDHHMMSSZ` tail. -/
def timeTail (t : DateTime) : List UInt8 :=
  digits2 t.month ++ digits2 t.day ++ digits2 t.hour ++ digits2 t.minute ++ digits2 t.second ++
    [0x5A]

/-- UTCTime can spell `t`: valid, in the years 1950–2049. -/
def utcOK (t : DateTime) : Bool := t.valid && decide (1950 ≤ t.year ∧ t.year < 2050)

/-- GeneralizedTime can spell `t`: valid, with a four-digit year. -/
def generalizedOK (t : DateTime) : Bool := t.valid && decide (t.year < 10000)

/-- UTCTime contents `YYMMDDHHMMSSZ`. -/
def utcContent (t : DateTime) : List UInt8 := digits2 (t.year % 100) ++ timeTail t

/-- GeneralizedTime contents `YYYYMMDDHHMMSSZ`. -/
def generalizedContent (t : DateTime) : List UInt8 :=
  digits2 (t.year / 100) ++ digits2 (t.year % 100) ++ timeTail t

/-- Read the `MMDDHHMMSSZ` tail, given the year. -/
def readTail (year : Nat) : List UInt8 → Option DateTime
  | [m₁, m₂, d₁, d₂, h₁, h₂, i₁, i₂, s₁, s₂, z] =>
      match read2 m₁ m₂, read2 d₁ d₂, read2 h₁ h₂, read2 i₁ i₂, read2 s₁ s₂ with
      | some mo, some dd, some hh, some mi, some ss =>
          if z = 0x5A then some ⟨year, mo, dd, hh, mi, ss⟩ else none
      | _, _, _, _, _ => none
  | _ => none

/-- Read UTCTime contents. -/
def utcOfContent? (bs : List UInt8) : Option DateTime :=
  match bs with
  | y₁ :: y₂ :: tail =>
      match read2 y₁ y₂ with
      | some yy =>
          match readTail (if yy < 50 then 2000 + yy else 1900 + yy) tail with
          | some t => if utcOK t then some t else none
          | none => none
      | none => none
  | _ => none

/-- Read GeneralizedTime contents. -/
def generalizedOfContent? (bs : List UInt8) : Option DateTime :=
  match bs with
  | c₁ :: c₂ :: y₁ :: y₂ :: tail =>
      match read2 c₁ c₂, read2 y₁ y₂ with
      | some cc, some yy =>
          match readTail (100 * cc + yy) tail with
          | some t => if generalizedOK t then some t else none
          | none => none
      | _, _ => none
  | _ => none

/-- UTCTime contents. -/
def utcTime : Codec (List UInt8) DateTime where
  WF t := utcOK t = true
  enc := utcContent
  dec := utcOfContent?

/-- GeneralizedTime contents, without fractional seconds. -/
def generalizedTime : Codec (List UInt8) DateTime where
  WF t := generalizedOK t = true
  enc := generalizedContent
  dec := generalizedOfContent?

end Content

/-- `Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }`
(RFC 5280 §4.1). -/
inductive Time where
  | utc (t : DateTime)
  | generalized (t : DateTime)
  deriving DecidableEq, Repr

namespace Time

/-- The instant denoted. -/
def dateTime : Time → DateTime
  | .utc t => t
  | .generalized t => t

/-- RFC 5280 §4.1.2.5: dates in 1950–2049 are UTCTime, all others
GeneralizedTime. (The UTCTime codec already rejects other years.) -/
def rfc5280Choice : Time → Bool
  | .utc _ => true
  | .generalized t => !decide (1950 ≤ t.year ∧ t.year < 2050)

/-- The sum view of the CHOICE. -/
def toSum : Time → DateTime ⊕ DateTime
  | .utc t => .inl t
  | .generalized t => .inr t

/-- The `Time` alternative of the sum view. -/
def ofSum : DateTime ⊕ DateTime → Time
  | .inl t => .utc t
  | .inr t => .generalized t

end Time

/-- UTCTime. -/
def utcTime : Codec Value DateTime := Codec.prim Tag.utcTime Content.utcTime

/-- GeneralizedTime, without fractional seconds. -/
def generalizedTime : Codec Value DateTime :=
  Codec.prim Tag.generalizedTime Content.generalizedTime

/-- `Time`, as a `CHOICE`. -/
def time : Codec Value Time := (Codec.orElse utcTime generalizedTime).iso Time.ofSum Time.toSum

/-- `Time` with the RFC 5280 choice of alternative by year. -/
def rfc5280Time : Codec Value Time := time.refine (·.rfc5280Choice = true)

end Silmaril.Formats.ASN1
