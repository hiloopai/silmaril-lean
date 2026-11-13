module

public import Silmaril.Parse.ByteParse.Defs

/-!
# HTTP/1.1 lexical syntax: byte classes

The terminal classes of the HTTP/1.1 grammar (RFC 9112 §1.2, which takes them from RFC 9110
§5.5–§5.6 and the ABNF core rules of RFC 5234 Appendix B.1), as decidable predicates on
octets. HTTP messages are octet sequences (RFC 9112 §2.2), so everything here is about
`UInt8`; no character decoding is involved.

| Predicate | ABNF | Source |
| --- | --- | --- |
| `isDigit` | `DIGIT = %x30-39` | RFC 5234 B.1 |
| `isAlpha` | `ALPHA = %x41-5A / %x61-7A` | RFC 5234 B.1 |
| `isHexDig` | `HEXDIG = DIGIT / "A" / … / "F"` (case-insensitive) | RFC 5234 B.1, §2.3 |
| `isVchar` | `VCHAR = %x21-7E` | RFC 5234 B.1 |
| `isWS` | `SP / HTAB` (the alternatives of `OWS`) | RFC 9110 §5.6.3 |
| `isTchar` | `tchar` | RFC 9110 §5.6.2 |
| `isObsText` | `obs-text = %x80-FF` | RFC 9110 §5.5 |
| `isFieldVchar` | `field-vchar = VCHAR / obs-text` | RFC 9110 §5.5 |
| `isFieldByte` | `SP / HTAB / field-vchar` (the bytes of `field-content`, and of `reason-phrase`, RFC 9112 §4) | RFC 9110 §5.5 |

These classes are also defined by the HTTP semantics track (`Silmaril.Net.Http`, RFC 9110),
which proves its validity checks equal to the grammars; once both are on `main` the two sets
of predicates should be identified (they are the same Boolean functions).

`trimOWS` removes the optional whitespace around a field value (RFC 9112 §5:
`field-line = field-name ":" OWS field-value OWS`).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

/-! ## Distinguished octets -/

/-- `SP`, `%x20`. -/
abbrev SP : UInt8 := 0x20
/-- `HTAB`, `%x09`. -/
abbrev HTAB : UInt8 := 0x09
/-- `CR`, `%x0D`. -/
abbrev CR : UInt8 := 0x0D
/-- `LF`, `%x0A`. -/
abbrev LF : UInt8 := 0x0A
/-- `":"`, `%x3A`. -/
abbrev COLON : UInt8 := 0x3A
/-- `CRLF`. -/
abbrev CRLF : Bytes := [CR, LF]

/-! ## Classes -/

/-- `DIGIT` (RFC 5234 B.1). -/
def isDigit (c : UInt8) : Bool := 0x30 ≤ c && c ≤ 0x39

/-- `ALPHA` (RFC 5234 B.1). -/
def isAlpha (c : UInt8) : Bool := (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A)

/-- `HEXDIG` (RFC 5234 B.1); ABNF strings are case-insensitive (RFC 5234 §2.3), so `a-f`
are hex digits as well. -/
def isHexDig (c : UInt8) : Bool :=
  isDigit c || (0x41 ≤ c && c ≤ 0x46) || (0x61 ≤ c && c ≤ 0x66)

/-- `VCHAR` (RFC 5234 B.1): visible US-ASCII. -/
def isVchar (c : UInt8) : Bool := 0x21 ≤ c && c ≤ 0x7E

/-- `SP / HTAB`: the whitespace of `OWS`, `RWS` and `BWS` (RFC 9110 §5.6.3). -/
def isWS (c : UInt8) : Bool := c == SP || c == HTAB

/-- `tchar` (RFC 9110 §5.6.2):
`"!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "." / "^" / "_" / "`" / "|" / "~" /
DIGIT / ALPHA`. -/
def isTchar (c : UInt8) : Bool :=
  isDigit c || isAlpha c || c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 ||
    c == 0x27 || c == 0x2A || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F ||
    c == 0x60 || c == 0x7C || c == 0x7E

/-- `obs-text = %x80-FF` (RFC 9110 §5.5). -/
def isObsText (c : UInt8) : Bool := 0x80 ≤ c

/-- `field-vchar = VCHAR / obs-text` (RFC 9110 §5.5). -/
def isFieldVchar (c : UInt8) : Bool := isVchar c || isObsText c

/-- `SP / HTAB / field-vchar`: the octets that may occur in a field value (RFC 9110 §5.5) and
in a reason phrase (`reason-phrase = 1*( HTAB / SP / VCHAR / obs-text )`, RFC 9112 §4). -/
def isFieldByte (c : UInt8) : Bool := isWS c || isFieldVchar c

/-- `token = 1*tchar` (RFC 9110 §5.6.2). -/
def IsToken (l : Bytes) : Prop := l ≠ [] ∧ ∀ b ∈ l, isTchar b = true

instance (l : Bytes) : Decidable (IsToken l) := inferInstanceAs (Decidable (_ ∧ _))

/-- `field-value = *field-content`, `field-content = field-vchar [ 1*( SP / HTAB /
field-vchar ) field-vchar ]` (RFC 9110 §5.5): field bytes, neither starting nor ending with
whitespace. (`*field-content` concatenates such pieces; a concatenation of them is again a
run of field bytes with non-whitespace ends, and conversely a nonempty such run is one
`field-content`. That equivalence is proved by the semantics track.) -/
def IsFieldValue (l : Bytes) : Prop :=
  (∀ b ∈ l, isFieldByte b = true) ∧ (∀ b ∈ l.head?, isWS b = false) ∧
    (∀ b ∈ l.getLast?, isWS b = false)

instance (l : Bytes) : Decidable (IsFieldValue l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Strip leading and trailing `OWS`. -/
def trimOWS (l : Bytes) : Bytes := ((l.dropWhile isWS).reverse.dropWhile isWS).reverse

/-! ## Digits -/

/-- The value of a `DIGIT` octet. -/
def digitVal (c : UInt8) : Nat := c.toNat - 0x30

/-- The `DIGIT` octet of `d < 10`. -/
def digitByte (d : Nat) : UInt8 := UInt8.ofNat (0x30 + d)

/-- The value of a `HEXDIG` octet. -/
def hexVal (c : UInt8) : Nat :=
  if isDigit c then c.toNat - 0x30
  else if c ≤ 0x46 then c.toNat - 0x41 + 10
  else c.toNat - 0x61 + 10

/-- The value of a string of `HEXDIG`s (most significant first). -/
def hexValue (l : Bytes) : Nat := l.foldl (fun n c => 16 * n + hexVal c) 0

/-- The lowercase `HEXDIG` octet of `d < 16`. -/
def hexByte (d : Nat) : UInt8 := if d < 10 then UInt8.ofNat (0x30 + d) else UInt8.ofNat (0x61 + d - 10)

/-- The hexadecimal digits of `n`, most significant first (`[0x30]` for zero). -/
def hexDigits (n : Nat) : Bytes :=
  if n < 16 then [hexByte n] else hexDigits (n / 16) ++ [hexByte (n % 16)]
termination_by n
decreasing_by omega

/-- The value of a string of `DIGIT`s. -/
def decValue (l : Bytes) : Nat := l.foldl (fun n c => 10 * n + digitVal c) 0

/-- The decimal digits of `n`, most significant first. -/
def decDigits (n : Nat) : Bytes :=
  if n < 10 then [digitByte n] else decDigits (n / 10) ++ [digitByte (n % 10)]
termination_by n
decreasing_by omega

/-! ## Case -/

/-- ASCII lowercase of one octet (field names are case-insensitive, RFC 9110 §5.1). -/
def lowerByte (c : UInt8) : UInt8 := if 0x41 ≤ c && c ≤ 0x5A then c + 0x20 else c

/-- ASCII lowercase. -/
def lower (l : Bytes) : Bytes := l.map lowerByte

/-- The octets of an ASCII string literal. -/
def ascii (s : String) : Bytes := s.toUTF8.data.toList

end Silmaril.Net.Http1
