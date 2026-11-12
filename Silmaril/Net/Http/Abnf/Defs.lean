module

public import Silmaril.Formats.Grammar.Thms

@[expose] public section

/-!
# ABNF core rules over octets (RFC 5234)

HTTP is defined over octets with grammars written in ABNF (RFC 5234, used by RFC 9110 §1.2 and
RFC 3986 §1.3). This module writes the pieces of ABNF that HTTP needs as expressions of the
Silmaril EBNF grammar framework (`Silmaril.Formats.Grammar.Ebnf`), whose semantics is the inductive
derivation relation `Derives` (finite derivations, no parser in the definition):

* a terminal value `%xNN` is `.terminal 0xNN`;
* a value range `%xLO-HI` (RFC 5234 §3.4) is `range LO HI`, the alternatives of the octets in it;
* alternation `/` (§3.2) is `.alternative`, concatenation (§3.1) `.sequence`, `*rule` (§3.6)
  `.repetition`, `1*rule` `Expr.oneOrMore`, `[rule]` (§3.8) `Expr.optional`;
* the core rules of Appendix B.1 used by HTTP: `ALPHA`, `DIGIT`, `HEXDIG`, `VCHAR`, `SP`, `HTAB`,
  and `obs-text` (RFC 9110 §5.6.4: `%x80-FF`).

Quoted strings in ABNF are case-insensitive (RFC 5234 §2.3), so `HEXDIG` (`DIGIT / "A" / … /
"F"`) also matches `a`–`f`.

Each rule `R` comes with a decidable check `isR : UInt8 → Bool` (for single-octet rules) and
the theorems of `Abnf/Thms.lean` equate the grammar with the check.

The grammars are generic in the nonterminal type `N` (they use no references), so they can be
embedded in a larger grammar system.
-/

namespace Silmaril.Net.Http.Abnf

open Silmaril.Formats.Grammar.Ebnf

/-- An octet (RFC 9110 §2.1: HTTP messages are sequences of octets). -/
abbrev Octet := UInt8

/-- Every octet, in order. -/
def allOctets : List UInt8 := (List.range 256).map Nat.toUInt8

/-- The alternatives of a list of terminals. -/
def anyOf {N : Type} : List UInt8 → Expr UInt8 N
  | [] => .empty
  | b :: bs => .alternative (.terminal b) (anyOf bs)

/-- A character class: the alternatives of the octets satisfying `p`. -/
def cls {N : Type} (p : UInt8 → Bool) : Expr UInt8 N := anyOf (allOctets.filter p)

/-- The value range `%xLO-HI` (RFC 5234 §3.4). -/
def inRange (lo hi : UInt8) (b : UInt8) : Bool := decide (lo ≤ b ∧ b ≤ hi)

/-- The value range `%xLO-HI` as a grammar (RFC 5234 §3.4). -/
def range {N : Type} (lo hi : UInt8) : Expr UInt8 N := cls (inRange lo hi)

/-! ## Core rules (RFC 5234 Appendix B.1, RFC 9110 §5.6.4) -/

/-- `ALPHA = %x41-5A / %x61-7A` (A-Z / a-z). -/
def isAlpha (b : UInt8) : Bool := inRange 0x41 0x5A b || inRange 0x61 0x7A b
/-- `ALPHA` as a grammar. -/
def alpha {N : Type} : Expr UInt8 N := .alternative (range 0x41 0x5A) (range 0x61 0x7A)

/-- `DIGIT = %x30-39` (0-9). -/
def isDigit (b : UInt8) : Bool := inRange 0x30 0x39 b
/-- `DIGIT` as a grammar. -/
def digit {N : Type} : Expr UInt8 N := range 0x30 0x39

/-- `HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"`, case-insensitive (RFC 5234 §2.3). -/
def isHexDig (b : UInt8) : Bool := isDigit b || inRange 0x41 0x46 b || inRange 0x61 0x66 b
/-- `HEXDIG` as a grammar. -/
def hexdig {N : Type} : Expr UInt8 N :=
  .alternative digit (.alternative (range 0x41 0x46) (range 0x61 0x66))

/-- `VCHAR = %x21-7E` (visible, printing characters). -/
def isVchar (b : UInt8) : Bool := inRange 0x21 0x7E b
/-- `VCHAR` as a grammar. -/
def vchar {N : Type} : Expr UInt8 N := range 0x21 0x7E

/-- `SP = %x20`. -/
def sp {N : Type} : Expr UInt8 N := .terminal 0x20
/-- `HTAB = %x09`. -/
def htab {N : Type} : Expr UInt8 N := .terminal 0x09
/-- `SP / HTAB`. -/
def isWsp (b : UInt8) : Bool := b == 0x20 || b == 0x09

/-- `obs-text = %x80-FF` (RFC 9110 §5.6.4). -/
def isObsText (b : UInt8) : Bool := inRange 0x80 0xFF b
/-- `obs-text` as a grammar. -/
def obsText {N : Type} : Expr UInt8 N := range 0x80 0xFF

/-- `OWS = *( SP / HTAB )` (RFC 9110 §5.6.3, optional whitespace). -/
def ows {N : Type} : Expr UInt8 N := .repetition (.alternative sp htab)

/-! ## ASCII case (RFC 9110 §5.1: field names are case-insensitive) -/

/-- ASCII lower case of an octet: `A`-`Z` to `a`-`z`, every other octet unchanged. -/
def lowerOctet (b : UInt8) : UInt8 := if inRange 0x41 0x5A b then b + 0x20 else b

/-- ASCII lower case of an octet string. -/
def lower (xs : List UInt8) : List UInt8 := xs.map lowerOctet

/-- ASCII case-insensitive equality of octet strings. -/
def eqIgnoreCase (xs ys : List UInt8) : Bool := lower xs == lower ys

/-! ## Characters and octets

WASI passes field names as `string` (Unicode scalar values) and field values as `list<u8>`. A
string denotes an octet string when all its characters are ASCII. -/

/-- The octets of an ASCII string (`none` when a character is not ASCII). -/
def asciiOctets? (s : List Char) : Option (List UInt8) :=
  if s.all (fun c => c.toNat < 128) then some (s.map (fun c => c.toNat.toUInt8)) else none

/-- The ASCII string of an octet string (octets as Latin-1 code points). -/
def octetChars (xs : List UInt8) : List Char := xs.map (fun b => Char.ofNat b.toNat)

end Silmaril.Net.Http.Abnf
