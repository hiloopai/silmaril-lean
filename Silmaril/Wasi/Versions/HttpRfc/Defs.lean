module

public import Silmaril.Wasi.Versions.HttpHdr.Defs

@[expose] public section

/-!
# The RFC 9110 field grammar, as the WASI `fields` checks use it

A **pass-1 stand-in** for the field grammar of the `Net` region's HTTP semantics core
(`Silmaril.Net.Http.*`, being written concurrently): when that lands, these definitions are
replaced by imports of it and the theorems of `HttpRfc.Thms` are restated over it. Names
follow the RFC rule names, so the switch is a renaming.

From RFC 9110 (*HTTP Semantics*, June 2022) and RFC 5234 (*ABNF*, Appendix B.1 core rules):

* §5.6.2 *Tokens*: `token = 1*tchar`,
  `tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "." / "^" / "_" / "`" / "|"
  / "~" / DIGIT / ALPHA` (`Tchar`, `Token`);
* §5.1 *Field Names*: `field-name = token`; "Field names are case-insensitive" (`FoldEq`);
* §5.5 *Field Values*:
  `field-value = *field-content`,
  `field-content = field-vchar [ 1*( SP / HTAB / field-vchar ) field-vchar ]`,
  `field-vchar = VCHAR / obs-text`, `obs-text = %x80-FF` (`FieldVChar`, `FieldContent`,
  `FieldValue`); and "Field values containing CR, LF, or NUL characters are invalid and
  dangerous ... a recipient ... MUST either reject the message or replace each of those
  characters with SP" (`NoCrLfNul`);
* §5.3 *Field Order*: a recipient "MAY combine multiple field lines within a field section
  that have the same field name into one field line, without changing the semantics of the
  message, by appending each subsequent field line value to the initial field line value in
  order, separated by a comma (",") and optional whitespace" (`combine`, with `", "`);
* RFC 5234 B.1: `ALPHA = %x41-5A / %x61-7A`, `DIGIT = %x30-39`, `VCHAR = %x21-7E`,
  `SP = %x20`, `HTAB = %x09`.

The grammars are inductive propositions read off the ABNF; `tcharB`, `fieldValueB` are the
decision procedures, proved equal to them in `HttpRfc.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.HttpRfc

/-! ## Core rules (RFC 5234 B.1) -/

/-- `ALPHA = %x41-5A / %x61-7A`. -/
def IsAlpha (n : Nat) : Prop := (0x41 ≤ n ∧ n ≤ 0x5A) ∨ (0x61 ≤ n ∧ n ≤ 0x7A)

/-- `DIGIT = %x30-39`. -/
def IsDigit (n : Nat) : Prop := 0x30 ≤ n ∧ n ≤ 0x39

/-- The fifteen punctuation characters of `tchar` (RFC 9110 §5.6.2), as code points. -/
def tcharPunct : List Nat :=
  [0x21, 0x23, 0x24, 0x25, 0x26, 0x27, 0x2A, 0x2B, 0x2D, 0x2E, 0x5E, 0x5F, 0x60, 0x7C, 0x7E]

/-! ## Tokens (RFC 9110 §5.6.2) and field names (§5.1) -/

/-- **`tchar`** (RFC 9110 §5.6.2), on a code point. -/
def Tchar (n : Nat) : Prop := n ∈ tcharPunct ∨ IsDigit n ∨ IsAlpha n

/-- **`token = 1*tchar`** (RFC 9110 §5.6.2), on characters. -/
inductive Token : List Char → Prop where
  /-- One `tchar`. -/
  | one {c : Char} : Tchar c.toNat → Token [c]
  /-- A `tchar` followed by a token. -/
  | cons {c : Char} {w : List Char} : Tchar c.toNat → Token w → Token (c :: w)

/-- **`field-name = token`** (RFC 9110 §5.1). -/
abbrev FieldName (n : List Char) : Prop := Token n

/-- The decision procedure of `tchar`. -/
def tcharB (n : Nat) : Bool :=
  tcharPunct.contains n || (0x30 ≤ n && n ≤ 0x39) || (0x41 ≤ n && n ≤ 0x5A) ||
    (0x61 ≤ n && n ≤ 0x7A)

/-- The decision procedure of `token`. -/
def tokenB (w : List Char) : Bool := !w.isEmpty && w.all (fun c => tcharB c.toNat)

/-- ASCII case folding (`A`-`Z` to `a`-`z`), the only folding RFC 9110 §5.1 needs: field names
are tokens, which are ASCII. -/
def foldN (n : Nat) : Nat := if 0x41 ≤ n ∧ n ≤ 0x5A then n + 0x20 else n

/-- **Case-insensitive equality of field names** (RFC 9110 §5.1): equal after ASCII folding,
character by character. -/
def FoldEq (a b : List Char) : Prop := a.map (foldN ∘ Char.toNat) = b.map (foldN ∘ Char.toNat)

/-! ## Field values (RFC 9110 §5.5) -/

/-- `VCHAR = %x21-7E` (RFC 5234). -/
def IsVChar (n : Nat) : Prop := 0x21 ≤ n ∧ n ≤ 0x7E

/-- `obs-text = %x80-FF` (RFC 9110 §5.6.4). -/
def IsObsText (n : Nat) : Prop := 0x80 ≤ n ∧ n ≤ 0xFF

/-- **`field-vchar = VCHAR / obs-text`** (RFC 9110 §5.5), on an octet. -/
def FieldVChar (b : BitVec 8) : Prop := IsVChar b.toNat ∨ IsObsText b.toNat

/-- `SP / HTAB / field-vchar`: the octets allowed inside a field value (RFC 9110 §5.5). -/
def FieldInner (b : BitVec 8) : Prop := b.toNat = 0x20 ∨ b.toNat = 0x09 ∨ FieldVChar b

/-- **`field-content = field-vchar [ 1*( SP / HTAB / field-vchar ) field-vchar ]`**
(RFC 9110 §5.5). -/
inductive FieldContent : List (BitVec 8) → Prop where
  /-- `field-vchar`. -/
  | one {c : BitVec 8} : FieldVChar c → FieldContent [c]
  /-- `field-vchar 1*( SP / HTAB / field-vchar ) field-vchar`. -/
  | wrap {c d : BitVec 8} {mid : List (BitVec 8)} : FieldVChar c → mid ≠ [] →
      (∀ x ∈ mid, FieldInner x) → FieldVChar d → FieldContent (c :: mid ++ [d])

/-- **`field-value = *field-content`** (RFC 9110 §5.5). -/
inductive FieldValue : List (BitVec 8) → Prop where
  /-- The empty value. -/
  | nil : FieldValue []
  /-- A `field-content` followed by a field value. -/
  | app {a b : List (BitVec 8)} : FieldContent a → FieldValue b → FieldValue (a ++ b)

/-- The decision procedure of `field-vchar`. -/
def fieldVCharB (b : BitVec 8) : Bool := (0x21 ≤ b.toNat && b.toNat ≤ 0x7E) || 0x80 ≤ b.toNat

/-- The decision procedure of `SP / HTAB / field-vchar`. -/
def fieldInnerB (b : BitVec 8) : Bool := b.toNat == 0x20 || b.toNat == 0x09 || fieldVCharB b

/-- **The decision procedure of `field-value`**: every octet is `SP`, `HTAB` or a
`field-vchar`, and a nonempty value starts and ends with a `field-vchar` (no leading or
trailing whitespace). -/
def fieldValueB (v : List (BitVec 8)) : Bool :=
  v.all fieldInnerB && (v.head?.all fieldVCharB) && (v.reverse.head?.all fieldVCharB)

/-- **No CR, LF or NUL** (RFC 9110 §5.5: such values are "invalid and dangerous" and must be
rejected or repaired by a recipient). -/
def NoCrLfNul (v : List (BitVec 8)) : Prop := ∀ b ∈ v, b.toNat ≠ 0 ∧ b.toNat ≠ 0x0A ∧ b.toNat ≠ 0x0D

/-! ## Field-line combination (RFC 9110 §5.3) -/

/-- `", "`. -/
def commaSp : List (BitVec 8) := [0x2C, 0x20]

/-- **The combined field value** of field lines with one name (RFC 9110 §5.3): the values in
order, separated by `", "`. -/
def combine : List (List (BitVec 8)) → List (BitVec 8)
  | [] => []
  | [v] => v
  | v :: w :: rest => v ++ commaSp ++ combine (w :: rest)

/-- **The combined value of a name in WASI `fields`**: the RFC 9110 §5.3 combination of the
values `fields.get(name)` answers (`Net.valsOfName`, names compared case-insensitively). -/
def combinedOf (m : Silmaril.Wasi.Versions.Net.Fields) (n : List Char) : List (BitVec 8) :=
  combine (Silmaril.Wasi.Versions.Net.valsOfName m n)

end Silmaril.Wasi.Versions.HttpRfc
