module

public import Silmaril.Net.Http.Abnf.Defs

@[expose] public section

/-!
# HTTP fields (RFC 9110 §5)

Fields are name/value pairs that carry metadata in the header and trailer sections of a
message (RFC 9110 §5). This module gives

* **field names** (§5.1): `field-name = token`, `token = 1*tchar` (§5.6.2), with the `tchar`
  grammar written literally (`tchar`, `token`) and the check `isToken`;
* **field values** (§5.5): `field-value = *field-content`,
  `field-content = field-vchar [ 1*( SP / HTAB / field-vchar ) field-vchar ]`,
  `field-vchar = VCHAR / obs-text`, as the grammar `fieldValue` and the check `isFieldValue`
  (a value is empty, or its octets are `SP`, `HTAB` or `field-vchar` and it starts and ends with
  a `field-vchar`); the lenient check `isSafeValue` of §5.5 ("Field values containing CR, LF,
  or NUL characters are invalid and dangerous");
* **field lines and sections** (§5.2, §5.3): a section is the list of its field lines in order;
  names are compared case-insensitively (§5.1: "Field names are case-insensitive");
  `Section.values` lists the values of a name in order, and `combine` is the combination of
  §5.3 ("appending each subsequent field line value to the initial field line value in order,
  separated by a comma (",") and optional whitespace … For consistency, use comma SP"). Empty
  values are skipped: they are empty list elements, which a recipient ignores (§5.6.1.2).

The grammar/check equalities are in `Field/Thms.lean` (`token_iff`, `fieldValue_iff`).

Not covered yet (roadmap, docs/projects/wasm-wasi.md): the list-based field grammar `#rule` (§5.6.1),
quoted strings and comments (§5.6.4, §5.6.5), parameters (§5.6.6), the field registry and
per-field grammars (§5.4, §5.6.7 dates), field limits (§5.4).
-/

namespace Silmaril.Net.Http.Field

open Silmaril.Formats.Grammar.Ebnf
open Silmaril.Net.Http.Abnf

/-! ## Tokens (§5.6.2) -/

/-- The punctuation of `tchar`:
`"!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" / "." / "^" / "_" / "`" / "|" / "~"`. -/
def tcharPunct : List UInt8 :=
  [0x21, 0x23, 0x24, 0x25, 0x26, 0x27, 0x2A, 0x2B, 0x2D, 0x2E, 0x5E, 0x5F, 0x60, 0x7C, 0x7E]

/-- `tchar` (§5.6.2): the punctuation of `tcharPunct`, `DIGIT` or `ALPHA`. -/
def tchar {N : Type} : Expr UInt8 N := .alternative (anyOf tcharPunct) (.alternative digit alpha)

/-- The check of `tchar`. -/
def isTchar (b : UInt8) : Bool := tcharPunct.contains b || isDigit b || isAlpha b

/-- `token = 1*tchar` (§5.6.2). -/
def token {N : Type} : Expr UInt8 N := Expr.oneOrMore tchar

/-- The check of `token`. -/
def isToken (xs : List UInt8) : Bool := !xs.isEmpty && xs.all isTchar

/-- `field-name = token` (§5.1). -/
def fieldName {N : Type} : Expr UInt8 N := token

/-- `tchar` on characters: an ASCII character whose octet is a `tchar`. -/
def isTcharChar (c : Char) : Bool := decide (c.toNat < 128) && isTchar c.toNat.toUInt8

/-- A field name given as a string (as WASI does): an ASCII token. -/
def isTokenChars (s : List Char) : Bool :=
  match asciiOctets? s with
  | some xs => isToken xs
  | none => false

/-! ## Field values (§5.5) -/

/-- `field-vchar = VCHAR / obs-text`. -/
def fieldVchar {N : Type} : Expr UInt8 N := .alternative vchar obsText

/-- The check of `field-vchar`. -/
def isFieldVchar (b : UInt8) : Bool := isVchar b || isObsText b

/-- `SP / HTAB / field-vchar`: the octets that may occur in a field value. -/
def fieldChar {N : Type} : Expr UInt8 N := .alternative (.alternative sp htab) fieldVchar

/-- The check of `SP / HTAB / field-vchar`. -/
def isFieldChar (b : UInt8) : Bool := isWsp b || isFieldVchar b

/-- `field-content = field-vchar [ 1*( SP / HTAB / field-vchar ) field-vchar ]`. -/
def fieldContent {N : Type} : Expr UInt8 N :=
  .sequence fieldVchar (Expr.optional (.sequence (Expr.oneOrMore fieldChar) fieldVchar))

/-- `field-value = *field-content`. -/
def fieldValue {N : Type} : Expr UInt8 N := .repetition fieldContent

/-- The check of `field-value`: every octet is `SP`, `HTAB` or a `field-vchar`, and the value
does not start or end with whitespace. -/
def isFieldValue (v : List UInt8) : Bool :=
  v.all isFieldChar && v.head?.all isFieldVchar && v.getLast?.all isFieldVchar

/-- The lenient check of §5.5: no NUL, CR or LF ("Field values containing CR, LF, or NUL
characters are invalid and dangerous"; a recipient MAY retain other control characters). -/
def isSafeValue (v : List UInt8) : Bool := v.all (fun b => b != 0x00 && b != 0x0A && b != 0x0D)

/-! ## Field lines and sections (§5.2, §5.3) -/

/-- A field line (§5.2): a name and a value. -/
structure Line where
  /-- The field name, as sent (case is not significant). -/
  name : List UInt8
  /-- The field line value. -/
  value : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- A valid field line: a token name and a `field-value`. -/
def Line.isValid (l : Line) : Bool := isToken l.name && isFieldValue l.value

/-- A field section (§5.2, §6.3, §6.5): its field lines, in order. -/
abbrev Section := List Line

/-- Every line of the section is valid. -/
def Section.isValid (s : Section) : Bool := s.all Line.isValid

/-- The lines of the name `n` (case-insensitive, §5.1), in order. -/
def Section.lines (s : Section) (n : List UInt8) : List Line :=
  s.filter (fun l => eqIgnoreCase l.name n)

/-- The field line values of the name `n`, in order (§5.3: their order is significant). -/
def Section.values (s : Section) (n : List UInt8) : List (List UInt8) :=
  (s.lines n).map Line.value

/-- Whether the section has a line of the name `n`. -/
def Section.has (s : Section) (n : List UInt8) : Bool := s.any (fun l => eqIgnoreCase l.name n)

/-- The section without the lines of the name `n`. -/
def Section.remove (s : Section) (n : List UInt8) : Section :=
  s.filter (fun l => !eqIgnoreCase l.name n)

/-- Append a field line. -/
def Section.append (s : Section) (n v : List UInt8) : Section := s ++ [⟨n, v⟩]

/-- Replace the lines of `n` by one line per value, at the end. -/
def Section.set (s : Section) (n : List UInt8) (vs : List (List UInt8)) : Section :=
  s.remove n ++ vs.map (fun v => ⟨n, v⟩)

/-- `", "`, the separator of combined values (§5.3: "use comma SP"). -/
def commaSp : List UInt8 := [0x2C, 0x20]

/-- The combination of field line values (§5.3): the non-empty values, in order, separated by
`", "`. -/
def combine (vs : List (List UInt8)) : List UInt8 := commaSp.intercalate (vs.filter (· ≠ []))

/-- The field value of the name `n` (§5.2: "the field value … is the result of combining
[the field line values] in order"); `none` when the section has no line of the name. -/
def Section.fieldValue? (s : Section) (n : List UInt8) : Option (List UInt8) :=
  if s.has n then some (combine (s.values n)) else none

/-- The names of a list, without later case-insensitive repetitions (first occurrences, in
order). -/
def dedupNames : List (List UInt8) → List (List UInt8)
  | [] => []
  | x :: xs => x :: dedupNames (xs.filter (fun y => !eqIgnoreCase y x))
termination_by xs => xs.length
decreasing_by
  rw [List.length_unattach, List.length_cons]
  exact Nat.lt_succ_of_le ((List.length_filter_le _ _).trans (List.length_attach ..).le)

/-- The distinct field names of a section, case-insensitively, as first sent. -/
def Section.names (s : Section) : List (List UInt8) := dedupNames (s.map Line.name)

/-- The section with the lines of each name combined into one (§5.3), at the position of the
name's first line. -/
def Section.combineAll (s : Section) : Section :=
  s.names.map (fun n => ⟨n, combine (s.values n)⟩)

end Silmaril.Net.Http.Field
