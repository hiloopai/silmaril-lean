module

public import Silmaril.Cerberus.Frontend.Monad.Defs

/-! # String literals

`string_literal` (`c_parser.mly:1753-1773`): adjacent `STRING_LITERAL` tokens, one
component per token with its region and its lexemes, nothing merged. The prefix is the
first explicit one; two different explicit prefixes are
`Cparser_non_standard_string_concatenation`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus Cabs P

/-- Whether the token is a `STRING_LITERAL`. -/
def isStringToken (t : Token) : Bool :=
  match t.kind with
  | .string .. => true
  | _ => false

/-- `string_literal_component`: one `STRING_LITERAL` with its region. -/
def stringLiteralComponent : P (Option EncodingPrefix × (Loc × List RawString)) := do
  let t ← advance
  match t.kind with
  | .string pfx xs => return (pfx, (t.start.region t.stop, xs.toList))
  | _ => fail "expected a string literal"

/-- `merge_prefix`: the first explicit prefix; a different later one is an error. -/
def mergePrefix (acc : Option EncodingPrefix) :
    List (Option EncodingPrefix) → Option (Option EncodingPrefix)
  | [] => some acc
  | none :: ps => mergePrefix acc ps
  | some p :: ps => match acc with
    | none => mergePrefix (some p) ps
    | some q =>
      let same := match p, q with
        | .utf8, .utf8 | .utf16, .utf16 | .utf32, .utf32 | .wide, .wide => true
        | _, _ => false
      if same then mergePrefix acc ps else none

/-- `string_literal`: `string_literal_component+`. -/
def stringLiteral : P StringLiteral := do
  let cs ← sepBy1Adjacent
  match mergePrefix none (cs.toList.map (·.1)) with
  | some pfx => return (pfx, cs.toList.map (·.2))
  | none => fail "non-standard string concatenation"
where
  sepBy1Adjacent : P (Array (Option EncodingPrefix × (Loc × List RawString))) := do
    let c ← stringLiteralComponent
    let cs ← manyWhile (return isStringToken (← peek)) stringLiteralComponent
    return #[c] ++ cs

/-- The text of raw lexemes, if they are all UTF-8 (attribute arguments are `string`s
of the Core port, which has no raw bytes). -/
def rawText (xs : List RawString) : Option String :=
  xs.foldlM (fun acc x => match x with
    | .utf8 t => some (acc ++ t)
    | .bytes _ => none) ""

end Silmaril.Cerberus.Frontend
