module

public import Silmaril.Cerberus.Mem.Layout.Defs

/-! Type compatibility at b3e11ea3, frontend/model/ail/ailTypesAux.lem:780-882.
The recursive bound reports exhaustion rather than declaring compatibility. -/

@[expose] public section
namespace Silmaril.Cerberus.Core

/-- ocaml_frontend/ocaml_implementation.ml:38-65,154-171. Enum registration
is supplied by the checked document registry. -/
def normalizeInteger (ity : IntegerType) (enums : Map Sym IntegerType := ∅) : Option IntegerType :=
  match ity with
  | .signed b => (.signed ·) <$> base b
  | .unsigned b => (.unsigned ·) <$> base b
  | .wchar | .wint => some (.signed .int)
  | .size => some (.unsigned .long)
  | .ptrdiff => some (.signed .long)
  | .enum tag => enums.lookup tag
  | t => some t
where
  base : IntegerBaseType → Option IntegerBaseType
    | .intN n | .intLeastN n | .intFastN n =>
        match n with
        | 8 => some .ichar | 16 => some .short | 32 => some .int | 64 => some .long
        | _ => none
    | .intmax | .intptr => some .long
    | b => some b

def noQualifiers : Qualifiers := ⟨false, false, false⟩

/-- Basic type equality follows normalization; char remains distinct from
signed char, and equal-width long and long long remain distinct. -/
def compatibleBasicWith (enums : Map Sym IntegerType) : BasicType → BasicType → Except String Bool
  | .integer a, .integer b => do
      let some a := normalizeInteger a enums | throw "integer compatibility normalization"
      let some b := normalizeInteger b enums | throw "integer compatibility normalization"
      pure (a == b)
  | .floating a, .floating b => pure (a == b)
  | .integer a, .floating _ | .floating _, .integer a => do
      let some _ := normalizeInteger a enums | throw "integer compatibility normalization"
      pure false

/-- Qualifiers are checked at every recursive level. Array elements and
function parameters use the unqualified types. Tags use symbol.lem:160-165
key equality, independent of their printable descriptions. -/
def compatibleWith (enums : Map Sym IntegerType) : Nat → Qualifiers → Ctype →
    Qualifiers → Ctype → Except String Bool
  | 0, _, _, _, _ => .error "recursive compatibility fuel"
  | fuel+1, qa, .mk _ a, qb, .mk _ b => do
      if qa != qb then return false
      match a, b with
      | .void, .void | .byte, .byte => pure true
      | .basic a, .basic b => compatibleBasicWith enums a b
      | .array a na, .array b nb => do
          let elements ← compatibleWith enums fuel noQualifiers a noQualifiers b
          pure (elements && match na, nb with
            | some n, some m => n == m
            | _, _ => true)
      | .pointer qa a, .pointer qb b => compatibleWith enums fuel qa a qb b
      | .struct a, .struct b | .union a, .union b => pure (Mem.Concrete.symbolEq a b)
      | .atomic a, .atomic b => compatibleWith enums fuel noQualifiers a noQualifiers b
      | .function (qa, a) pa va, .function (qb, b) pb vb => do
          let ret ← compatibleWith enums fuel qa a qb b
          let params ← parameterPairs pa pb |>.mapM fun ((_, a, _), (_, b, _)) =>
            compatibleWith enums fuel noQualifiers a noQualifiers b
          pure (ret && pa.length == pb.length && params.all id && va == vb)
      | .functionNoParams (qa, a), .functionNoParams (qb, b) => compatibleWith enums fuel qa a qb b
      | .function (qa, a) _ variadic, .functionNoParams (qb, b)
      | .functionNoParams (qa, a), .function (qb, b) _ variadic => do
          pure ((← compatibleWith enums fuel qa a qb b) && !variadic)
      | _, _ => pure false
where
  parameterPairs := List.zip

/-- Compatibility without enum registrations retains the legacy interface. -/
def compatibleBasic := compatibleBasicWith ∅
def compatible := compatibleWith ∅

end Silmaril.Cerberus.Core
