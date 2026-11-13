module

public import Silmaril.Cerberus.Ctype.Defs

/-! # C types: the helpers of `Ctype`, `IntegerType` and the implementation

Ports of the functions of `frontend/model/ctype.lem` and `frontend/model/integerType.lem`
that the desugaring and the typing use, and of the integer-type normalisation of
`ocaml_frontend/ocaml_implementation.ml` (`DefaultImpl`, which the oracle runs), at
`b3e11ea3`.

Lem's equalities on these types are not structural (`Silmaril.Cerberus.Ctype`): enum tags
compare as symbols, by `Sym.key`, and `ctypeEqual` ignores annotations, compares function
parameters through `List.zip`, and only the shapes of pointer types.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- `Ctype.make_qualifiers` (`ctype.lem:251`). -/
def makeQualifiers (c r v : Bool) : Qualifiers := ⟨c, r, v⟩

/-- `Ctype.no_qualifiers` (`ctype.lem:258`). -/
def noQualifiers : Qualifiers := ⟨false, false, false⟩

/-- `Ctype.combine_qualifiers` (`ctype.lem:265`). -/
def combineQualifiers (qs₁ qs₂ : Qualifiers) : Qualifiers :=
  ⟨qs₁.const || qs₂.const, qs₁.restrict || qs₂.restrict, qs₁.volatile || qs₂.volatile⟩

/-- `Ctype.proj_ctype_` (`ctype.lem:236`). -/
def projCtype_ : Ctype → CtypeNode
  | .mk _ ty => ty

/-- `Ctype.unatomic` (`ctype.lem:239`). -/
def unatomic : Ctype → Ctype
  | .mk _ (.atomic ty) => ty
  | ty => ty

/-- `Ctype.unatomic_` (`ctype.lem:247`). -/
def unatomic_ (ty : Ctype) : CtypeNode := projCtype_ (unatomic ty)

/-- `Ctype.mk_ctype_integer` (`ctype.lem:277`). -/
def mkCtypeInteger (ity : IntegerType) : Ctype := .mk [] (.basic (.integer ity))

/-- `Ctype.mk_ctype_atomic` (`ctype.lem:280`): `none` where Lem fails (an array, function or
atomic inner type). -/
def mkCtypeAtomic : Ctype → Option Ctype
  | .mk _ (.array ..) | .mk _ (.function ..) | .mk _ (.functionNoParams _) | .mk _ (.atomic _) =>
    none
  | cty => some (.mk [] (.atomic cty))

/-- `Ctype.is_unsigned_char` (`ctype.lem:342`). -/
def isUnsignedChar : Ctype → Bool
  | .mk _ (.basic (.integer (.unsigned .ichar))) => true
  | _ => false

/-- `Ctype.intptr_t` (`ctype.lem:330`). -/
def intptr_t : Ctype := mkCtypeInteger (.signed .intptr)
/-- `Ctype.intmax_t` (`ctype.lem:334`). -/
def intmax_t : Ctype := mkCtypeInteger (.signed .intmax)
/-- `Ctype.uintptr_t` (`ctype.lem:367`). -/
def uintptr_t : Ctype := mkCtypeInteger (.unsigned .intptr)
/-- `Ctype.uintmax_t` (`ctype.lem:371`). -/
def uintmax_t : Ctype := mkCtypeInteger (.unsigned .intmax)
/-- `Ctype.wchar_t` (`ctype.lem:385`). -/
def wchar_t : Ctype := mkCtypeInteger .wchar
/-- `Ctype.size_t` (`ctype.lem:389`). -/
def size_t : Ctype := mkCtypeInteger .size
/-- `Ctype.ptrdiff_t` (`ctype.lem:393`). -/
def ptrdiff_t : Ctype := mkCtypeInteger .ptrdiff

/-- `IntegerType.integerBaseTypeEqual` (`integerType.lem:41-72`). -/
def integerBaseTypeEqual : IntegerBaseType → IntegerBaseType → Bool
  | a, b => a == b

/-- `IntegerType.integerTypeEqual` (`integerType.lem:79-111`): enum tags compare by
`Sym.key`. -/
def integerTypeEqual : IntegerType → IntegerType → Bool
  | .enum s₁, .enum s₂ => s₁.key == s₂.key
  | a, b => a == b

/-- `Ctype.basicTypeEqual` (`ctype.lem:101`). -/
def basicTypeEqual : BasicType → BasicType → Bool
  | .integer i₁, .integer i₂ => integerTypeEqual i₁ i₂
  | .floating f₁, .floating f₂ => f₁ == f₂
  | _, _ => false

/-- `Ctype.qualifiersEqual` (`ctype.lem:123`). -/
def qualifiersEqual (qs₁ qs₂ : Qualifiers) : Bool := qs₁ == qs₂

mutual

/-- `Ctype.ctypeEqual` (`ctype.lem:134-184`): annotations are ignored, function parameters
are compared pairwise through `List.zip`, and two pointer, void or byte types are equal
whatever they point to. -/
def ctypeEqual : Ctype → Ctype → Bool
  | .mk _ ty₁, .mk _ ty₂ => ctypeNodeEqual ty₁ ty₂

/-- The match of `ctypeEqual` on the shapes. -/
def ctypeNodeEqual : CtypeNode → CtypeNode → Bool
  | .basic b₁, .basic b₂ => basicTypeEqual b₁ b₂
  | .array t₁ n₁, .array t₂ n₂ => ctypeEqual t₁ t₂ && n₁ == n₂
  | .function (qs₁, t₁) ps₁ b₁, .function (qs₂, t₂) ps₂ b₂ =>
    qualifiersEqual qs₁ qs₂ && ctypeEqual t₁ t₂ && paramsEqual ps₁ ps₂ && b₁ == b₂
  | .functionNoParams (qs₁, t₁), .functionNoParams (qs₂, t₂) =>
    qualifiersEqual qs₁ qs₂ && ctypeEqual t₁ t₂
  | .atomic t₁, .atomic t₂ => ctypeEqual t₁ t₂
  | .struct s₁, .struct s₂ => s₁.key == s₂.key
  | .union s₁, .union s₂ => s₁.key == s₂.key
  | .void, .void | .pointer .., .pointer .. | .byte, .byte => true
  | _, _ => false

/-- `List.all (uncurry paramsEqual) (List.zip params1 params2)`: the common prefix. -/
def paramsEqual : List (Qualifiers × Ctype × Bool) → List (Qualifiers × Ctype × Bool) → Bool
  | (qs₁, t₁, b₁) :: ps₁, (qs₂, t₂, b₂) :: ps₂ =>
    qualifiersEqual qs₁ qs₂ && ctypeEqual t₁ t₂ && b₁ == b₂ && paramsEqual ps₁ ps₂
  | _, _ => true

end

/-- The aliases of `DefaultImpl.type_alias_map` (`ocaml_implementation.ml:154-171`) for
`intN_t`, `int_leastN_t` and `int_fastN_t`. -/
def nTAliases : Nat → Option IntegerBaseType
  | 8 => some .ichar
  | 16 => some .short
  | 32 => some .int
  | 64 => some .long
  | _ => none

/-- `Common.normalise_integerType_` under `DefaultImpl` (`ocaml_implementation.ml:37-66`):
the standard aliases replaced by the implementation's types, and an enum by its registered
type (`typeofEnum`, the implementation's `registered_enums`). `none` where Cerberus fails
(an alias of an unsupported width). -/
def normaliseIntegerType (typeofEnum : Sym → Option IntegerType) (ity : IntegerType) :
    Option IntegerType :=
  let auxIbty : IntegerBaseType → Option IntegerBaseType
    | .intN n | .intLeastN n | .intFastN n => nTAliases n
    | .intmax | .intptr => some .long
    | ibty => some ibty
  match ity with
  | .signed ibty => .signed <$> auxIbty ibty
  | .unsigned ibty => .unsigned <$> auxIbty ibty
  | .enum tag => typeofEnum tag
  | .wchar | .wint => some (.signed .int)
  | .size => some (.unsigned .long)
  | .ptrdiff => some (.signed .long)
  | ity => some ity

end Silmaril.Cerberus.Frontend
