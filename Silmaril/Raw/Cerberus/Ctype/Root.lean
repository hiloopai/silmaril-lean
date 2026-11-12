module

public import Silmaril.Cerberus.Map.Defs

/-! # Cerberus C types and annotations

The types of Cerberus's `frontend/model/integerType.lem`,
`frontend/model/annot.lem` and `frontend/model/ctype.lem` at commit
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. The helper functions and
standard-type constants of those modules are not ported.

C types are nested inductives (through `List`, `Option` and products), for which
Lean's `DecidableEq` deriving handler does not apply, so they and every type
containing one derive only `Repr`.

Lem's equalities on these types are not structural. Integer types and basic types
compare enum tags as symbols, by `Sym.key`. `ctypeEqual` also ignores annotations,
and compares function parameter lists with `List.zip`, so lists of different
lengths can compare equal. A port of code that uses Lem's `=` on these types needs
a port of the corresponding Lem equality.
-/

@[expose] public section

namespace Silmaril.Cerberus

/-- The rank-carrying part of a signed or unsigned integer type. -/
inductive IntegerBaseType where
  | ichar
  | short
  | int
  | long
  | longLong
  | intN : Nat → IntegerBaseType
  | intLeastN : Nat → IntegerBaseType
  | intFastN : Nat → IntegerBaseType
  | intmax
  | intptr
  deriving DecidableEq, Repr

/-- C integer types (STD §6.2.5#17). -/
inductive IntegerType where
  | char
  | bool
  | signed : IntegerBaseType → IntegerType
  | unsigned : IntegerBaseType → IntegerType
  | enum : Sym → IntegerType
  | wchar
  | wint
  | size
  | ptrdiff
  | ptraddr
  deriving DecidableEq, Repr

/-- Bounded-model-checking annotations. -/
inductive BmcAnnot where
  | id : Nat → BmcAnnot
  deriving DecidableEq, Repr

/-- A C2X attribute `[[ns::id(args)]]`. -/
structure Attribute where
  ns : Option Identifier
  id : Identifier
  args : List (Loc × String × List (Loc × String))
  deriving DecidableEq, Repr

/-- A list of C2X attributes. -/
inductive Attributes where
  | mk : List Attribute → Attributes
  deriving DecidableEq, Repr

/-- Loop identifiers. -/
abbrev LoopId := Nat

/-- Where a Core label comes from. -/
inductive LabelAnnot where
  | loop : LoopId → LabelAnnot
  | loopContinue : LoopId → LabelAnnot
  | loopBreak : LoopId → LabelAnnot
  | return_
  | switch
  | case_
  | default
  | actualLabel
  deriving DecidableEq, Repr

/-- Cerberus-specific attributes. -/
inductive CerbAttribute where
  | withAddress : Int → CerbAttribute
  | hidden
  deriving DecidableEq, Repr

/-- Annotations on values. -/
inductive ValueAnnot where
  | integer : IntegerType → ValueAnnot
  deriving DecidableEq, Repr

/-- Annotations carried by C types, Core patterns and Core expressions. -/
inductive Annot where
  | std : String → Annot
  | loc : Loc → Annot
  | uid : String → Annot
  | marker : Nat → Annot
  | markerObjectTypes : Nat → Annot
  | bmc : BmcAnnot → Annot
  | attrs : Attributes → Annot
  | typedef : Sym → Annot
  | label : LabelAnnot → Annot
  | cerb : CerbAttribute → Annot
  | value : ValueAnnot → Annot
  | inlinedLabel : (Loc × Sym × LabelAnnot) → Annot
  | stmt
  | expr
  deriving DecidableEq, Repr

/-- Per-loop attributes recorded during elaboration. -/
structure LoopAttribute where
  markerId : Nat
  attributes : Attributes
  conditionLoc : Loc
  loopLoc : Loc
  deriving DecidableEq, Repr

/-- Loop attributes by loop identifier. -/
abbrev LoopAttributes := Map LoopId LoopAttribute

/-- Real floating types (STD §6.2.5#10). -/
inductive RealFloatingType where
  | float
  | double
  | longDouble
  deriving DecidableEq, Repr

/-- Floating types (STD §6.2.5#11); complex types are commented out in Lem. -/
inductive FloatingType where
  | realFloating : RealFloatingType → FloatingType
  deriving DecidableEq, Repr

/-- Basic types (STD §6.2.5#14). -/
inductive BasicType where
  | integer : IntegerType → BasicType
  | floating : FloatingType → BasicType
  deriving DecidableEq, Repr

/-- Type qualifiers (STD §6.2.5#26); `_Atomic` is a type constructor. -/
structure Qualifiers where
  const : Bool
  restrict : Bool
  volatile : Bool
  deriving DecidableEq, Repr

mutual

/-- The shape of a C type. The qualifiers of `array` are those of the element
type, and those of `pointer` are those of the referenced type. -/
inductive CtypeNode where
  | void
  | basic : BasicType → CtypeNode
  | array : Ctype → Option Int → CtypeNode
  | function : (Qualifiers × Ctype) → List (Qualifiers × Ctype × Bool) → Bool → CtypeNode
  | functionNoParams : (Qualifiers × Ctype) → CtypeNode
  | pointer : Qualifiers → Ctype → CtypeNode
  | atomic : Ctype → CtypeNode
  | struct : Sym → CtypeNode
  | union : Sym → CtypeNode
  | byte

/-- An annotated C type. -/
inductive Ctype where
  | mk : List Annot → CtypeNode → Ctype

end

deriving instance Repr for CtypeNode, Ctype

/-- A flexible array member; the `Ctype` is the element type. -/
inductive FlexibleArrayMember where
  | mk : Attributes → Identifier → Qualifiers → Ctype → FlexibleArrayMember
  deriving Repr

/-- A member alignment specifier. -/
inductive Alignment where
  | integer : Int → Alignment
  | ctype : Ctype → Alignment
  deriving Repr

/-- The definition of a struct or union tag. -/
inductive TagDefinition where
  | struct :
      List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) →
      Option FlexibleArrayMember → TagDefinition
  | union :
      List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) →
      TagDefinition
  deriving Repr

end Silmaril.Cerberus
