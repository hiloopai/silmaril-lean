module

public import Silmaril.Cerberus.Target.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs

/-! Fallible interpretation of the existing typed-Ail generalized types.
Adapted from pinned `ail/genTypesAux.lem:277-343`, `ail/ailTyping.lem:5-102`
and the default (non-CHERI) integer helpers in `ail/ailTypesAux.lem`.
Upstream nonstandard macro-type and range-comparison rules are retained.
This supplies prerequisites; it does not implement Ail-to-Core elaboration.
-/

@[expose] public section
namespace Silmaril.Cerberus.GeneralizedTypes
open Silmaril.Cerberus
open Target

/-- `eq_integer_rank`, including corresponding signed/unsigned types. -/
def eqIntegerRank (first second : IntegerType) : Bool :=
  integerEqual first second || match first, second with
    | .signed a, .unsigned b | .unsigned a, .signed b => decide (a = b)
    | .char, .signed .ichar | .char, .unsigned .ichar
    | .signed .ichar, .char | .unsigned .ichar, .char => true
    | _, _ => false

/-- The ordered pattern table in `lt_integer_rank_ISO`, including its upstream
macro-type limitations; this is not a normalized numeric ranking. -/
def ltIntegerRank : IntegerType → IntegerType → Bool
  | _, .bool => false
  | .bool, _ => true
  | _, .char | _, .signed .ichar | _, .unsigned .ichar => false
  | .char, .signed _ | .char, .unsigned _
  | .signed .ichar, .signed _ | .signed .ichar, .unsigned _
  | .unsigned .ichar, .signed _ | .unsigned .ichar, .unsigned _ => true
  | _, .signed .short | _, .unsigned .short => false
  | .signed .short, .signed _ | .signed .short, .unsigned _
  | .unsigned .short, .signed _ | .unsigned .short, .unsigned _ => true
  | _, .signed .int | _, .unsigned .int => false
  | .signed .int, .signed _ | .signed .int, .unsigned _
  | .unsigned .int, .signed _ | .unsigned .int, .unsigned _ => true
  | _, .signed .long | _, .unsigned .long => false
  | .signed .long, .signed _ | .signed .long, .unsigned _
  | .unsigned .long, .signed _ | .unsigned .long, .unsigned _ => true
  | _, _ => false

def leIntegerRank (first second : IntegerType) : Bool :=
  eqIntegerRank first second || ltIntegerRank first second

def normalizedBase : IntegerBaseType → Bool
  | .ichar | .short | .int | .long | .longLong => true
  | _ => false

def normalizedInteger : IntegerType → Bool
  | .char | .bool | .ptraddr => true
  | .signed base | .unsigned base => normalizedBase base
  | _ => false

/-- Faithful `le_integer_range` pattern table after one-step normalization.
It intentionally does not replace the source table by interval inclusion.
Source internal/WIP cases become explicit failures. -/
def leIntegerRange (config : Config) (env : Environment)
    (first second : IntegerType) : Except Error Bool := do
  let first ← normalize config env first
  let second ← normalize config env second
  if integerEqual first second then return true
  if !normalizedInteger first || !normalizedInteger second then
    throw (.unsupportedRangeComparison first second)
  let p := precision config env
  match first, second with
  | .char, .signed .ichar | .signed .ichar, .char => return config.plainCharSigned
  | .char, .signed base =>
      if config.plainCharSigned then return true
      else return decide ((← p .char) < (← p (.signed base)))
  | .signed base, .char =>
      if !config.plainCharSigned then return false
      else return decide ((← p (.signed base)) = (← p .char))
  | .unsigned .ichar, .char => return !config.plainCharSigned
  | .unsigned base, .char =>
      if config.plainCharSigned then return false
      else return decide ((← p (.unsigned base)) = (← p .char))
  | .char, .unsigned _ => return !config.plainCharSigned
  | .char, .bool =>
      if config.plainCharSigned then return false
      else return decide ((← p .char) = (← p .bool))
  | .bool, .char =>
      if !config.plainCharSigned then return true
      else return decide ((← p .bool) < (← p .char))
  | .signed .ichar, .signed _
  | .signed .short, .signed .int | .signed .short, .signed .long
  | .signed .short, .signed .longLong | .signed .int, .signed .long
  | .signed .int, .signed .longLong | .signed .long, .signed .longLong => return true
  | .signed a, .signed b => return decide ((← p (.signed a)) = (← p (.signed b)))
  | .signed _, .bool => return false
  | .bool, .signed base => return decide ((← p .bool) < (← p (.signed base)))
  | .bool, .unsigned _ | .unsigned .ichar, .unsigned _
  | .unsigned .short, .unsigned .int | .unsigned .short, .unsigned .long
  | .unsigned .short, .unsigned .longLong | .unsigned .int, .unsigned .long
  | .unsigned .int, .unsigned .longLong | .unsigned .long, .unsigned .longLong => return true
  | .unsigned base, .bool => return decide ((← p (.unsigned base)) = (← p .bool))
  | .unsigned a, .unsigned b => return decide ((← p (.unsigned a)) = (← p (.unsigned b)))
  | .signed _, .unsigned _ => return false
  | .unsigned _, .signed .ichar
  | .unsigned .short, .signed .short | .unsigned .int, .signed .int
  | .unsigned .long, .signed .long | .unsigned .longLong, .signed .longLong => return false
  | .unsigned a, .signed b => return decide ((← p (.unsigned a)) < (← p (.signed b)))
  | .char, .char | .bool, .bool | .ptraddr, .ptraddr => return true
  | _, _ => throw (.unsupportedRangeComparison first second)

/-- `integer_promotion`, including upstream's unaliased size/intptr exceptions. -/
def promote (config : Config) (env : Environment) (type : IntegerType) : Except Error IntegerType := do
  if config.cheri then throw .unsupportedCheri
  match type with
  | .signed .int | .unsigned .int | .size | .signed .intptr | .unsigned .intptr => return type
  | type =>
      if leIntegerRank type (.signed .int) then
        if ← leIntegerRange config env type (.signed .int) then return .signed .int
        else return .unsigned .int
      else return type

def correspondingUnsigned : IntegerType → IntegerType
  | .signed base => .unsigned base
  | type => type

/-- `usual_arithmetic_integer_default`, preserving size_t dominance and the
intptr_t cases before promotion. The CHERI algorithm is not ported here. -/
def usualInteger (config : Config) (env : Environment)
    (first second : IntegerType) : Except Error IntegerType := do
  if config.cheri then throw .unsupportedCheri
  match first, second with
  | .size, _ | _, .size => return .size
  | .signed .intptr, .unsigned .intptr | .unsigned .intptr, .signed .intptr =>
      return .unsigned .intptr
  | .signed .intptr, _ | _, .signed .intptr => return .signed .intptr
  | .unsigned .intptr, _ | _, .unsigned .intptr => return .unsigned .intptr
  | _, _ =>
      let first ← promote config env first
      let second ← promote config env second
      let signedFirst ← signedness config env first
      let signedSecond ← signedness config env second
      if signedFirst = signedSecond then
        return if ltIntegerRank first second then second else first
      else if !signedFirst && leIntegerRank second first then return first
      else if !signedSecond && leIntegerRank first second then return second
      else if signedFirst then
        if ← leIntegerRange config env second first then return first
        else return correspondingUnsigned first
      else
        if ← leIntegerRange config env first second then return second
        else return correspondingUnsigned second

/-- Candidate order is the exact `AilTyping.type_of_constant` table. Binary
spelling follows the source's non-decimal branch. -/
def constantCandidates (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) : List IntegerType :=
  match basis, suffix with
  | .decimal, none => [.signed .int, .signed .long, .signed .longLong]
  | _, none => [.signed .int, .unsigned .int, .signed .long, .unsigned .long,
      .signed .longLong, .unsigned .longLong]
  | _, some .u => [.unsigned .int, .unsigned .long, .unsigned .longLong]
  | .decimal, some .l => [.signed .long, .signed .longLong]
  | _, some .l => [.signed .long, .unsigned .long, .signed .longLong, .unsigned .longLong]
  | _, some .ul => [.unsigned .long, .unsigned .longLong]
  | .decimal, some .ll => [.signed .longLong]
  | _, some .ll => [.signed .longLong, .unsigned .longLong]
  | _, some .ull => [.unsigned .longLong]

/-- Select the first representable candidate; missing target data propagates. -/
def firstRepresentable (config : Config) (env : Environment) (loc : Loc) (value : Int) :
    List IntegerType → Except Error IntegerType
  | [] => .error (.untypableIntegerConstant loc value)
  | type :: rest => do
      let range ← integerRange config env type
      if range.contains value then return type
      else firstRepresentable config env loc value rest

def typeOfConstant (config : Config) (env : Environment) (loc : Loc) :
    Ail.IntegerConstant → Except Error IntegerType
  | .iconstant value basis suffix =>
      firstRepresentable config env loc value (constantCandidates basis suffix)
  | .max type | .min type => .ok type

/-- `interpret_genIntegerType`: concrete and special names are returned as
upstream names; only operations needing target facts consult the environment. -/
def interpretInteger (config : Config) (env : Environment) (loc : Loc) :
    Ail.GenIntegerType → Except Error IntegerType
  | .concrete type => .ok type
  | .sizeT => .ok .size
  | .ptrdiffT => .ok .ptrdiff
  | .ptraddrT => .ok .ptraddr
  | .unknown constant => typeOfConstant config env loc constant
  | .promote type => do promote config env (← interpretInteger config env loc type)
  | .usual first second => do
      usualInteger config env (← interpretInteger config env loc first)
        (← interpretInteger config env loc second)

def interpretBasic (config : Config) (env : Environment) (loc : Loc) :
    Ail.GenBasicType → Except Error BasicType
  | .integer type => return .integer (← interpretInteger config env loc type)
  | .floating type => .ok (.floating type)

/-- `interpret_genType`: only atomic generalized types recurse. Embedded Ctypes
are retained, and each newly constructed Ctype gets exactly `[Aloc loc]`. -/
def interpretType (config : Config) (env : Environment) (loc : Loc) :
    Ail.GenType → Except Error Ctype
  | .void => .ok (.mk [.loc loc] .void)
  | .basic type => return .mk [.loc loc] (.basic (← interpretBasic config env loc type))
  | .array elem size => .ok (.mk [.loc loc] (.array elem size))
  | .function result params variadic => .ok (.mk [.loc loc] (.function result params variadic))
  | .functionNoParams result => .ok (.mk [.loc loc] (.functionNoParams result))
  | .pointer qs type => .ok (.mk [.loc loc] (.pointer qs type))
  | .struct tag => .ok (.mk [.loc loc] (.struct tag))
  | .union tag => .ok (.mk [.loc loc] (.union tag))
  | .atomic type => return .mk [.loc loc] (.atomic (← interpretType config env loc type))
  | .byte => .ok (.mk [.loc loc] .byte)

/-- The interpreted `GenTypes.typeCategory` missing from the syntax-only port;
all payloads are the existing actual Ctype/qualifier/location types. -/
inductive TypeCategory where
  | lvalue (qualifiers : Qualifiers) (type : Ctype) (isRegister : Bool)
  | rvalue (type : Ctype)
  deriving Repr

def TypeCategory.type : TypeCategory → Ctype
  | .lvalue _ type _ | .rvalue type => type

def interpretCategory (config : Config) (env : Environment) (loc : Loc) :
    Ail.GenTypeCategory → Except Error TypeCategory
  | .lvalue qs type register => .ok (.lvalue qs type register)
  | .rvalue type => return .rvalue (← interpretType config env loc type)

/-- The type interpretation needed by `translation_aux.lem:205` without
performing expression elaboration or re-annotating the imported typed Ail. -/
def expressionType (config : Config) (env : Environment) (expression : Ail.TypedExpression) :
    Except Error Ctype := do
  return (← interpretCategory config env expression.loc expression.annotation).type

end Silmaril.Cerberus.GeneralizedTypes
