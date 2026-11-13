module

public import Silmaril.Cerberus.Ctype.Defs

/-! Explicit target inputs for the pinned Cerberus frontend. Adapted from
`ocaml_frontend/ocaml_implementation.ml` and `ail/integerImpl.lem` at
`rems-project/cerberus@b3e11ea334e95359907d4abf9194f0e7fedc6c6a` (see
`NOTICES/Cerberus`). This preserves the Apple default,
including its eight-byte floating-layout shortcuts. It is not a System V
layout model. Unsupported aliases and missing enum bindings return errors.
-/

@[expose] public section
namespace Silmaril.Cerberus.Target
open Silmaril.Cerberus

structure Layout where
  size : Nat
  alignment : Nat
  deriving DecidableEq, Repr

inductive BinaryMode where
  | twosComplement | onesComplement | signMagnitude
  deriving DecidableEq, Repr

/-- One-step alias maps, as in upstream `Common.normalise_integerType_`. -/
structure Aliases where
  intN : Nat → Option IntegerBaseType
  intLeastN : Nat → Option IntegerBaseType
  intFastN : Nat → Option IntegerBaseType
  intmax : IntegerBaseType
  intptr : IntegerBaseType
  wchar : IntegerType
  wint : IntegerType
  size : IntegerType
  ptrdiff : IntegerType

/-- Explicit replacement for the upstream selected implementation/global switch.
No well-formedness or native-target equivalence is asserted by this record. -/
structure Config where
  name : String
  binaryMode : BinaryMode
  plainCharSigned : Bool
  charLayout : Layout
  boolLayout : Layout
  baseLayout : IntegerBaseType → Option Layout
  floatLayout : FloatingType → Option Layout
  pointerLayout : Option Layout
  maximumAlignment : Nat
  aliases : Aliases
  cheri : Bool := false

inductive Error where
  | unsupportedWidth (width : Nat)
  | unsupportedBase (type : IntegerBaseType)
  | unresolvedInteger (type : IntegerType)
  | missingLayout
  | unregisteredEnum (symbol : Sym)
  | duplicateEnum (symbol : Sym)
  | unsupportedRangeComparison (left right : IntegerType)
  | untypableIntegerConstant (location : Loc) (value : Int)
  | unsupportedCheri
  deriving DecidableEq, Repr

/-- Enum bindings use Cerberus symbol identity, not diagnostic descriptions. -/
structure Environment where
  enums : Map Sym IntegerType

def emptyEnvironment : Environment := ⟨∅⟩

/-- `DefaultImpl.register_enum`: no `-fshort-enums`, and no duplicate binding. -/
def registerEnum (env : Environment) (symbol : Sym) (values : List Int) :
    Except Error Environment :=
  if (Map.lookup symbol env.enums).isSome then .error (.duplicateEnum symbol)
  else
    let type := if values.any (fun n => decide (n < 0)) then
      IntegerType.signed .int else .unsigned .int
    .ok ⟨Map.insert symbol type env.enums⟩

def lookupEnum (env : Environment) (symbol : Sym) : Except Error IntegerType :=
  match Map.lookup symbol env.enums with
  | some type => .ok type
  | none => .error (.unregisteredEnum symbol)

def pinnedWidthAlias : Nat → Option IntegerBaseType
  | 8 => some .ichar
  | 16 => some .short
  | 32 => some .int
  | 64 => some .long
  | _ => none

def pinnedBaseLayout : IntegerBaseType → Option Layout
  | .ichar => some ⟨1, 1⟩
  | .short => some ⟨2, 2⟩
  | .int => some ⟨4, 4⟩
  | .long | .longLong => some ⟨8, 8⟩
  | _ => none

/-- Exact `DefaultImpl.impl`, including the source's float/long-double TODOs. -/
def pinnedApple : Config where
  name := "clang9_x86_64-apple-darwin16.7.0"
  binaryMode := .twosComplement
  plainCharSigned := true
  charLayout := ⟨1, 1⟩
  boolLayout := ⟨1, 1⟩
  baseLayout := pinnedBaseLayout
  floatLayout := fun _ => some ⟨8, 8⟩
  pointerLayout := some ⟨8, 8⟩
  maximumAlignment := 8
  aliases := {
    intN := pinnedWidthAlias, intLeastN := pinnedWidthAlias, intFastN := pinnedWidthAlias
    intmax := .long, intptr := .long
    wchar := .signed .int, wint := .signed .int
    size := .unsigned .long, ptrdiff := .signed .long }

def resolveWidth (lookup : Nat → Option IntegerBaseType) (n : Nat) :
    Except Error IntegerBaseType :=
  match lookup n with
  | some type => .ok type
  | none => .error (.unsupportedWidth n)

def normalizeBase (config : Config) : IntegerBaseType → Except Error IntegerBaseType
  | .intN n => resolveWidth config.aliases.intN n
  | .intLeastN n => resolveWidth config.aliases.intLeastN n
  | .intFastN n => resolveWidth config.aliases.intFastN n
  | .intmax => .ok config.aliases.intmax
  | .intptr => .ok config.aliases.intptr
  | type => .ok type

/-- One normalization step; `ptraddr` remains its own type upstream. -/
def normalize (config : Config) (env : Environment) : IntegerType → Except Error IntegerType
  | .signed type => return .signed (← normalizeBase config type)
  | .unsigned type => return .unsigned (← normalizeBase config type)
  | .enum symbol => lookupEnum env symbol
  | .wchar => .ok config.aliases.wchar
  | .wint => .ok config.aliases.wint
  | .size => .ok config.aliases.size
  | .ptrdiff => .ok config.aliases.ptrdiff
  | type => .ok type

def directSignedness (config : Config) : IntegerType → Except Error Bool
  | .char => .ok config.plainCharSigned
  | .bool | .unsigned _ | .size | .ptraddr => .ok false
  | .signed _ | .wchar | .wint | .ptrdiff => .ok true
  | .enum symbol => .error (.unregisteredEnum symbol)

/-- `Common.is_signed_ity`: resolve enum bindings, preserving the source's
fixed signedness of special typedef names. -/
def signedness (config : Config) (env : Environment) (type : IntegerType) : Except Error Bool := do
  let type ← match type with
    | .enum symbol => lookupEnum env symbol
    | type => .ok type
  directSignedness config type

def normalizedLayout (config : Config) : IntegerType → Except Error Layout
  | .char => .ok config.charLayout
  | .bool => .ok config.boolLayout
  | .signed base | .unsigned base =>
      match config.baseLayout base with
      | some layout => .ok layout
      | none => .error (.unsupportedBase base)
  | .ptraddr =>
      match config.pointerLayout with
      | some layout => .ok layout
      | none => .error .missingLayout
  | type => .error (.unresolvedInteger type)

def integerLayout (config : Config) (env : Environment) (type : IntegerType) :
    Except Error Layout := do
  normalizedLayout config (← normalize config env type)

def floatingLayout (config : Config) (type : FloatingType) : Except Error Layout :=
  match config.floatLayout type with
  | some layout => .ok layout
  | none => .error .missingLayout

/-- `Common.precision_ity`; in particular the pinned `_Bool` gets eight bits. -/
def precision (config : Config) (env : Environment) (type : IntegerType) : Except Error Nat := do
  let layout ← integerLayout config env type
  let signed ← signedness config env type
  return if signed then 8 * layout.size - 1 else 8 * layout.size

structure IntegerRange where
  lower : Int
  upper : Int
  deriving DecidableEq, Repr

def IntegerRange.contains (range : IntegerRange) (value : Int) : Bool :=
  decide (range.lower ≤ value ∧ value ≤ range.upper)

/-- `IntegerImpl.integer_range`, with no replacement by host machine integers. -/
def integerRange (config : Config) (env : Environment) (type : IntegerType) :
    Except Error IntegerRange := do
  let bits ← precision config env type
  let signed ← signedness config env type
  let bound : Int := 2 ^ bits
  return if signed then
    match config.binaryMode with
    | .twosComplement => ⟨-bound, bound - 1⟩
    | .onesComplement | .signMagnitude => ⟨-bound + 1, bound - 1⟩
  else ⟨0, bound - 1⟩

/-- The equality used by upstream integer helpers ignores enum descriptions. -/
def integerEqual : IntegerType → IntegerType → Bool
  | .enum first, .enum second => decide (first.key = second.key)
  | first, second => decide (first = second)

end Silmaril.Cerberus.Target
