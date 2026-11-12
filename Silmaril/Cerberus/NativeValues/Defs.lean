module

public import Silmaril.Cerberus.NativeTypes.Defs

/-! Concrete native C values. This is an implementation-facing typing layer,
not a replacement interpretation of the imported Cerberus memory model. Pointer
identity, active union members and floating storage bits remain explicit. -/

@[expose] public section
namespace Silmaril.Cerberus.NativeValues

open NativeTypes

def IntegerRange (signedness : Signedness) (bits : Nat) (value : Int) : Prop :=
  match signedness with
  | .signed => -(2 ^ (bits - 1) : Int) ≤ value ∧ value < 2 ^ (bits - 1)
  | .unsigned => 0 ≤ value ∧ value < 2 ^ bits

instance integerRangeDecidable (signedness : Signedness) (bits : Nat) (value : Int) :
    Decidable (IntegerRange signedness bits value) := by
  unfold IntegerRange
  split <;> infer_instance

def ScalarValid (scalar : Scalar) : Prop := ∃ layout, scalar.layout = .ok layout

def Integral : Scalar → Prop
  | .floating _ => False
  | _ => True

def ScalarWidth : Scalar → Nat
  | .boolean => 1
  | .integer kind _ => 8 * kind.bytes
  | .bitInt precision _ => precision
  | .floating format => format.layout.valueBits

/-- Floating values here are format-indexed storage bit patterns. No numerical
IEEE, decimal, x87, C arithmetic or trap-representation interpretation is added. -/
inductive Value where
  | boolean (value : Bool)
  | integer (value : Int)
  | floating (bits : Nat)
  | pointer (value : Pointer)
  | array (values : List Value)
  | structure (members : List Value)
  | union (active : Nat) (value : Value)
  | enumeration (value : Value)
  | complex (real imaginary : Value)
  | vector (lanes : List Value)
  | atomic (value : Value)
  /-- Unnamed and zero-width bitfields have no C value. -/
  | padding
  deriving Repr

inductive ScalarTyped : Scalar → Value → Prop where
  | boolean (value : Bool) : ScalarTyped .boolean (.boolean value)
  | integer (kind : IntegerKind) (signedness : Signedness) (value : Int)
      (range : IntegerRange signedness (8 * kind.bytes) value) :
      ScalarTyped (.integer kind signedness) (.integer value)
  | bitInt (precision : Nat) (signedness : Signedness) (value : Int)
      (valid : ScalarValid (.bitInt precision signedness))
      (range : IntegerRange signedness precision value) :
      ScalarTyped (.bitInt precision signedness) (.integer value)
  | floating (format : Floating) (bits : Nat)
      (bound : bits < 2 ^ format.layout.valueBits) :
      ScalarTyped (.floating format) (.floating bits)

/-- Allocation identities are independent of machine addresses. The extent and
liveness describe representable pointer values, including one-past pointers;
they do not grant dereference, ownership, alignment or aliasing permissions. -/
structure Allocation where
  extent : Nat
  live : Bool
  deriving DecidableEq, Repr

structure Environment where
  types : NativeTypes.Environment
  allocations : Nat → Option Allocation := fun _ => none
  functions : String → Option CType := fun _ => none

def ArrayElementShape : CType → Prop
  | .void | .function .. | .array _ none => False
  | .qualified _ type => ArrayElementShape type
  | _ => True

def FunctionResultShape : CType → Prop
  | .array .. | .function .. => False
  | .qualified _ type => FunctionResultShape type
  | _ => True

/-- Prototypes use their adjusted parameter types; array/function parameters
must already have become pointers, and a sole void parameter becomes `[]`. -/
def FunctionParameterShape : CType → Prop
  | .void | .array .. | .function .. => False
  | .qualified _ type => FunctionParameterShape type
  | _ => True


def AtomicUnderlying : CType → Prop
  | .void | .function .. | .array .. | .atomic _ | .qualified .. => False
  | _ => True

/-- Declaration syntax admitted behind pointers. Named incomplete records are
allowed here; complete by-value objects use `WellFormed` below. -/
inductive Declared : CType → Prop where
  | void : Declared .void
  | scalar {scalar : Scalar} (valid : ScalarValid scalar) : Declared (.scalar scalar)
  | pointer {type : CType} (pointee : Declared type) : Declared (.pointer type)
  | array {type : CType} {arrayCount : Option Nat}
      (element : Declared type) (allowed : ArrayElementShape type)
      (nonzero : ∀ count, arrayCount = some count → 0 < count) : Declared (.array type arrayCount)
  | record (kind : AggregateKind) (tag : Nat) : Declared (.record kind tag)
  | enumeration (tag : Nat) : Declared (.enumeration tag)
  | complex (format : Floating) : Declared (.complex format)
  | vector {lane : Scalar} {lanes : Nat} (valid : ScalarValid lane) (nonzero : 0 < lanes) :
      Declared (.vector lane lanes)
  | atomic {type : CType} (underlying : Declared type) (allowed : AtomicUnderlying type) :
      Declared (.atomic type)
  | qualified {type : CType} {qualifiers : Silmaril.Cerberus.Qualifiers}
      (underlying : Declared type)
      (restrict : qualifiers.restrict = true → ∃ pointee, type = .pointer pointee) :
      Declared (.qualified qualifiers type)
  | function {result : CType} {parameters : List CType} {variadic : Bool}
      (resultDeclared : Declared result)
      (resultAllowed : FunctionResultShape result)
      (parametersDeclared : ∀ type ∈ parameters, Declared type)
      (parametersAllowed : ∀ type ∈ parameters, FunctionParameterShape type) :
      Declared (.function result parameters variadic)

def ObjectPointee : CType → Prop
  | .function .. => False
  | .qualified _ type => ObjectPointee type
  | _ => True


inductive PointerTyped (environment : Environment) : CType → Pointer → Prop where
  | null {pointee : CType} (declared : Declared pointee) : PointerTyped environment pointee .null
  | object {pointee : CType} {identity : Nat} {allocation : Allocation} {offset : Int}
      (declared : Declared pointee) (objectType : ObjectPointee pointee)
      (allocated : environment.allocations identity = some allocation)
      (live : allocation.live = true) (lower : 0 ≤ offset)
      (upper : offset ≤ (allocation.extent : Int)) :
      PointerTyped environment pointee (.object identity offset)
  | function {result : CType} {parameters : List CType} {variadic : Bool} {symbol : String}
      (declared : Declared (.function result parameters variadic))
      (registered : environment.functions symbol = some (.function result parameters variadic)) :
      PointerTyped environment (.function result parameters variadic) (.function symbol)

def Member.name : Member → Option String
  | .field name .. => some name
  | .bitField name .. => name

def Member.selectable : Member → Prop
  | .field .. => True
  | .bitField name _ width => name.isSome = true ∧ 0 < width

def RecordShape (record : Record) : Prop :=
  (record.members.filterMap Member.name).Nodup ∧
  (∀ align, record.alignment = some align → 0 < align ∧ align &&& (align - 1) = 0) ∧
  (record.flexible.isSome = true → record.kind = .struct ∧
    record.members.filterMap Member.name ≠ [])


mutual
  /-- Complete native object typing, independent of ABI classification, a byte
  encoding, machine state, compiler acceptance and any target record offsets. -/
  inductive WellFormed (types : NativeTypes.Environment) : CType → Prop where
    | scalar {scalar : Scalar} (valid : ScalarValid scalar) : WellFormed types (.scalar scalar)
    | pointer {pointee : CType} (declared : Declared pointee) : WellFormed types (.pointer pointee)
    | array {type : CType} {count : Nat} (element : WellFormed types type) (nonzero : 0 < count) :
        WellFormed types (.array type (some count))
    | record {tag : Nat} {record : Record} {kind : AggregateKind}
        (registered : types.records tag = some record) (kindMatches : record.kind = kind)
        (shape : RecordShape record)
        (members : ∀ member ∈ record.members, MemberWellFormed types member)
        (flexible : ∀ type, record.flexible = some type → WellFormed types type) :
        WellFormed types (.record kind tag)
    | enumeration {tag : Nat} {scalar : Scalar} (registered : types.enums tag = some scalar)
        (integral : Integral scalar) (valid : ScalarValid scalar) :
        WellFormed types (.enumeration tag)
    | complex (format : Floating) : WellFormed types (.complex format)
    | vector {scalar : Scalar} {lanes : Nat} (valid : ScalarValid scalar) (nonzero : 0 < lanes) :
        WellFormed types (.vector scalar lanes)
    | atomic {type : CType} (underlying : WellFormed types type) (allowed : AtomicUnderlying type) :
        WellFormed types (.atomic type)
    | qualified {type : CType} {qualifiers : Silmaril.Cerberus.Qualifiers}
        (underlying : WellFormed types type)
        (restrict : qualifiers.restrict = true → ∃ pointee, type = .pointer pointee) :
        WellFormed types (.qualified qualifiers type)
  inductive MemberWellFormed (types : NativeTypes.Environment) : Member → Prop where
    | field {type : CType} {declared : Option Nat} {fieldName : String}
        (typed : WellFormed types type)
        (alignment : ∀ align, declared = some align → 0 < align ∧ align &&& (align - 1) = 0) :
        MemberWellFormed types (.field fieldName type declared)
    | bitField {scalar : Scalar} {width : Nat} {name : Option String}
        (valid : ScalarValid scalar) (integral : Integral scalar)
        (fits : width ≤ ScalarWidth scalar) (zero : width = 0 → name = none) :
        MemberWellFormed types (.bitField name scalar width)
end


inductive BitFieldTyped : Option String → Scalar → Nat → Value → Prop where
  | unnamed {scalar : Scalar} {width : Nat} : BitFieldTyped none scalar width .padding
  | boolean {fieldName : String} (value : Bool) : BitFieldTyped (some fieldName) .boolean 1 (.boolean value)
  | integer {signedness : Signedness} {width : Nat} {integer : Int}
      {fieldName : String} {integerKind : IntegerKind}
      (range : IntegerRange signedness width integer) (nonzero : 0 < width) :
      BitFieldTyped (some fieldName) (.integer integerKind signedness) width (.integer integer)
  | bitInt {signedness : Signedness} {width : Nat} {integer : Int}
      {fieldName : String} {precision : Nat}
      (range : IntegerRange signedness width integer) (nonzero : 0 < width) :
      BitFieldTyped (some fieldName) (.bitInt precision signedness) width (.integer integer)


mutual
  inductive HasType (environment : Environment) : CType → Value → Prop where
    | scalar {scalar : Scalar} {value : Value} (typed : ScalarTyped scalar value) : HasType environment (.scalar scalar) value
    | pointer {pointee : CType} {pointer : Pointer} (typed : PointerTyped environment pointee pointer) :
        HasType environment (.pointer pointee) (.pointer pointer)
    | array {values : List Value} {count : Nat} {element : CType} (length : values.length = count)
        (typed : ∀ value ∈ values, HasType environment element value) :
        HasType environment (.array element (some count)) (.array values)
    | structure {tag : Nat} {record : Record} {values : List Value}
        (registered : environment.types.records tag = some record)
        (kind : record.kind = .struct) (typed : MembersTyped environment record.members values) :
        HasType environment (.record .struct tag) (.structure values)
    | union {tag active : Nat} {record : Record} {member : Member} {value : Value}
        (registered : environment.types.records tag = some record)
        (kind : record.kind = .union) (selected : record.members[active]? = some member)
        (selectable : Member.selectable member) (typed : MemberTyped environment member value) :
        HasType environment (.record .union tag) (.union active value)
    | enumeration {tag : Nat} {scalar : Scalar} {value : Value}
        (registered : environment.types.enums tag = some scalar)
        (typed : ScalarTyped scalar value) :
        HasType environment (.enumeration tag) (.enumeration value)
    | complex {format : Floating} {real imaginary : Value}
        (realTyped : ScalarTyped (.floating format) real)
        (imaginaryTyped : ScalarTyped (.floating format) imaginary) :
        HasType environment (.complex format) (.complex real imaginary)
    | vector {values : List Value} {lanes : Nat} {scalar : Scalar} (length : values.length = lanes)
        (typed : ∀ value ∈ values, ScalarTyped scalar value) :
        HasType environment (.vector scalar lanes) (.vector values)
    | atomic {type : CType} {value : Value} (typed : HasType environment type value) :
        HasType environment (.atomic type) (.atomic value)
    | qualified {type : CType} {value : Value} {qualifiers : Silmaril.Cerberus.Qualifiers}
        (typed : HasType environment type value) :
        HasType environment (.qualified qualifiers type) value
  inductive MemberTyped (environment : Environment) : Member → Value → Prop where
    | field {type : CType} {value : Value} {fieldName : String} {alignment : Option Nat}
        (typed : HasType environment type value) :
        MemberTyped environment (.field fieldName type alignment) value
    | bitField {name : Option String} {scalar : Scalar} {width : Nat} {value : Value}
        (typed : BitFieldTyped name scalar width value) :
        MemberTyped environment (.bitField name scalar width) value
  inductive MembersTyped (environment : Environment) : List Member → List Value → Prop where
    | nil : MembersTyped environment [] []
    | cons {member : Member} {value : Value} {members : List Member} {values : List Value}
        (head : MemberTyped environment member value)
        (tail : MembersTyped environment members values) :
        MembersTyped environment (member :: members) (value :: values)
end

/-- This carrier can be constructed before choosing any ABI target or encoding.
There is deliberately no successful-classification or compiler premise. -/
structure TypedValue (environment : Environment) (type : CType) where
  value : Value
  wellFormed : WellFormed environment.types type
  hasType : HasType environment type value

end Silmaril.Cerberus.NativeValues
