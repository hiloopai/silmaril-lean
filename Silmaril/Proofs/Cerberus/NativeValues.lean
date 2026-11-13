module

public import Silmaril.Cerberus.NativeValues.Defs

@[expose] public section
namespace Silmaril.Cerberus.NativeValues

open NativeTypes

theorem ScalarTyped.valid {scalar : Scalar} {value : Value}
    (typed : ScalarTyped scalar value) : ScalarValid scalar := by
  cases typed with
  | boolean => exact ⟨_, rfl⟩
  | integer => exact ⟨_, rfl⟩
  | bitInt _ _ _ valid _ => exact valid
  | floating => exact ⟨_, rfl⟩

theorem WellFormed.not_void (types : NativeTypes.Environment) :
    ¬ WellFormed types .void := by
  intro typed
  cases typed

theorem WellFormed.not_function (types : NativeTypes.Environment) (result : CType)
    (parameters : List CType) (variadic : Bool) :
    ¬ WellFormed types (.function result parameters variadic) := by
  intro typed
  cases typed

theorem WellFormed.not_incomplete_array (types : NativeTypes.Environment) (element : CType) :
    ¬ WellFormed types (.array element none) := by
  intro typed
  cases typed

theorem WellFormed.array_nonzero {types : NativeTypes.Environment} {element : CType} {count : Nat}
    (typed : WellFormed types (.array element (some count))) : 0 < count := by
  cases typed with
  | array _ nonzero => exact nonzero

theorem MembersTyped.length {environment : Environment} {members : List Member} {values : List Value}
    (typed : MembersTyped environment members values) : members.length = values.length := by
  cases typed with
  | nil => rfl
  | cons _ tail => exact congrArg Nat.succ (MembersTyped.length tail)
termination_by members.length

theorem HasType.array_length {environment : Environment} {element : CType} {count : Nat}
    {values : List Value} (typed : HasType environment (.array element (some count)) (.array values)) :
    values.length = count := by
  cases typed with
  | array length _ => exact length

theorem HasType.union_selected {environment : Environment} {tag active : Nat} {value : Value}
    (typed : HasType environment (.record .union tag) (.union active value)) :
    ∃ record member, environment.types.records tag = some record ∧ record.kind = .union ∧
      record.members[active]? = some member ∧ Member.selectable member ∧
      MemberTyped environment member value := by
  cases typed with
  | union registered kind selected selectable memberTyped =>
      exact ⟨_, _, registered, kind, selected, selectable, memberTyped⟩

/-- The source type derivation is available without choosing any ABI classifier,
object layout, byte representation, compiler or successful execution. -/
theorem TypedValue.type_derivation {environment : Environment} {type : CType}
    (value : TypedValue environment type) :
    WellFormed environment.types type ∧ HasType environment type value.value :=
  ⟨value.wellFormed, value.hasType⟩

theorem TypedValue.ext {environment : Environment} {type : CType}
    {first second : TypedValue environment type} (same : first.value = second.value) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

theorem ScalarTyped.integer_range {kind : IntegerKind} {signedness : Signedness} {value : Int}
    (typed : ScalarTyped (.integer kind signedness) (.integer value)) :
    IntegerRange signedness (8 * kind.bytes) value := by
  cases typed with
  | integer _ _ _ range => exact range

theorem ScalarTyped.bitInt_range {precision : Nat} {signedness : Signedness} {value : Int}
    (typed : ScalarTyped (.bitInt precision signedness) (.integer value)) :
    ScalarValid (.bitInt precision signedness) ∧ IntegerRange signedness precision value := by
  cases typed with
  | bitInt _ _ _ valid range => exact ⟨valid, range⟩

end Silmaril.Cerberus.NativeValues
