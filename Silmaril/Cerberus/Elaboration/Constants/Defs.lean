module

public import Silmaril.Cerberus.GeneralizedTypes.Defs
public import Silmaril.Cerberus.Elaboration.State.Defs

/-! Actual constant translation from pinned `translation.lem:191-227`, its
constant-expression dispatch/annotations and the no-temporary `bound` wrapper.
Concrete integer extrema follow `memory/concrete/impl_mem.ml`, whose special
typedef cases differ from the frontend's generic range helper. Floating text
rejects until OCaml `float_of_string` correspondence is supplied. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Constants
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

def targetResult {α : Type} (result : Except Target.Error α) : Except String α :=
  result.mapError reprStr

def resolveConcreteEnum (_config : Target.Config) (env : Target.Environment)
    (type : IntegerType) : Except String IntegerType :=
  match type with
  | .enum symbol => targetResult (Target.lookupEnum env symbol)
  | type => .ok type

/-- `Impl_mem.max_ival`, including its unsigned wchar and eight-bit Bool cases.
The wire integer model carries an Int, not a symbolic max/min constructor. -/
def concreteMaximum (config : Target.Config) (env : Target.Environment)
    (type : IntegerType) : Except String Int := do
  let type ← resolveConcreteEnum config env type
  let layout ← targetResult (Target.integerLayout config env type)
  if layout.size = 0 then throw "concrete maximum requires a nonzero scalar size"
  let signed ← match type with
    | .char => .ok config.plainCharSigned
    | .bool | .size | .wchar | .unsigned _ | .ptraddr => .ok false
    | .ptrdiff | .wint | .signed _ => .ok true
    | .enum _ => .error "concrete maximum: unresolved enum"
  return (2 : Int) ^ (8 * layout.size - if signed then 1 else 0) - 1

/-- `Impl_mem.min_ival`: char uses a fixed eight bits; wchar and wint minima
are zero even though frontend signedness reports them as signed. -/
def concreteMinimum (config : Target.Config) (env : Target.Environment)
    (type : IntegerType) : Except String Int := do
  let type ← resolveConcreteEnum config env type
  match type with
  | .char => return if config.plainCharSigned then -128 else 0
  | .bool | .size | .wchar | .wint | .unsigned _ | .ptraddr => return 0
  | .ptrdiff | .signed _ =>
      let layout ← targetResult (Target.integerLayout config env type)
      if layout.size = 0 then throw "concrete minimum requires a nonzero scalar size"
      return -((2 : Int) ^ (8 * layout.size - 1))
  | .enum _ => throw "concrete minimum: unresolved enum"

def loadedInteger (value : Int) : Pure := valuePure (.loaded (.specified (.integer value)))

def hexDigit (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte ≤ 57 then some (byte - 48)
  else if 65 ≤ byte ∧ byte ≤ 70 then some (byte - 55)
  else if 97 ≤ byte ∧ byte ≤ 102 then some (byte - 87)
  else none

/-- Upstream accepts digit8 in the octal escape check; preserve that source
behavior rather than silently repairing the parser. -/
def octalDigit (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte ≤ 56 then some (byte - 48) else none

def decodeDigits (base : Nat) (digit : Nat → Option Nat) (bytes : List Nat) : Except String Nat :=
  match bytes with
  | [] => .error "empty character escape"
  | _ => bytes.foldlM (fun value byte => match digit byte with
      | some n => .ok (base * value + n)
      | none => .error "invalid character escape digit") 0

/-- The ASCII table and escape cases of `Decode.decode_character_constant_aux`.
Raw bytes are interpreted as OCaml bytes, without a Unicode fallback. -/
def decodeCharacterAux : List Nat → Except String Nat
  | [byte] =>
      if (32 ≤ byte ∧ byte ≤ 126 ∧ byte ≠ 92) ∨ byte = 9 then .ok byte
      else .error "invalid plain character constant"
  | [92, 34] => .ok 34
  | [92, 39] => .ok 39
  | [92, 92] => .ok 92
  | [92, 97] => .ok 7
  | [92, 98] => .ok 8
  | [92, 102] => .ok 12
  | [92, 110] => .ok 10
  | [92, 114] => .ok 13
  | [92, 116] => .ok 9
  | [92, 118] => .ok 11
  | 92 :: 120 :: digits => decodeDigits 16 hexDigit digits
  | 92 :: digits => decodeDigits 8 octalDigit digits
  | _ => .error "invalid character constant"

def rawBytes : Cabs.RawString → List Nat
  | .utf8 text => text.toUTF8.data.toList.map UInt8.toNat
  | .bytes bytes => bytes.data.toList.map UInt8.toNat

/-- The decoder ignores prefixes upstream and wraps using eight-bit char
signedness, independently of the selected layout's char size. -/
def decodeCharacter (config : Target.Config) (raw : Cabs.RawString) : Except String Int := do
  let value ← decodeCharacterAux (rawBytes raw)
  let remainder := value % 256
  return if config.plainCharSigned && decide (127 < remainder) then
    (remainder : Int) - 256 else remainder

def translateConstant (config : Target.Config) (env : Target.Environment) :
    Ail.Constant → Except String Pure
  | .indeterminate type => .ok (unspecified type)
  | .null => .ok (specified (nullptr (.mk [] .void)))
  | .integer (.iconstant value _ _) => .ok (loadedInteger value)
  | .integer (.max type) => return loadedInteger (← concreteMaximum config env type)
  | .integer (.min type) => return loadedInteger (← concreteMinimum config env type)
  | .floating _ => .error "unsupported: exact OCaml float_of_string translation is not ported"
  | .character (_, raw) => return loadedInteger (← decodeCharacter config raw)
  | .array _ constants => do
      let values ← constants.attach.mapM fun constant => translateConstant config env constant.val
      return specified (array values)
  | .struct tag members => do
      let values ← members.attach.mapM fun member => do
        return (member.val.1, ← translateConstant config env member.val.2)
      return specified (structPure tag values)
  | .union tag member value => return specified (unionPure tag member (← translateConstant config env value))
  | .predefined .false_ => .ok (loadedInteger 0)
  | .predefined .true_ => .ok (loadedInteger 1)
termination_by constant => sizeOf constant
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | have h := List.sizeOf_lt_of_mem constant.property
      omega
    | have h := List.sizeOf_lt_of_mem member.property
      rcases member with ⟨⟨identifier, value⟩, membership⟩
      simp_all
      omega

def marker : List Annot → Except String (Option Nat)
  | [] => .ok none
  | .marker id :: rest => do
      match ← marker rest with
      | none => return some id
      | some _ => throw "found more than one marker"
  | _ :: rest => marker rest

def constantIsNullPointer : Ail.Constant → Bool
  | .null => true
  | .integer (.iconstant value _ _) => decide (value = 0)
  | _ => false

def isPointer : Ctype → Bool
  | .mk _ (.pointer _ _) => true
  | _ => false

def annotateIntegerEffect : Ctype → Effect → Effect
  | .mk _ (.basic (.integer type)), .mk annotations node =>
      .mk (.value (.integer type) :: annotations) node
  | _, expression => expression

def liftResult {α : Type} : Except String α → State.ElabM α
  | .ok value => pure value
  | .error message => throw (.message message)

/-- Exact constant branch, including source marker consumption. Existing Ail
annotations are inspected for marker effects; the constant branch itself does
not attach the computed std_annots list upstream. Null fast paths bypass both. -/
def expression (config : Target.Config) (env : Target.Environment) :
    Ail.TypedExpression → State.ElabM Effect
  | input@(.mk category annotations location (.const constant)) => do
      let type ← liftResult (targetResult (GeneralizedTypes.expressionType config env input))
      if isPointer type && constantIsNullPointer constant then
        return pureEffect (specified (nullptr type))
      match ← liftResult (marker annotations) with
      | some _ => let _ ← State.recordObjectTypesMarker; pure ()
      | none => pure ()
      let core ← liftResult (translateConstant config env constant)
      let effect := pureEffect core
      let annotated := match category with
        | .lvalue .. => effect
        | .rvalue _ => annotateIntegerEffect type effect
      return addLocation location (addExpression annotated)
  | _ => throw (.message "unsupported: only actual Ail constant expressions are translated")

/-- Constants create no temporary objects. Preserve `track_temporary_objects`
and the exact source `[Astd §6.5#2] Ebound` constructor anyway. -/
def wrappedExpression (config : Target.Config) (env : Target.Environment)
    (input : Ail.TypedExpression) : State.ElabM Effect := do
  let (temporaries, core) ← State.trackTemporaryObjects (expression config env input)
  match temporaries with
  | [] => return .mk [.std "§6.5#2"] (.bound core)
  | _ => throw (.message "unsupported: constant expression unexpectedly created temporary objects")

end Silmaril.Cerberus.Elaboration.Constants
