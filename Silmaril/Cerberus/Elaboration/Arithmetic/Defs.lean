module

public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.Runtime.Defs

/-! Scalar add/sub/mul equations from pinned `translation.lem:61-74,
271-327,1416-1479,2025-2081,2124-2179`. Operand computations are inputs so
recursive dispatch stays separate and source allocation order is explicit.
CHERI and pointer arithmetic reject. The source's differing direct/runtime
conversions, unused fifth symbol and subtraction standard-tag typo remain. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Arithmetic
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- The source predicates inspect only direct basic types. -/
def integerType : Ctype → Option IntegerType
  | .mk _ (.basic (.integer type)) => some type
  | _ => none

def floatingType : Ctype → Bool
  | .mk _ (.basic (.floating _)) => true
  | _ => false

def scalarObjectType : Ctype → Except String ObjectType
  | .mk _ (.basic (.integer _)) => .ok .integer
  | .mk _ (.basic (.floating _)) => .ok .floating
  | _ => .error "unsupported: arithmetic operands must have direct scalar arithmetic types"

def promoteType (config : Target.Config) (env : Target.Environment) :
    Ctype → Except String (Ctype × IntegerType)
  | .mk annotations (.basic (.integer type)) => do
      let promoted ← Constants.targetResult (GeneralizedTypes.promote config env type)
      return (.mk annotations (.basic (.integer promoted)), promoted)
  | _ => .error "Translation.usual_arithmetic_conversion: not (integer vs integer)"

/-- Add alone selects `PEconv_int`; mul/sub use named runtime `conv_int`. -/
def convert (bindings : List Runtime.Binding) (direct : Bool)
    (type : IntegerType) (value : Pure) : Except String Pure :=
  if direct then .ok (convertInteger type value)
  else Runtime.standardCall bindings "conv_int" [ailCtype (.mk [] (.basic (.integer type))), value]

def convertPair (bindings : List Runtime.Binding) (direct : Bool)
    (type : IntegerType) (left right : Pure) : Except String (Pure × Pure) := do
  return (← convert bindings direct type left, ← convert bindings direct type right)

/-- Actual value conversion algorithm, including dynamic representability
branches. It is distinct from the generalized type interpreter's result type. -/
def usualArithmetic (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (direct : Bool)
    (leftType rightType : Ctype) (left right : Pure) : Except String (Pure × Pure) := do
  if config.cheri then throw "unsupported: CHERI arithmetic conversion"
  match floatingType leftType, floatingType rightType with
  | true, true => return (left, right)
  | true, false => return (left, .mk [] () (.ctor .fvFromInt [right]))
  | false, true => return (.mk [] () (.ctor .fvFromInt [left]), right)
  | false, false =>
      let (promotedLeft, first) ← promoteType config env leftType
      let (promotedRight, second) ← promoteType config env rightType
      if Target.integerEqual first second then return ← convertPair bindings direct first left right
      let signedFirst ← Constants.targetResult (Target.signedness config env first)
      let signedSecond ← Constants.targetResult (Target.signedness config env second)
      if signedFirst = signedSecond then
        let type := if GeneralizedTypes.ltIntegerRank first second then second else first
        return ← convertPair bindings direct type left right
      else if !signedFirst && GeneralizedTypes.leIntegerRank second first then
        return ← convertPair bindings direct first left right
      else if !signedSecond && GeneralizedTypes.leIntegerRank first second then
        return ← convertPair bindings direct second left right
      else
        let (source, destination, signedType) :=
          if signedFirst then (promotedRight, promotedLeft, first)
          else (promotedLeft, promotedRight, second)
        let condition ← Runtime.standardCall bindings "all_values_representable_in"
          [ailCtype source, ailCtype destination]
        let unsignedType := GeneralizedTypes.correspondingUnsigned signedType
        let yes ← convertPair bindings direct signedType left right
        let no ← convertPair bindings direct unsignedType left right
        return (ifPure condition yes.1 no.1, ifPure condition yes.2 no.2)

def withIntegerBehavior (config : Target.Config) (env : Target.Environment)
    (resultType : Ctype) (operator : IntOp) (left right defaultValue : Pure) : Except String Pure := do
  match integerType resultType with
  | some type =>
      if ← Constants.targetResult (Target.signedness config env type) then
        return catchExceptionalCondition type operator left right
      else return wrapInteger type operator left right
  | none => return defaultValue

/-- The source allocates `cap` even when the non-CHERI branch never uses it. -/
structure Operands where
  left : State.WrappedSymbol
  right : State.WrappedSymbol
  leftObject : State.WrappedSymbol
  rightObject : State.WrappedSymbol
  cap : State.WrappedSymbol

def freshOperands (leftType rightType : ObjectType) : State.ElabM Operands := do
  let left ← State.wrappedFreshSymbol (.loaded leftType)
  let right ← State.wrappedFreshSymbol (.loaded rightType)
  let leftObject ← State.wrappedFreshSymbol (.object leftType)
  let rightObject ← State.wrappedFreshSymbol (.object rightType)
  let cap ← State.wrappedFreshSymbol (.object .integer)
  return ⟨left, right, leftObject, rightObject, cap⟩

/-- Metadata of only the three supported existing Ail operators. -/
def operatorData : ArithmeticOperator → Except String (BinOp × IntOp × String × String × String × String)
  | .add => .ok (.add, .add, "§6.5.6", "§6.5.6#4", "§6.5.6#5", "§6.5.6#5")
  | .sub => .ok (.sub, .sub, "§6.5.6", "§6.5.6#4", "§6.5.6#6", "§6.5.5#6")
  | .mul => .ok (.mul, .mul, "§6.5.5", "§6.5.5#3", "§6.5.5#4", "§6.5.5#4")
  | _ => .error "unsupported: arithmetic operator is outside add/sub/mul"

def finish (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (location : Loc) (resultType leftType rightType : Ctype) (operator : ArithmeticOperator)
    (operands : Operands) (left right : Effect) : Except String Effect := do
  let (binary, integerOperator, standard, conversionStandard, operationStandard, wrapperStandard) ←
    operatorData operator
  let objectLeft ← scalarObjectType leftType
  let objectRight ← scalarObjectType rightType
  let promoted ← usualArithmetic config env bindings (decide (operator = .add))
    leftType rightType operands.leftObject.expression operands.rightObject.expression
  let (promotedLeft, promotedRight) := standardPair conversionStandard promoted
  let rawOperation := standardPure operationStandard (operation binary promotedLeft promotedRight)
  let checked ← withIntegerBehavior config env resultType integerOperator promotedLeft promotedRight rawOperation
  let specifiedResult := specified (standardPure wrapperStandard checked)
  let signed ← match integerType resultType with
    | some type => Constants.targetResult (Target.signedness config env type)
    | none => .ok false
  let exceptional := standardUndefined location "§6.5#5" .UB036_exceptional_condition
  let unspecifiedResult :=
    if operator = .sub then
      if signed then exceptional else unspecified resultType
    else
      if !signed && (integerType resultType).isSome then unspecified resultType else exceptional
  let pattern ← tuplePattern [operands.left.pattern, operands.right.pattern]
  let values ← tuplePure [operands.left.expression, operands.right.expression]
  let specifiedPattern ← tuplePattern
    [Construction.specifiedPattern operands.leftObject.pattern,
     Construction.specifiedPattern operands.rightObject.pattern]
  return addStandard standard (weakSequence pattern (unseq [left, right])
    (pureEffect (casePure values
      [(specifiedPattern, specifiedResult),
       (wildcard (.tuple [.loaded objectLeft, .loaded objectRight]), unspecifiedResult)])))

/-- Successful paths retain each source branch's actual fresh-symbol order.
Monadic operand inputs are executed once, in left-to-right source order. -/
def translate (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (location : Loc) (resultType leftType rightType : Ctype) (operator : ArithmeticOperator)
    (left right : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI arithmetic")
  let _ ← Constants.liftResult (operatorData operator)
  let objectLeft ← Constants.liftResult (scalarObjectType leftType)
  let objectRight ← Constants.liftResult (scalarObjectType rightType)
  let (operands, coreLeft, coreRight) ←
    if operator = .add then do
      let operands ← freshOperands objectLeft objectRight
      let coreLeft ← left
      let coreRight ← right
      pure (operands, coreLeft, coreRight)
    else do
      let coreLeft ← left
      let coreRight ← right
      let operands ← freshOperands objectLeft objectRight
      pure (operands, coreLeft, coreRight)
  Constants.liftResult (finish config env bindings location resultType leftType rightType operator
    operands coreLeft coreRight)

end Silmaril.Cerberus.Elaboration.Arithmetic
