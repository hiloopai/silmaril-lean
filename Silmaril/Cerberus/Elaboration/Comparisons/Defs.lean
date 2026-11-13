module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs

/-! Actual scalar Gt and Eq branches from pinned `translation.lem:437-499,
546-587`. The helpers run supplied child computations in source order and
retain the distinct relational/equality allocation and case constructors.
Outer expression annotations/markers and eager construction scheduling belong
to the caller; this slice certifies neither arbitrary source callback staging
nor pointer-comparison branches. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Comparisons
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- The fifth Boolean is allocated even on the scalar nonpointer path. -/
structure Operands where
  left : State.WrappedSymbol
  right : State.WrappedSymbol
  leftObject : State.WrappedSymbol
  rightObject : State.WrappedSymbol
  comparison : State.WrappedSymbol

def freshOperands (leftType rightType : ObjectType) : State.ElabM Operands := do
  let left ← State.wrappedFreshSymbol (.loaded leftType)
  let right ← State.wrappedFreshSymbol (.loaded rightType)
  let leftObject ← State.wrappedFreshSymbol (.object leftType)
  let rightObject ← State.wrappedFreshSymbol (.object rightType)
  let comparison ← State.wrappedFreshSymbol .boolean
  return ⟨left, right, leftObject, rightObject, comparison⟩

def booleanInteger (condition : Pure) : Pure :=
  ifPure condition (specified (integer 1)) (specified (integer 0))

def specifiedPair (operands : Operands) : Except String Pat :=
  tuplePattern [specifiedPattern operands.leftObject.pattern, specifiedPattern operands.rightObject.pattern]

def loadedPair (operands : Operands) : Except String (Pat × Pure) := do
  return (← tuplePattern [operands.left.pattern, operands.right.pattern],
    ← tuplePure [operands.left.expression, operands.right.expression])

/-- Relational source uses an effectful case, with its specified branch's own
standard annotation and a pure unspecified fallback. -/
def finishGreater (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (resultType leftType rightType : Ctype) (operands : Operands)
    (left right : Effect) : Except String Effect := do
  let objectLeft ← Arithmetic.scalarObjectType leftType
  let objectRight ← Arithmetic.scalarObjectType rightType
  let promoted ← Arithmetic.usualArithmetic config env bindings false leftType rightType
    operands.leftObject.expression operands.rightObject.expression
  let (promotedLeft, promotedRight) := standardPair "§6.5.8#3" promoted
  let (pattern, values) ← loadedPair operands
  let specified ← specifiedPair operands
  return addStandard "§6.5.8" (weakSequence pattern (unseq [left, right])
    (caseEffect values
      [(specified, addStandard "§6.5.8#6" (pureEffect
        (booleanInteger (operation .gt promotedLeft promotedRight)))),
       (wildcard (.tuple [.loaded objectLeft, .loaded objectRight]), pureEffect (unspecified resultType))]))

/-- Equality source places a pure case inside Epure, and annotates its
specified branch and comparison condition separately. It has no outer scope tag. -/
def finishEqual (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (resultType leftType rightType : Ctype) (operands : Operands)
    (left right : Effect) : Except String Effect := do
  let objectLeft ← Arithmetic.scalarObjectType leftType
  let objectRight ← Arithmetic.scalarObjectType rightType
  let promoted ← Arithmetic.usualArithmetic config env bindings false leftType rightType
    operands.leftObject.expression operands.rightObject.expression
  let (promotedLeft, promotedRight) := standardPair "§6.5.9#4, sentence 1" promoted
  let (pattern, values) ← loadedPair operands
  let specified ← specifiedPair operands
  let condition := standardPure "§6.5.9#4, sentence 3" (operation .eq promotedLeft promotedRight)
  return weakSequence pattern (unseq [left, right]) (pureEffect (casePure values
    [(specified, standardPure "§6.5.9#3" (booleanInteger condition)),
     (wildcard (.tuple [.loaded objectLeft, .loaded objectRight]), unspecified resultType)]))

/-- Scalar Gt translates both children before allocating all five wrappers. -/
def greater (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (resultType leftType rightType : Ctype) (left right : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI relational comparison")
  let objectLeft ← Constants.liftResult (Arithmetic.scalarObjectType leftType)
  let objectRight ← Constants.liftResult (Arithmetic.scalarObjectType rightType)
  let coreLeft ← left
  let coreRight ← right
  let operands ← freshOperands objectLeft objectRight
  Constants.liftResult (finishGreater config env bindings resultType leftType rightType operands coreLeft coreRight)

/-- Scalar Eq allocates all five wrappers before translating either child. -/
def equal (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (resultType leftType rightType : Ctype) (left right : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI equality comparison")
  let objectLeft ← Constants.liftResult (Arithmetic.scalarObjectType leftType)
  let objectRight ← Constants.liftResult (Arithmetic.scalarObjectType rightType)
  let operands ← freshOperands objectLeft objectRight
  let coreLeft ← left
  let coreRight ← right
  Constants.liftResult (finishEqual config env bindings resultType leftType rightType operands coreLeft coreRight)

end Silmaril.Cerberus.Elaboration.Comparisons
