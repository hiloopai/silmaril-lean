module

public import Silmaril.Cerberus.Elaboration.Expressions.Defs
public import Silmaril.Cerberus.Elaboration.LocalObjects.Defs

/-! Selected actual global-object equations from pinned Cerberus
`translation.lem:4222-4299`. Non-CHERI direct integer and selected null-pointer objects with empty
attributes are supported. External object
allocation still consumes the source's otherwise-unused fresh symbol.
Global-expression context differs only at identifiers upstream, which this
constant and integer-null cast domain excludes. Compound literals reject explicitly. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Globals
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

def integerType : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | _ => false

def constantExpression : Ail.TypedExpression → Bool
  | .mk _ _ _ (.const _) => true
  | _ => false

/-- Actual object branch. The source allocates the object binder before looking
up the initializer, then the result binder after wrapped initializer translation.
The wrapper's only outer annotation is `Astd`, hence its source `locOf` is unknown.
The supplied runtime conversion is retained even when source and destination
integer types coincide. No C typing, runtime or memory-backend correctness follows.
-/
def declaration (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (objects : List (Sym × Ail.TypedExpression))
    (symbol : Sym) (location : Loc) (attributes : Attributes)
    (alignment : Option Alignment) (qualifiers : Qualifiers) (type : Ctype) :
    State.ElabM (Global Codec.wireModel Unit Unit) := do
  if config.cheri then throw (.message "unsupported: CHERI global-object elaboration")
  unless integerType type || Constants.isPointer type do
    throw (.message "unsupported: global object is not a direct integer or pointer")
  let .mk [] := attributes
    | throw (.message "unsupported: global object attributes are not ported")
  let coreType := ailCtype type
  let coreCreate := MemoryActions.create location (LocalObjects.alignment type alignment)
    coreType (.source location [symbol])
  let pointer ← State.freshDescription .none
  match objects.find? (fun entry => decide (entry.1.key = symbol.key)) with
  | none => return .declaration (.object .pointer, type)
  | some (_, input) =>
      let (initializerType, core) ←
        if Constants.isPointer type && NullPointers.isNullPointerConstant input then
          pure (.loaded .pointer, pureEffect (specified (nullptr type)))
        else do
          unless constantExpression input ||
              (Constants.isPointer type && NullPointers.integerNullCast input) do
            throw (.message (if integerType type then
              "unsupported: global initializer is not a constant expression"
              else "unsupported: global initializer is outside constants and integer-null pointer casts"))
          let (_, compounds, core) ← State.withBlockObjects []
            (Expressions.wrappedExpression config types runtime input)
          unless compounds.isEmpty do
            throw (.message "unsupported: global compound literals are not ported")
          let sourceType ← Constants.liftResult
            (Constants.targetResult (GeneralizedTypes.expressionType config types input))
          let objectType ← match sourceType with
            | .mk _ (.basic (.integer _)) => pure ObjectType.integer
            | .mk _ (.pointer _ _) => pure ObjectType.pointer
            | _ => throw (.message "unsupported: global initializer is not a direct integer or pointer")
          if integerType type then
            unless integerType sourceType do
              throw (.message "unsupported: global constant initializer is not a direct integer")
          else
            unless Constants.isPointer sourceType do
              throw (.message "unsupported: global pointer initializer is not a pointer")
          pure (.loaded objectType, core)
      let result ← State.freshDescription .none
      let converted ← if integerType type then do
          let sourceType ← Constants.liftResult
            (Constants.targetResult (GeneralizedTypes.expressionType config types input))
          Constants.liftResult
            (Conversion.loadedArithmetic runtime sourceType type (symbolPure result))
        else pure (symbolPure result)
      return .definition (.object .pointer, type) (addLocation .unknown
        (strongSequence (symbolPattern pointer (.object .pointer)) coreCreate
          (strongSequence (symbolPattern result initializerType) core
            (strongSequence (wildcard .unit)
              (MemoryActions.store location qualifiers.const coreType (symbolPure pointer) converted .na)
              (pureEffect (symbolPure pointer))))))

end Silmaril.Cerberus.Elaboration.Globals
