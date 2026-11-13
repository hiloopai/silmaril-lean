module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs
public import Silmaril.Cerberus.Elaboration.ObjectExpressions.Defs
public import Silmaril.Cerberus.Elaboration.Comparisons.Defs
public import Silmaril.Cerberus.Elaboration.Designators.Defs
public import Silmaril.Cerberus.Elaboration.Calls.Defs
public import Silmaril.Cerberus.Elaboration.CallArguments.Defs
public import Silmaril.Cerberus.Elaboration.NullPointers.Defs
public import Silmaril.Cerberus.Elaboration.IntegerCasts.Defs

/-! Actual typed-Ail expression dispatcher for constants, object
identifiers/rvalues, scalar add/sub/mul, scalar gt/eq, direct integer casts, integer-zero pointer casts and normal fixed-integer direct calls.
The frozen constant port remains independently usable. Recursive effects,
marker freshness, full-expression bounds and annotation order are retained.
Other expression forms and expression-result lifetimes outside the call helper
reject explicitly. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Expressions
open Silmaril.Cerberus
open Construction

/-- Shared outer annotation order from `translation.lem:1500`.
The call branch attaches its computed standard annotations at `ccall`;
this outer wrapper does not attach that list to every expression form. -/
def annotate (category : Ail.GenTypeCategory) (location : Loc) (type : Ctype)
    (expression : Effect) : Effect :=
  let typed := match category with
    | .lvalue .. => expression
    | .rvalue _ => Constants.annotateIntegerEffect type expression
  addLocation location (addExpression typed)

def expression (config : Target.Config) (env : Target.Environment) (bindings : List Runtime.Binding)
    (input : Ail.TypedExpression) (aliases : Designators.Aliases := []) : State.ElabM Effect :=
  match input with
  | .mk _ _ _ (.const _) => Constants.expression config env input
  | .mk category annotations location node => do
      let type ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env input))
      if Constants.isPointer type && NullPointers.isNullPointerConstant input then
        return pureEffect (specified (nullptr type))
      let standardAnnotations ← match ← Constants.liftResult (Constants.marker annotations) with
        | some _ => do
            let marker ← State.recordObjectTypesMarker
            pure (.markerObjectTypes marker :: annotations)
        | none => pure annotations
      let core ← match _hnode : node with
        | .binary left operator right => do
            let leftType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env left))
            let rightType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env right))
            match operator with
            | .arithmetic arithmetic =>
                Arithmetic.translate config env bindings location type leftType rightType arithmetic
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .gt =>
                Comparisons.greater config env bindings type leftType rightType
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | .eq =>
                Comparisons.equal config env bindings type leftType rightType
                  (expression config env bindings left aliases) (expression config env bindings right aliases)
            | _ => throw (.message "unsupported: binary operator outside scalar add/sub/mul/gt/eq")
        | .cast _ destination operand => do
            let source ← Constants.liftResult
              (Constants.targetResult (GeneralizedTypes.expressionType config env operand))
            match destination with
            | .mk _ (.basic (.integer _)) =>
                IntegerCasts.translate config bindings source destination
                  (expression config env bindings operand aliases)
            | _ =>
                NullPointers.castInteger config source destination operand
                  (expression config env bindings operand aliases)
        | .ident symbol => ObjectExpressions.identifier config symbol
        | .rvalue child => do
            let childType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env child))
            ObjectExpressions.rvalue config location childType (expression config env bindings child aliases)
        | .functionDecay child => do
            let childType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env child))
            Designators.direct config aliases childType child
        | .call designator [] => do
            let designatorType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env designator))
            Calls.zeroArguments bindings location standardAnnotations designatorType
              (expression config env bindings designator aliases)
        | .call designator arguments => do
            let designatorType ← Constants.liftResult
              (Constants.targetResult (GeneralizedTypes.expressionType config env designator))
            let actuals ← arguments.attach.mapM fun argument => do
              let type ← Constants.liftResult
                (Constants.targetResult (GeneralizedTypes.expressionType config env argument.val))
              let .mk _ _ location _ := argument.val
              pure (CallArguments.Argument.mk location type
                (expression config env bindings argument.val aliases))
            CallArguments.translate config bindings location standardAnnotations designatorType
              (expression config env bindings designator aliases) actuals
        | _ => throw (.message "unsupported: actual expression form is outside constants, object rvalues, scalar operations and normal fixed-integer direct calls")
      return annotate category location type core
termination_by sizeOf input
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem argument.property
      omega

def wrappedExpression (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (input : Ail.TypedExpression)
    (aliases : Designators.Aliases := []) : State.ElabM Effect := do
  let (temporaries, core) ← State.trackTemporaryObjects (expression config env bindings input aliases)
  match temporaries with
  | [] => return .mk [.std "§6.5#2"] (.bound core)
  | _ => throw (.message "unsupported: expression temporary-object lifetimes are not ported")

end Silmaril.Cerberus.Elaboration.Expressions
