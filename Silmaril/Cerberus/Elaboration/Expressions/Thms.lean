module

public import Silmaril.Cerberus.Elaboration.Expressions.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Expressions
open Silmaril.Cerberus
open Construction

/-- The dispatcher preserves the frozen constant port, including its null and
marker fast paths, without a second outer annotation pass. -/
theorem constant_dispatch (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (category : Ail.GenTypeCategory)
    (annotations : List Annot) (location : Loc) (constant : Ail.Constant) :
    expression config env bindings (.mk category annotations location (.const constant)) =
    Constants.expression config env (.mk category annotations location (.const constant)) := by
  unfold expression
  rfl

theorem integer_annotation_order (annotations : List Annot) (location : Loc)
    (type : IntegerType) (categoryType : Ail.GenType) (core : Effect) :
    annotate (.rvalue categoryType) location (.mk annotations (.basic (.integer type))) core =
    addLocation location (addExpression (Constants.annotateIntegerEffect
      (.mk annotations (.basic (.integer type))) core)) := rfl

end Silmaril.Cerberus.Elaboration.Expressions
