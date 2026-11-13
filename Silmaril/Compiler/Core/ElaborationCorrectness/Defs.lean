module

public import Silmaril.Cerberus.Elaboration.Statements.Thms
public import Silmaril.Cerberus.Elaboration.Constants.Thms
public import Silmaril.Cerberus.Elaboration.Freshness.Thms
public import Silmaril.Compiler.Core.ElaborationSemantics.Thms

/-! Actual typed-Ail syntax constructors for the first local elaboration
correctness result. These return the existing Ail syntax, not a second source
language or a substitute semantics. This separate verification workflow covers
an explicitly annotated signed-int literal without marker annotations.
-/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationCorrectness
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

def integerLiteral (location : Loc) (number : Int) (basis : Ail.Basis)
    (suffix : Option Ail.IntegerSuffix) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] location
    (.const (.integer (.iconstant number basis suffix)))

def returnLiteral (statementLocation expressionLocation : Loc) (desugaring : Ail.DesugInfo)
    (attributes : Attributes) (number : Int) (basis : Ail.Basis)
    (suffix : Option Ail.IntegerSuffix) : Ail.TypedStatement :=
  .mk statementLocation desugaring attributes
    (.return_ (integerLiteral expressionLocation number basis suffix))

/-- Actual Core syntax characterized by `returnLiteral_run`. It is an output
description, never a premise replacing successful source translation. -/
def returnCore (temporary label conversion : Sym) (statementLocation expressionLocation : Loc)
    (attributes : Attributes) (returnAnnotations : List Annot) (number : Int) : Effect :=
  addLocation statementLocation (addStatement (addAttributes attributes
    (strongSequence (symbolPattern temporary (.loaded .integer))
      (.mk [.std "§6.5#2"] (.bound
        (.mk [.loc expressionLocation, .expr, .value (.integer (.signed .int))]
          (.pure (Constants.loadedInteger number)))))
      (Construction.run label [call (.sym conversion)
        [ctype (.mk returnAnnotations (.basic (.integer (.signed .int)))), symbolPure temporary]]))))

end Silmaril.Compiler.Core.ElaborationCorrectness
