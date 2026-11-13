module

public import Silmaril.Compiler.Native.Analysis.Defs
@[expose] public section

namespace Silmaril.Compiler.Native.Analysis
open Silmaril.Cerberus Silmaril.Cerberus.Ail

variable {location : Loc} {desugaring : DesugInfo} {attributes : Attributes}

/-- The ordered scanner is compositional over a block's statement list. -/
theorem switchCases_block (bindings : Bindings) (statements : List TypedStatement)
    (accumulator : Array (Option (Int × Int))) :
    switchCases (.mk location desugaring attributes (.block bindings statements)) accumulator =
      statements.foldl (fun acc child => switchCases child acc) accumulator := by
  rw [switchCases]
  exact List.foldl_attach (f := fun acc child => switchCases child acc)

/-- Cases in a nested switch belong to that switch. -/
theorem switchCases_switch (condition : TypedExpression) (body : TypedStatement)
    (accumulator : Array (Option (Int × Int))) :
    switchCases (.mk location desugaring attributes (.switch condition body)) accumulator = accumulator := by
  simp [switchCases]

/-- A direct identifier address is included independently of the input set. -/
theorem addrTakenExpression_address {annotation operandAnnotation : GenTypeCategory}
    {annotations operandAnnotations : List Annot} {operandLocation : Loc} (symbol : Sym)
    (accumulator : Std.HashSet Nat) :
    addrTakenExpression (.mk annotation annotations location
      (.unary .address (.mk operandAnnotation operandAnnotations operandLocation (.ident symbol)))) accumulator =
        accumulator.insert symbol.number := by
  simp [addrTakenExpression]

/-- Address scans cross the statement-expression boundary through actual bodies. -/
theorem addrTakenExpression_gccStatement {annotation : GenTypeCategory} {annotations : List Annot}
    (bindings : Bindings) (statements : List TypedStatement) (accumulator : Std.HashSet Nat) :
    addrTakenExpression (.mk annotation annotations location (.gccStatement bindings statements)) accumulator =
      statements.foldl (fun acc child => addrTakenStatement child acc) accumulator := by
  rw [addrTakenExpression]
  exact List.foldl_attach (f := fun acc child => addrTakenStatement child acc)

end Silmaril.Compiler.Native.Analysis
