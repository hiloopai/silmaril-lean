module

public import Silmaril.Cerberus.Elaboration.Runtime.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Runtime
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

theorem firstMatching_head {α : Type} (predicate : α → Bool) (value : α) (rest : List α)
    (accepts : predicate value = true) : firstMatching predicate (value :: rest) = some value := by
  simp [firstMatching, accepts]

/-- A shadowing non-function rejects, even if a later function has the same name. -/
theorem standardCall_procedureDecl (symbol : Sym) (location : Loc) (type : BaseType)
    (parameters : List BaseType) (rest : List Binding) (name : String) (arguments : List Pure)
    (accepts : hasName name symbol = true) :
    standardCall ((symbol, .procedureDecl location type parameters) :: rest) name arguments =
      .error ("[Translate_effect.E.mk_stdcall] `" ++ name ++ "' is not a Core standard function.") := by
  simp [standardCall, firstMatching, accepts]

end Silmaril.Cerberus.Elaboration.Runtime
