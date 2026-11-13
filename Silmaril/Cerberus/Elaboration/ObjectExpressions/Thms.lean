module

public import Silmaril.Cerberus.Elaboration.ObjectExpressions.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ObjectExpressions
open Silmaril.Cerberus

/-- The source's atomic test is syntactic, rather than recursive unwrapping. -/
theorem atomic_load_order (annotations : List Annot) (type : Ctype) :
    loadOrder (.mk annotations (.atomic type)) = .seqCst := rfl

theorem integer_load_order (annotations : List Annot) (type : IntegerType) :
    loadOrder (.mk annotations (.basic (.integer type))) = .na := rfl

end Silmaril.Cerberus.Elaboration.ObjectExpressions
