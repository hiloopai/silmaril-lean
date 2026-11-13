module

public import Silmaril.Cerberus.Elaboration.MemoryActions.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.MemoryActions
open Silmaril.Cerberus
open Construction

/-- The complete annotated CType reaches the actual positive load action. -/
theorem load_type (location : Loc) (type : Ctype) (pointer : Pure) (order : MemoryOrder) :
    load location (ailCtype type) pointer order =
    .mk [] (.action (.mk .pos (.mk location () (.load (ailCtype type) pointer order)))) := rfl

theorem staticKill_type (location : Loc) (type : Ctype) (pointer : Pure) :
    staticKill location type pointer =
    .mk [] (.action (.mk .pos (.mk location () (.kill (.static type) pointer)))) := rfl

end Silmaril.Cerberus.Elaboration.MemoryActions
