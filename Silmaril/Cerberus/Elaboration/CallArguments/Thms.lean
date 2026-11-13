module

public import Silmaril.Cerberus.Elaboration.CallArguments.Defs

/-! Exact cleanup equations for the selected caller-owned temporary objects.
These describe generated Core syntax; concrete backend lifetime soundness and
call semantic preservation remain separate obligations. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.CallArguments
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

theorem cleanup_one (location : Loc) (type : Ctype) (pointer : Sym)
    (continuation : Effect) :
    cleanup location [type] [pointer] continuation =
      strongSequence (wildcard .unit)
        (MemoryActions.staticKill location type (symbolPure pointer)) continuation := rfl

theorem cleanup_pair (location : Loc) (firstType secondType : Ctype)
    (first second : Sym) (continuation : Effect) :
    cleanup location [firstType, secondType] [first, second] continuation =
      strongSequence (wildcard (.tuple [.unit, .unit]))
        (unseqEffect [MemoryActions.staticKill location firstType (symbolPure first),
          MemoryActions.staticKill location secondType (symbolPure second)]) continuation := rfl

end Silmaril.Cerberus.Elaboration.CallArguments
