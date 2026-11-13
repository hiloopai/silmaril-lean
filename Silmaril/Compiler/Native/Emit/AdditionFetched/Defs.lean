module

public import Silmaril.Compiler.Native.Emit.AdditionFunction.Defs
public import Silmaril.X86.FetchTrace.Defs
/-! Canonical loaded-byte entry for the actual unoptimized addition function.
No step/run/decoder-success premise or assembler correspondence is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionFetched
open Silmaril Silmaril.X86

/-- The first 35 actual instructions retire; the last RET returns. -/
def retiringInstructions (left right : Word) : List Ext.Instr :=
  (AdditionFunction.instructions left right).take 35

structure Entry (caller : X86.MState) (left right exit : Word) : Prop where
  function : AdditionFunction.Entry caller exit
  loaded : Ext.Loaded caller.memory caller.core.rip (AdditionFunction.code left right)
  disjoint : Silmaril.X86.FetchTrace.Disjoint caller.core.rip (AdditionFunction.code left right)
    (AdditionFunction.footprint (caller.core.read .rsp))

end Silmaril.Compiler.Native.Emit.AdditionFetched
