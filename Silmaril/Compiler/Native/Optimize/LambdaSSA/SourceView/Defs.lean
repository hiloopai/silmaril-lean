module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission.Defs
/-! Actual mutable-source and entered-version output locations. The source
locations come from the original side of the actual enter output map. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.SourceView
open Silmaril.Machine

def sourceOutputs (base : Nat) (block : Silmaril.Compile.Mir.Block) : List (Lir.Loc Nat) :=
  ((enter base block).outputs.map Prod.fst).map .reg

def enteredOutputs (base : Nat) (block : Silmaril.Compile.Mir.Block) : List (Lir.Loc Nat) :=
  ((enter base block).outputs.map Prod.snd).map .reg

end Silmaril.Compiler.Native.Optimize.LambdaSSA.SourceView
