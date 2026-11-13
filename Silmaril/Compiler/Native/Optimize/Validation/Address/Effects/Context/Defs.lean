module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Soundness.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Context.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.SourceView.Thms
/-! Mixed ordinary-address blocks transport between different related partial
inputs. Actual function membership bounds source reads and output observations. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Context
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract

/-- Finite successful contextual refinement at the fixed real address resolver.
The two incoming frames need agree only on complete slots and low optional
registers; candidate execution is a conclusion. -/
def Preserves (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block) : Prop :=
  ∀ (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (memory finalMemory : Lir.Memory) (exit : BlockExit),
    PureSoundness.FrameAgrees base sourceInput candidateInput →
    BlockExec (calls units placement) source sourceInput memory exit sourceFinal finalMemory →
    ∃ candidateFinal, BlockExec (calls units placement) candidate candidateInput memory exit candidateFinal finalMemory ∧
      PureSoundness.FrameAgrees base sourceFinal candidateFinal

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Context
