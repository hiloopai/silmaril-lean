module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Source.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Candidate.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Soundness.Thms
/-! Actual mixed-address checker refinement fixes the real source resolver and
retains partial frames, real ordered memory effects and all low observations. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Soundness
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract

/-- Every real finite successful source run has a same-exit, same-memory
candidate run with whole-slot and low optional-register agreement, at this
actual units/placement resolver. Calls and the native frame symbol are separate. -/
def Preserves (units : Array Mir.Unit) (placement : MirSem.Placement)
    (base : Nat) (source candidate : Mir.Block) : Prop :=
  ∀ (frame sourceFrame : Lir.Frame Nat) (memory sourceMemory : Lir.Memory) (exit : BlockExit),
    BlockExec (calls units placement) source frame memory exit sourceFrame sourceMemory →
    ∃ candidateFrame, BlockExec (calls units placement) candidate frame memory exit candidateFrame sourceMemory ∧
      PureSoundness.FrameAgrees base sourceFrame candidateFrame

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Soundness
