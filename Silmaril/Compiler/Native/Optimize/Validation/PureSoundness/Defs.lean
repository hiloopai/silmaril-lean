module

public import Silmaril.Compiler.Native.Optimize.Validation.Candidate.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.SourceReads.Thms
/-! Finite successful open-block refinement for the actual pure validator.
Partial incoming frames and arbitrary open-call meanings are retained. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.PureSoundness
open Silmaril.Machine
open Silmaril.Compile

structure FrameAgrees (base : Nat) (source candidate : Lir.Frame Nat) : Prop where
  slots : candidate.slots = source.slots
  registers : ∀ reg, reg < base → candidate.get reg = source.get reg

/-- Every actual finite successful source run has a candidate run with the same
exit and memory and agreement on all original register names below base. -/
def Preserves (base : Nat) (source candidate : Mir.Block) : Prop :=
  ∀ (calls : OpenCalls) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit),
    BlockExec calls source frame memory exit sourceFrame sourceMemory →
    ∃ candidateFrame, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      FrameAgrees base sourceFrame candidateFrame

end Silmaril.Compiler.Native.Optimize.Validation.PureSoundness
