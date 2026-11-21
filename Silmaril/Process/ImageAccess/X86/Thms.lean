module

public import Silmaril.Process.ImageAccess.Thms
public import Silmaril.Process.ImageAccess.X86.Defs
import Silmaril.Proofs.Process.ImageAccess.X86

@[expose] public section

namespace Silmaril.Process.ImageAccess.X86

open Silmaril.X86 (Reg State)
open Silmaril.X86.Ext (Mem Sz exec)

/-- The full-view adapter recovers the existing decoded executor, including concrete faults.
Unavailable and UB have no translation into the legacy executor's outcomes. -/
theorem load_full (size : Sz) (dest : Reg) (src : Mem) (core : State)
    (memory : Memory) (length : Nat) :
    (match (load size dest src core length).run (Image.full memory).localReader with
      | .ok after => some (Silmaril.X86.Ext.Result.ok after memory)
      | .error .fault => some .dataFault
      | .error _ => none) = some (exec (.load size dest src) core memory length) :=
  Proofs.Process.ImageAccess.X86.load_full size dest src core memory length

/-- Prove the safe load and postcondition on a simpler reader, then transfer them to the
old entry point. The successor has the original concrete memory. -/
theorem load_exec_of_wp {size : Sz} {dest : Reg} {src : Mem} {core : State}
    {memory : Memory} {length : Nat} {source : Reader} {post : State → Prop}
    (refines : Reader.Refines (Image.full memory).localReader source)
    (safe : (load size dest src core length).wp source post) :
    ∃ after, exec (.load size dest src) core memory length = .ok after memory ∧ post after :=
  Proofs.Process.ImageAccess.X86.load_exec_of_wp refines safe

end Silmaril.Process.ImageAccess.X86
