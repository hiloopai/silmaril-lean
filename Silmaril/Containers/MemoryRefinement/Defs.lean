module

public import Silmaril.Containers.Machine.Defs
public import Silmaril.Semantics.MemoryRefinement.Defs

/-! # Plug the existing container process, machine and policy into a behaviour model

The process interpreter takes the ISA and memory system separately. It owns
their event interface; a `ClonePolicy` alone cannot implement a scheduler.
-/

@[expose] public section

namespace Silmaril.Containers.MemoryRefinement

def ofRuns {Entry Event : Type} (runs : Entry → Containers.Model Event) : Semantics.MemoryRefinement.Model (Beh Event) :=
  ⟨Entry, runs, fun entry => ¬ (runs entry).Sat Spec.noUB⟩

/-- No new runtime record. Fix any of these arguments without fixing the others. -/
def onMachine {Image Program Event Cpu Memory : Type} (load : Image → Except Refusal Program)
    (process : Cpu → Memory → Mach.MachineSem Program Event) (isa : Cpu) (memory : Memory)
    (parallel : Mach.ClonePolicy) (observe : Beh Event → Beh Event → Prop := Eq) :=
  ofRuns (Mach.MachRuntime.toRuntime ⟨load, process isa memory, parallel, observe⟩).beh

end Silmaril.Containers.MemoryRefinement
