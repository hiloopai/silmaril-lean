module

public import Silmaril.Process.TypedSyscall.Defs
import Silmaril.Proofs.Process.TypedSyscall.Transport

@[expose] public section

namespace Silmaril.Process.TypedSyscall

theorem Action.push_then {source middle target : Signature} {Core Store Stop : Type}
    (first : source.Hom middle) (second : middle.Hom target) (action : Action source Core Store Stop) :
    (action.push first).push second = action.push (first.then second) := by cases action <;> rfl

theorem Kernel.pull_then {source middle target : Signature} {Store Event : Type}
    (first : source.Hom middle) (second : middle.Hom target) (kernel : Kernel target Store Event)
    (req : source.Request) (store : Store) (event : Event) (answer : Completion (source.Response req) Store) :
    (kernel.pull second).pull first req store event answer ↔ kernel.pull (first.then second) req store event answer :=
  Proofs.Process.TypedSyscall.pull_then first second kernel req store event answer

/-- Pushing the CPU across signatures is equivalent to pulling the kernel back.
This preserves the event and outcome, including store changes and non-returning
exit. It does not assert kernel progress or relate two independently defined kernels. -/
theorem step_push_iff {source target : Signature} {Image Pool Core Store Event Stop : Type}
    (hom : source.Hom target) (cpu : Cpu source Image Core Store Stop)
    (kernel : Kernel target Store Event) (schedule : Scheduler Pool Core)
    (image : Image) (pool : Pool) (store : Store) (observation : Option Event)
    (outcome : Outcome Pool Store Stop) :
    Step (cpu.push hom) kernel schedule image pool store observation outcome ↔
      Step cpu (kernel.pull hom) schedule image pool store observation outcome :=
  Proofs.Process.TypedSyscall.step_push_iff hom cpu kernel schedule image pool store observation outcome

end Silmaril.Process.TypedSyscall
