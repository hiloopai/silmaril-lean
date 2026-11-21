module

public import Silmaril.Containers.TypedSyscall.Defs
public import Silmaril.Process.TypedSyscall.Thms

@[expose] public section

namespace Silmaril.Containers.TypedSyscall

open Silmaril.Process.TypedSyscall

/-- For this constructed pullback the entire machines are equal, so the
existing interpreter and runtime see the same executions, including stops. -/
theorem completedMachine_push {source target : Signature} {Image Pool Core Store Event : Type}
    (hom : source.Hom target) (cpu : Cpu source Image Core Store Stop)
    (kernel : Kernel target Store Event) (schedule : Scheduler Pool Core) (isInput : Event → Bool) :
    completedMachine isInput (Step (cpu.push hom) kernel schedule) =
      completedMachine isInput (Step cpu (kernel.pull hom) schedule) := by
  apply congrArg (completedMachine isInput)
  exact funext fun image => funext fun pool => funext fun store => funext fun observation =>
    funext fun outcome => propext (step_push_iff hom cpu kernel schedule image pool store observation outcome)

theorem stoppedWord_map {Event Other : Type} (label : Event → Other) (events : List Event) (stop : Stop) :
    (stoppedWord events stop).map (relabel label) = stoppedWord (events.map label) stop := by
  simp [stoppedWord, Streams.Word.map, relabel, List.map_map, Function.comp_def]

/-- A relabeled prefix has the same verdict for the pulled-back event policy.
In particular, relabeling cannot make a terminal UB marker acceptable. -/
theorem relabel_vlang {Event Other : Type} (label : Event → Other) (ok : Other → Bool)
    (observations : List (Check.Obs Event)) :
    observations.map (relabel label) ∈ Check.vlang ok ↔ observations ∈ Check.vlang (ok ∘ label) := by
  have policy : Check.Obs.ok ok ∘ relabel label = Check.Obs.ok (ok ∘ label) :=
    funext fun observation => by cases observation <;> rfl
  change ((observations.map (relabel label)).all (Check.Obs.ok ok) = true) ↔
    observations.all (Check.Obs.ok (ok ∘ label)) = true
  rw [List.all_map, policy]

end Silmaril.Containers.TypedSyscall
