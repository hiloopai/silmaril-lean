module

public import Silmaril.Process.TypedSyscall.Defs

@[expose] public section

namespace Silmaril.Proofs.Process.TypedSyscall

open Silmaril.Process.TypedSyscall

private theorem map_map {Reply Middle Last Store : Type} (project : Reply → Middle)
    (finish : Middle → Last) (answer : Completion Reply Store) :
    (answer.map project).map finish = answer.map (fun reply => finish (project reply)) := by
  cases answer <;> rfl

theorem pull_then {source middle target : Signature} {Store Event : Type}
    (first : source.Hom middle) (second : middle.Hom target) (kernel : Kernel target Store Event)
    (req : source.Request) (store : Store) (event : Event) (answer : Completion (source.Response req) Store) :
    (kernel.pull second).pull first req store event answer ↔ kernel.pull (first.then second) req store event answer := by
  unfold Kernel.pull
  have compose (concrete : Completion (target.Response (second.request (first.request req))) Store) :=
    map_map (second.response (first.request req)) (first.response req) concrete
  constructor
  · rintro ⟨_, ⟨concrete, admitted, rfl⟩, mapped⟩
    exact ⟨concrete, admitted, (compose concrete).symm.trans mapped⟩
  · rintro ⟨concrete, admitted, mapped⟩
    exact ⟨_, ⟨concrete, admitted, rfl⟩, (compose concrete).trans mapped⟩

private theorem finish_map {Reply Other Pool Store Stop : Type} (project : Reply → Other)
    (commit : Other → Pool) (answer : Completion Reply Store) :
    (answer.map project).finish (Stop := Stop) commit = answer.finish (fun reply => commit (project reply)) := by
  cases answer <;> rfl

theorem step_push_iff {source target : Signature} {Image Pool Core Store Event Stop : Type}
    (hom : source.Hom target) (cpu : Cpu source Image Core Store Stop)
    (kernel : Kernel target Store Event) (schedule : Scheduler Pool Core)
    (image : Image) (pool : Pool) (store : Store) (observation : Option Event)
    (outcome : Outcome Pool Store Stop) :
    Step (cpu.push hom) kernel schedule image pool store observation outcome ↔
      Step cpu (kernel.pull hom) schedule image pool store observation outcome := by
  unfold Step
  cases chosen : schedule pool with
  | none => rfl
  | some slot =>
    obtain ⟨core, replace⟩ := slot
    cases selected : cpu image core store with
    | retire next updated => simp only [Cpu.push, selected, Action.push]
    | stop reason => simp only [Cpu.push, selected, Action.push]
    | call req resume =>
      simp only [Cpu.push, selected, Action.push, Kernel.pull]
      constructor
      · rintro ⟨event, answer, admitted, observed, finished⟩
        exact ⟨event, answer.map (hom.response req), ⟨answer, admitted, rfl⟩, observed,
          finished.trans
            (finish_map (Stop := Stop) (hom.response req) (fun reply => replace (resume reply)) answer).symm⟩
      · rintro ⟨event, _, ⟨answer, admitted, rfl⟩, observed, finished⟩
        exact ⟨event, answer, admitted, observed,
          finished.trans (finish_map (Stop := Stop) (hom.response req) (fun reply => replace (resume reply)) answer)⟩

end Silmaril.Proofs.Process.TypedSyscall
