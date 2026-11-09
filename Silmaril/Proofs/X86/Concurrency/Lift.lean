module

public import Silmaril.X86.Concurrency.Lift.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms

/-!
# The single-threaded lift for sequential machines: proofs

* `evRun_of_reaches`: a run of a flat-evented machine has an event trace;
* `evRun_replay`: the trace is `ActOk` and replays sequentially from the run's first memory to
  its last;
* `runUnder_of_reaches`: so, under every `SC ⊑ M ⊑ XL`, the run reads the same under `M`;
* `totalUnder_of`: a total function contract on a flat-evented machine is total under `M`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Lift

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.Concurrency.Lift
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.Machine.Execution (run Reaches)

variable {σ : Type} {step : σ → Option σ} {mem : σ → Mem} {P : σ → List XAct → Prop}

theorem evRun_of_run (hF : FlatStep step mem P) :
    ∀ (n : Nat) (s t : σ), run step n s = some t → ∃ acts, EvRun step mem P s t acts
  | 0, s, t, h => by
    simp only [Silmaril.Machine.Execution.run_zero, Option.some.injEq] at h
    subst h; exact ⟨[], .refl s⟩
  | n + 1, s, t, h => by
    simp only [Silmaril.Machine.Execution.run_succ] at h
    cases hs : step s with
    | none => simp [hs] at h
    | some s' =>
      rw [hs, Option.bind_some] at h
      obtain ⟨acts, hP, hok, hr⟩ := hF s s' hs
      obtain ⟨rest, hrest⟩ := evRun_of_run hF n s' t h
      exact ⟨_, .cons hs hP hok hr hrest⟩

theorem evRun_of_reaches (hF : FlatStep step mem P) {s t : σ} (h : Reaches step s t) :
    ∃ acts, EvRun step mem P s t acts := by
  obtain ⟨n, hn⟩ := h
  exact evRun_of_run hF n s t hn

theorem evRun_replay {s t : σ} {acts : List XAct} (h : EvRun step mem P s t acts) :
    (∀ a ∈ acts, ActOk a) ∧ actsReplay (mem s) acts = some (mem t) := by
  induction h with
  | refl s => exact ⟨fun _ h => by simp at h, rfl⟩
  | cons _ _ hok hr _ ih =>
    refine ⟨fun a ha => (List.mem_append.mp ha).elim (hok a) (ih.1 a), ?_⟩
    rw [actsReplay_append, hr, Option.bind_some]
    exact ih.2

theorem runUnder_of_evRun {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) {s t : σ}
    {acts : List XAct} (h : EvRun step mem P s t acts) : RunUnder M step mem P s t := by
  obtain ⟨hok, hr⟩ := evRun_replay h
  refine ⟨acts, h, fun m => ?_⟩
  rw [oneSem_iff hsc hxl _ acts hok, hr]
  exact ⟨fun h => (Option.some.inj h).symm, fun h => h ▸ rfl⟩

/-- **A run of a flat-evented machine reads the same under every `SC ⊑ M ⊑ XL`.** -/
theorem runUnder_of_reaches (hF : FlatStep step mem P) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M)
    (hxl : M ⊑ Exec.Xl) {s t : σ} (h : Reaches step s t) : RunUnder M step mem P s t := by
  obtain ⟨acts, ha⟩ := evRun_of_reaches hF h
  exact runUnder_of_evRun hsc hxl ha

/-- **A total contract on a flat-evented machine is total under every `SC ⊑ M ⊑ XL`.** -/
theorem totalUnder_of {I : Silmaril.X86.SegVC.Isa σ} {S : Silmaril.X86.FnContract.Spec σ}
    (hF : FlatStep I.step (fun s => flat (I.mem s)) P) (hT : S.Total I) {M : Exec → Prop}
    (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) : S.TotalUnder I P M := by
  intro s hl ha he
  obtain ⟨t, hr, hres⟩ := hT s hl ha he
  exact ⟨t, hr, hres, runUnder_of_reaches hF hsc hxl hr⟩

end Silmaril.Proofs.X86.Concurrency.Lift
