module

public import Silmaril.Semantics.SQLite.Isolation.Cancel.Defs

public section

namespace Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel

open Silmaril.Semantics.SQLite.Isolation.Cancel

/-! ## The stuttering-helper countermodel -/

/-- Inside the helper, with one helper tick left that never decreases. -/
def stuck : Sys := ⟨0, ⟨1, 1, 1, [], .running⟩, false, true⟩

theorem stutter_run_succ :
    ∀ n, run onePoll stutterHelper helperCode cancelledAtStart alwaysRun (n + 1) = stuck
  | 0 => rfl
  | n + 1 => by
    show (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun (n + 1)).step
      onePoll stutterHelper helperCode .run = stuck
    rw [stutter_run_succ n]
    rfl

theorem stutter_running (n : Nat) :
    (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).mach.status =
        .running ∧
      (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).mach.sincePoll ≤
        onePoll.period ∧
      (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).visible = true := by
  cases n with
  | zero => exact ⟨rfl, by decide, rfl⟩
  | succ n => rw [stutter_run_succ n]; exact ⟨rfl, by decide, rfl⟩

/-! ## Premise witnesses -/

/-- The invariant of the cleared loop `[work, jump 0, halt]` under poll period `1`. -/
def LoopInv (s : Sys) : Prop :=
  s.visible = false ∧ s.mach.helperLeft = 0 ∧ s.mach.input = [] ∧ s.mach.status = .running ∧
    s.mach.pc ≤ 1 ∧ s.mach.sincePoll ≤ 1

theorem loopInv_step {s : Sys} (h : LoopInv s) :
    LoopInv (s.step onePoll chargedStutterHelper loopCode .run) := by
  obtain ⟨e, ⟨pc, sp, hl, inp, st⟩, pend, vis⟩ := s
  obtain ⟨hv, hh, hi, hs, hpc, hsp⟩ := h
  simp only at hv hh hi hs hpc hsp
  subst hv hh hi hs
  have hpc' : pc = 0 ∨ pc = 1 := by omega
  have hsp' : sp = 0 ∨ sp = 1 := by omega
  rcases hpc' with rfl | rfl <;> rcases hsp' with rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

theorem incoherent_loopInv :
    ∀ n, LoopInv (run onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun (n + 1))
  | 0 => ⟨rfl, rfl, rfl, rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  | n + 1 => loopInv_step (incoherent_loopInv n)

theorem incoherent_running (n : Nat) :
    (run onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun n).mach.status =
      .running := by
  cases n with
  | zero => rfl
  | succ n => exact (incoherent_loopInv n).2.2.2.1

theorem incoherent_fair : FairFrom clearThenRun 0 := fun n _ => ⟨n + 1, by omega, rfl⟩

/-- Waiting on the host after the call. -/
def parked : Sys := ⟨0, ⟨1, 1, 0, [], .waiting⟩, false, true⟩

theorem parked_run_succ :
    ∀ n, run onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun (n + 1) = parked
  | 0 => rfl
  | n + 1 => by
    show (run onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun (n + 1)).step
      onePoll chargedStutterHelper callCode .run = parked
    rw [parked_run_succ n]
    rfl

theorem idle_run :
    ∀ n, run onePoll chargedStutterHelper loopCode cancelledAtStart neverRun n =
      cancelledAtStart
  | 0 => rfl
  | n + 1 => by
    show (run onePoll chargedStutterHelper loopCode cancelledAtStart neverRun n).step
      onePoll chargedStutterHelper loopCode .idle = cancelledAtStart
    rw [idle_run n]
    rfl

theorem not_stopped_of_running {s : MState} (h : s.status = .running) : ¬ s.Stopped := by
  rintro ⟨r, hr⟩; rw [h] at hr; cases hr

theorem stutter_countermodel :
    FairFrom alwaysRun 0 ∧
    ExternalReturnsFrom onePoll stutterHelper helperCode cancelledAtStart alwaysRun 0 ∧
    CoherentFrom alwaysRun 0 ∧
    (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun 0).RelevantVisible ∧
    ∀ n,
      ¬ (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).mach.Stopped ∧
      (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).mach.sincePoll ≤
        onePoll.period ∧
      (run onePoll stutterHelper helperCode cancelledAtStart alwaysRun n).visible = true := by
  refine ⟨fun n _ => ⟨n, Nat.le_refl n, rfl⟩, ?_, fun _ _ => nofun, ⟨rfl, rfl⟩, ?_⟩
  · intro n _ hw
    rw [(stutter_running n).1] at hw
    cases hw
  · intro n
    obtain ⟨h1, h2, h3⟩ := stutter_running n
    exact ⟨not_stopped_of_running h1, h2, h3⟩

theorem incoherent_witness :
    FairFrom clearThenRun 0 ∧
    ExternalReturnsFrom onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun 0 ∧
    (run onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun 0).RelevantVisible ∧
    ¬ CoherentFrom clearThenRun 0 ∧
    ∀ n,
      ¬ (run onePoll chargedStutterHelper loopCode cancelledAtStart clearThenRun n).mach.Stopped := by
  refine ⟨fun n _ => ⟨n + 1, by omega, rfl⟩, ?_, ⟨rfl, rfl⟩,
    fun h => h 0 (Nat.le_refl 0) rfl,
    fun n => not_stopped_of_running (incoherent_running n)⟩
  intro n _ hw
  rw [incoherent_running n] at hw
  cases hw

theorem no_return_witness :
    FairFrom alwaysRun 0 ∧ CoherentFrom alwaysRun 0 ∧
    (run onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun 0).RelevantVisible ∧
    ¬ ExternalReturnsFrom onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun 0 ∧
    ∀ n,
      ¬ (run onePoll chargedStutterHelper callCode cancelledAtStart alwaysRun n).mach.Stopped := by
  refine ⟨fun n _ => ⟨n, Nat.le_refl n, rfl⟩, fun _ _ => nofun, ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro h
    obtain ⟨m, _, hm⟩ := h 1 (by omega) (by rw [parked_run_succ 0]; rfl)
    cases hm
  · intro n
    cases n with
    | zero => exact not_stopped_of_running rfl
    | succ n =>
      rw [parked_run_succ n]
      rintro ⟨r, hr⟩
      cases hr

theorem unfair_witness :
    ExternalReturnsFrom onePoll chargedStutterHelper loopCode cancelledAtStart neverRun 0 ∧
    CoherentFrom neverRun 0 ∧
    (run onePoll chargedStutterHelper loopCode cancelledAtStart neverRun 0).RelevantVisible ∧
    ¬ FairFrom neverRun 0 ∧
    ∀ n,
      ¬ (run onePoll chargedStutterHelper loopCode cancelledAtStart neverRun n).mach.Stopped := by
  refine ⟨?_, fun _ _ => nofun, ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro n _ hw
    rw [idle_run n] at hw
    cases hw
  · intro h
    obtain ⟨m, _, hm⟩ := h 0 (Nat.le_refl 0)
    cases hm
  · intro n
    rw [idle_run n]
    exact not_stopped_of_running rfl

end Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel
