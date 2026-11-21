module

public import Silmaril.Semantics.Operational.Determinism.Fuel.Defs
public import Silmaril.Semantics.Operational.Determinism.Thms

public section

namespace Silmaril.Proofs.Semantics.Operational.Determinism

open Silmaril.Semantics.Operational

variable {S O : Type*} {sem : WithUB S O}

theorem run_sound (oracle : Oracle sem) (source : S) (fuel : Nat) :
    (oracle.run source fuel).Sound sem source fuel := by
  induction fuel generalizing source with
  | zero =>
    have valid := oracle.valid source
    cases selected : oracle.pick source with
    | move target =>
      rw [selected] at valid
      rw [Oracle.run, selected]
      exact ⟨.nil _, target, valid⟩
    | stop event =>
      rw [selected] at valid
      rw [Oracle.run, selected]
      exact ⟨0, Nat.le_refl _, .nil _, valid⟩
  | succ fuel ih =>
    have valid := oracle.valid source
    cases selected : oracle.pick source with
    | stop event =>
      rw [selected] at valid
      rw [Oracle.run, selected]
      exact ⟨0, Nat.zero_le _, .nil _, valid⟩
    | move target =>
      rw [selected] at valid
      rw [Oracle.run, selected]
      change (oracle.run target fuel).Sound sem source (fuel + 1)
      have trace := ih target
      cases next : oracle.run target fuel with
      | stop final event =>
        rw [next] at trace
        obtain ⟨length, le, path, evidence⟩ := trace
        exact ⟨length + 1, Nat.succ_le_succ le, .cons valid path, evidence⟩
      | exhausted current =>
        rw [next] at trace
        exact ⟨.cons valid trace.1, trace.2⟩

private theorem picks_step (oracle : Oracle sem) {source target : S} (step : sem.step source target)
    (det : sem.toOpSem.StepDetAt source) (discipline : sem.toOpSem.TerminalDiscipline)
    (notUB : ¬ sem.ub source) (known : oracle.pick source ≠ .stop .unknown) :
    oracle.pick source = .move target := by
  have evidence := oracle.valid source
  cases picks : oracle.pick source with
  | move next =>
    rw [picks] at evidence
    rw [det evidence step]
  | stop event =>
    rw [picks] at evidence
    cases event with
    | observed result => exact (discipline evidence _ step).elim
    | stuck => exact (evidence.1 _ step).elim
    | ub => exact (notUB evidence).elim
    | unknown => exact (known picks).elim

private theorem picks_observation (oracle : Oracle sem) {source : S} {outcome : Outcome O}
    (observes : sem.observe source outcome) (det : sem.toOpSem.LocalDetAt source)
    (discipline : sem.toOpSem.TerminalDiscipline) (notUB : ¬ sem.ub source)
    (known : oracle.pick source ≠ .stop .unknown) : oracle.pick source = .stop (.observed outcome) := by
  have evidence := oracle.valid source
  cases picks : oracle.pick source with
  | move next =>
    rw [picks] at evidence
    exact (discipline observes _ evidence).elim
  | stop event =>
    rw [picks] at evidence
    cases event with
    | observed result => rw [det.2 evidence observes]
    | stuck => exact (evidence.2 _ observes).elim
    | ub => exact (notUB evidence).elim
    | unknown => exact (known picks).elim

theorem run_complete (oracle : Oracle sem) {start final : S} {length fuel : Nat} {outcome : Outcome O}
    (path : StepsN sem.step length start final) (observed : sem.observe final outcome) (enough : length ≤ fuel)
    (det : sem.toOpSem.DetFrom start) (discipline : sem.toOpSem.TerminalDiscipline)
    (safe : sem.SafeAt start) (known : ∀ ⦃source⦄, sem.toOpSem.Reach start source →
      oracle.pick source ≠ .stop .unknown) : oracle.run start fuel = .stop final (.observed outcome) := by
  induction path generalizing fuel with
  | nil source =>
    rw [Oracle.run, picks_observation oracle observed (det .refl) discipline
      (fun ub => safe ⟨source, .refl, ub⟩) (known .refl)]
  | @cons length source next final head tail ih =>
    cases fuel with
    | zero => exact (Nat.not_succ_le_zero _ enough).elim
    | succ fuel =>
      rw [Oracle.run, picks_step oracle head (det .refl).1 discipline
        (fun ub => safe ⟨source, .refl, ub⟩) (known .refl)]
      have firstEdge : sem.toOpSem.Reach source next := .single head
      exact ih observed (Nat.le_of_succ_le_succ enough) (fun {_} rest => det (firstEdge.trans rest))
        (safe.of_reach firstEdge) (fun {_} rest => known (firstEdge.trans rest))

theorem no_diverges_of_normal {start final : S} {length : Nat} (path : StepsN sem.step length start final)
    (det : sem.toOpSem.DetFrom start) (normal : sem.toOpSem.Normal final) : ¬ sem.toOpSem.Diverges start := by
  induction path with
  | nil source => exact normal.not_diverges
  | @cons length source next final head tail ih =>
    intro trace
    obtain ⟨selected, step, suffix⟩ := trace.unfold
    have same := (det .refl).1 step head
    subst selected
    have firstEdge : sem.toOpSem.Reach source next := .single head
    exact ih (fun {_} rest => det (firstEdge.trans rest)) normal suffix

end Silmaril.Proofs.Semantics.Operational.Determinism

namespace Silmaril.Proofs.Semantics.Operational.Determinism

open Silmaril.Semantics.Operational

variable {S O : Type*} {sem : WithUB S O}

theorem sized {source final : S} {step : S → S → Prop} (path : Relation.ReflTransGen step source final) :
    ∃ length, StepsN step length source final := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .nil _⟩
  | head edge _ ih => obtain ⟨length, suffix⟩ := ih; exact ⟨length + 1, .cons edge suffix⟩

theorem unsized {length : Nat} {source final : S} {step : S → S → Prop}
    (path : StepsN step length source final) : Relation.ReflTransGen step source final := by
  induction path with
  | nil => exact .refl
  | cons head _ rest => exact (Relation.ReflTransGen.single head).trans rest

theorem may_iff_exists_stepsN (rel : OpSem S O) (source : S) (outcome : Outcome O) :
    rel.May source outcome ↔ ∃ length final, StepsN rel.step length source final ∧ rel.observe final outcome := by
  constructor
  · rintro ⟨final, path, observed⟩
    obtain ⟨length, sizedPath⟩ := sized path
    exact ⟨length, final, sizedPath, observed⟩
  · rintro ⟨_, final, path, observed⟩
    exact ⟨final, unsized path, observed⟩

theorem may_iff_run (oracle : Oracle sem) (start : S) (outcome : Outcome O)
    (det : sem.toOpSem.DetFrom start) (discipline : sem.toOpSem.TerminalDiscipline)
    (safe : sem.SafeAt start) (known : ∀ ⦃source⦄, sem.toOpSem.Reach start source →
      oracle.pick source ≠ .stop .unknown) :
    sem.toOpSem.May start outcome ↔ ∃ fuel final, oracle.run start fuel = .stop final (.observed outcome) := by
  constructor
  · intro may
    obtain ⟨length, final, path, observed⟩ := (may_iff_exists_stepsN sem.toOpSem start outcome).mp may
    exact ⟨length, final, run_complete oracle path observed (Nat.le_refl _) det discipline safe known⟩
  · rintro ⟨fuel, final, run⟩
    have sound := run_sound oracle start fuel
    rw [run] at sound
    obtain ⟨_, _, path, observed⟩ := sound
    exact ⟨final, unsized path, observed⟩

end Silmaril.Proofs.Semantics.Operational.Determinism
