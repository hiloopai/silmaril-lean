module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Leads
public import Silmaril.Process.LPS.Behaviour

/-! # From a CLI `Leads` proof to LPS facts, through a stuttering simulation (VERIFIED)

The bridge segment of the `sha256` end-to-end proof (`Sha256Cli.Bridge`) moves a total
correctness proof in a CLI-style process model (a step relation `cstep` on states `X` with
event lists over `E`, and a `Leads cstep Ok Done` proof from the launch) to an LPS run
(`SStep segs spec refused` on `Config isa`). This file is the model-independent part.

`StutterSim` is the interface. It relates an LPS configuration to a CLI state and the CLI
history in one of two modes:

* `rel c x h` (aligned): `c` and `x` are at the same instruction boundary;
* `pend c x h` (pending): LPS has executed the trapping instruction and has a syscall pending
  (LPS splits a system call into the trap and the call), while the CLI state `x` is still
  before the trap (the CLI process takes trap, call and return as one step).

Each LPS step from a related pair (with `Ok` and a CLI step available, which is what `Leads`
supplies) is a successful step that is matched by zero CLI steps (aligned → pending, no
event) or one CLI step (with the LPS events the flattening `ev` of the CLI events). Each
related pair whose CLI state can move lets LPS move. Some CLI step from each aligned pair is
matched by a finite LPS run with the flattened events. Aligned pairs at a CLI goal state are
halted LPS configurations with a status in `S`.

From that and `Leads`, everything the LPS target needs follows (all proved here):

* `star_related`: every finite LPS run is the flattening of a CLI run, and ends related;
* `mustExit`: `MustExitInAt S` (every execution exits normally with a status in `S`, no error,
  no stall, no divergence), hence no reachable error and nothing unmodelled;
* `complete`: some CLI run reaches the goal and is matched by an LPS run;
* `obsTrace_prefix`: every observable LPS trace is a prefix of the flattening of some CLI run
  that keeps the invariant or reaches the goal.

No `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS

universe u v

/-- What `Leads` supplies at a state that is not a goal: the invariant holds, the state can
move, and every move keeps the invariant or reaches the goal. -/
def Safe {X : Type u} {E : Type v} (cstep : X → List E → X → Prop) (Ok Done : X → List E → Prop)
    (x : X) (h : List E) : Prop :=
  Ok x h ∧ (∃ e y, cstep x e y) ∧ ∀ e y, cstep x e y → Ok y (h ++ e) ∨ Done y (h ++ e)

theorem Leads.safe {X : Type u} {E : Type v} {cstep : X → List E → X → Prop}
    {Ok Done : X → List E → Prop} {x : X} {h : List E} (leads : Leads cstep Ok Done x h)
    (notDone : ¬ Done x h) : Safe cstep Ok Done x h := by
  cases leads with
  | done goal => exact absurd goal notDone
  | step ok moves next => exact ⟨ok, moves, fun e y s => (next e y s).now⟩

section

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter} {X : Type u} {E : Type v} {cstep : X → List E → X → Prop}
  {Ok Done : X → List E → Prop} {ev : E → List Event} {S : List Word}

/-- A stuttering simulation of the LPS run by the CLI process, with LPS events the
flattening `ev` of the CLI events. -/
structure StutterSim (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (cstep : X → List E → X → Prop) (Ok Done : X → List E → Prop) (ev : E → List Event)
    (S : List Word) where
  rel : Config isa → X → List E → Prop
  pend : Config isa → X → List E → Prop
  /-- An LPS step from an aligned pair: to a pending pair silently, or with one CLI step. -/
  stepRel : ∀ {c x h evs st}, rel c x h → Safe cstep Ok Done x h →
    SStep segs spec refused c evs st → ∃ c', st = .next c' ∧
      ((evs = [] ∧ pend c' x h) ∨
        ∃ es y, cstep x es y ∧ evs = es.flatMap ev ∧ rel c' y (h ++ es))
  /-- An LPS step from a pending pair completes one CLI step. -/
  stepPend : ∀ {c x h evs st}, pend c x h → Safe cstep Ok Done x h →
    SStep segs spec refused c evs st → ∃ c', st = .next c' ∧
      ∃ es y, cstep x es y ∧ evs = es.flatMap ev ∧ rel c' y (h ++ es)
  /-- LPS can move from an aligned pair whose CLI state can move. -/
  progressRel : ∀ {c x h}, rel c x h → Safe cstep Ok Done x h →
    ∃ evs st, SStep segs spec refused c evs st
  /-- LPS can move from a pending pair whose CLI state can move. -/
  progressPend : ∀ {c x h}, pend c x h → Safe cstep Ok Done x h →
    ∃ evs st, SStep segs spec refused c evs st
  /-- An aligned pair at a goal state is a halted LPS configuration with status in `S`. -/
  doneRel : ∀ {c x h}, rel c x h → Done x h →
    ∃ code, c.model.halted = some code ∧ code ∈ S ∧ c.model.killedBy = none
  /-- A pending pair is never at a goal state. -/
  donePend : ∀ {c x h}, pend c x h → ¬ Done x h
  /-- Some CLI step from an aligned pair is matched by a finite LPS run. -/
  back : ∀ {c x h}, rel c x h → Safe cstep Ok Done x h →
    ∃ es y, cstep x es y ∧ ∃ c', Star segs spec refused c (es.flatMap ev) c' ∧ rel c' y (h ++ es)

namespace StutterSim

variable (sim : StutterSim (isa := isa) segs spec refused cstep Ok Done ev S)

include sim in
/-- Every finite LPS run from a related pair is the flattening of a CLI run and ends
related. -/
theorem star_related {c₀ c : Config isa} {tr : List Event} (run : Star segs spec refused c₀ tr c) :
    ∀ {x₀ : X} {h : List E}, Leads cstep Ok Done x₀ h → (sim.rel c₀ x₀ h ∨ sim.pend c₀ x₀ h) →
      ∃ es y, Machine.Trace.Runs cstep x₀ es y ∧ tr = es.flatMap ev ∧
        (sim.rel c y (h ++ es) ∨ sim.pend c y (h ++ es)) := by
  induction run with
  | refl c =>
    intro x₀ h _ related
    exact ⟨[], x₀, .refl _, rfl, by simpa using related⟩
  | @step c₁ evs c₂ tr c₃ first _ ih =>
    intro x₀ h leads related
    cases leads with
    | done goal =>
      rcases related with r | p
      · obtain ⟨code, halted, -, -⟩ := sim.doneRel r goal
        have running := first.not_halted
        rw [halted] at running
        cases running
      · exact absurd goal (sim.donePend p)
    | step ok moves next =>
      have continueWith : ∀ es y, cstep x₀ es y → sim.rel c₂ y (h ++ es) → evs = es.flatMap ev →
          ∃ es' y', Machine.Trace.Runs cstep x₀ es' y' ∧ evs ++ tr = es'.flatMap ev ∧
            (sim.rel c₃ y' (h ++ es') ∨ sim.pend c₃ y' (h ++ es')) := by
        intro es y s r eq
        obtain ⟨es₂, y₂, run₂, tr₂, related₂⟩ := ih (next es y s) (.inl r)
        refine ⟨es ++ es₂, y₂, .cons s run₂, ?_, ?_⟩
        · rw [eq, tr₂, List.flatMap_append]
        · simpa [List.append_assoc] using related₂
      rcases related with r | p
      · obtain ⟨c', same, matched⟩ := sim.stepRel r ⟨ok, moves, fun e y s => (next e y s).now⟩ first
        cases same
        rcases matched with ⟨silent, p'⟩ | ⟨es, y, s, eq, r'⟩
        · obtain ⟨es₂, y₂, run₂, tr₂, related₂⟩ := ih (.step ok moves next) (.inr p')
          exact ⟨es₂, y₂, run₂, by rw [silent, tr₂]; rfl, related₂⟩
        · exact continueWith es y s r' eq
      · obtain ⟨c', same, es, y, s, eq, r'⟩ := sim.stepPend p ⟨ok, moves, fun e y s => (next e y s).now⟩ first
        cases same
        exact continueWith es y s r' eq

include sim in
/-- Universal termination with a status in `S`. -/
theorem mustExit {x : X} {h : List E} (leads : Leads cstep Ok Done x h) :
    (∀ c, sim.rel c x h → MustExitInAt segs spec refused S c) ∧
      (∀ c, sim.pend c x h → MustExitInAt segs spec refused S c) := by
  induction leads with
  | done goal =>
    refine ⟨fun c r => ?_, fun c p => absurd goal (sim.donePend p)⟩
    obtain ⟨code, halted, member, alive⟩ := sim.doneRel r goal
    exact .halted halted member alive
  | @step x h ok moves next ih =>
    have safe : Safe cstep Ok Done x h := ⟨ok, moves, fun e y s => (next e y s).now⟩
    have pending : ∀ c, sim.pend c x h → MustExitInAt segs spec refused S c := by
      intro c p
      obtain ⟨evs, st, s⟩ := sim.progressPend p safe
      refine .running s.not_halted ⟨evs, st, s⟩ ?_ ?_
      · intro evs' bad
        obtain ⟨c', same, -⟩ := sim.stepPend p safe bad
        cases same
      · intro evs' c' s'
        obtain ⟨c'', same, es, y, cs, -, r'⟩ := sim.stepPend p safe s'
        cases same
        exact (ih es y cs).1 _ r'
    refine ⟨fun c r => ?_, pending⟩
    obtain ⟨evs, st, s⟩ := sim.progressRel r safe
    refine .running s.not_halted ⟨evs, st, s⟩ ?_ ?_
    · intro evs' bad
      obtain ⟨c', same, -⟩ := sim.stepRel r safe bad
      cases same
    · intro evs' c' s'
      obtain ⟨c'', same, matched⟩ := sim.stepRel r safe s'
      cases same
      rcases matched with ⟨-, p'⟩ | ⟨es, y, cs, -, r'⟩
      · exact pending _ p'
      · exact (ih es y cs).1 _ r'

include sim in
/-- Some CLI run reaches the goal, and an LPS run with its flattened events matches it. -/
theorem complete {x : X} {h : List E} (leads : Leads cstep Ok Done x h) :
    ∀ {c : Config isa}, sim.rel c x h →
      ∃ es y c', Machine.Trace.Runs cstep x es y ∧ Done y (h ++ es) ∧
        Star segs spec refused c (es.flatMap ev) c' ∧ sim.rel c' y (h ++ es) := by
  induction leads with
  | done goal =>
    intro c r
    exact ⟨[], _, c, .refl _, by simpa using goal, .refl c, by simpa using r⟩
  | @step x h ok moves next ih =>
    intro c r
    have safe : Safe cstep Ok Done x h := ⟨ok, moves, fun e y s => (next e y s).now⟩
    obtain ⟨e, y, s, c₁, star₁, r₁⟩ := sim.back r safe
    obtain ⟨es, z, c₂, run, goal, star₂, r₂⟩ := ih e y s r₁
    refine ⟨e ++ es, z, c₂, .cons s run, by simpa [List.append_assoc] using goal, ?_,
      by simpa [List.append_assoc] using r₂⟩
    rw [List.flatMap_append]
    exact star₁.trans star₂

include sim in
/-- No error is reachable. -/
theorem not_reachesError {c₀ : Config isa} {x₀ : X} {h : List E}
    (leads : Leads cstep Ok Done x₀ h) (r : sim.rel c₀ x₀ h) :
    ¬ ReachesError segs spec refused c₀ :=
  ((sim.mustExit leads).1 c₀ r).not_reachesError

include sim in
/-- Nothing unmodelled is reachable. -/
theorem not_reachesUnmodeled {c₀ : Config isa} {x₀ : X} {h : List E}
    (leads : Leads cstep Ok Done x₀ h) (r : sim.rel c₀ x₀ h) :
    ¬ ReachesUnmodeled segs spec refused c₀ := by
  rintro ⟨tr, c, s, unmodeled⟩
  exact sim.not_reachesError leads r ⟨tr, c, [], s,
    (errorStep_unmodeled_iff.2 unmodeled).sstep⟩

include sim in
/-- Every observable LPS trace is a prefix of the flattening of a CLI run whose end keeps the
invariant or is a goal. -/
theorem obsTrace_prefix (final : ∀ z zs, Done z zs → ∀ e w, ¬ cstep z e w)
    {c₀ : Config isa} {x₀ : X} {h : List E}
    (leads : Leads cstep Ok Done x₀ h) (r : sim.rel c₀ x₀ h) {tr : List Event}
    (obs : ObsTrace segs spec refused c₀ tr) :
    ∃ es y, Machine.Trace.Runs cstep x₀ es y ∧ (Ok y (h ++ es) ∨ Done y (h ++ es)) ∧
      tr <+: es.flatMap ev := by
  obtain ⟨tr', c, star, pre⟩ := obs
  obtain ⟨es, y, run, eq, -⟩ := sim.star_related star leads (.inl r)
  exact ⟨es, y, run, leads.runs final run, eq ▸ pre⟩

end StutterSim

end

end Silmaril.Process.LPS.Problems.Sha256Cli
