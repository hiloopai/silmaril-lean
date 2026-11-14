module

public import Silmaril.Games.Abstract.Outcome.Defs
import Silmaril.Proofs.Games.Abstract.Outcome.Basic

/-!
# Outcome-tagged traces: small examples

Over the free game with component moves `ready` and `a` and an environment
move `inp`:

* `trapA` (do `a`, then trap) and `loopA` (do `a`, then loop silently): equal
  coarse observations, different tagged observations;
* `trapS` (trap during startup, before `ready`) and `loopS` (diverge during
  startup): coarse-equivalent; `readyTrap` (trap after `ready`) is not
  coarse-equivalent to `trapS`: the abort is kept with its trace;
* `trapA` shows `[a]` as a prefix without diverging after it;
* `exitLoop` (may loop silently or exit and return) has a divergence
  observation that `retM` (return at once) lacks, although a fair scheduler
  would never loop forever;
* `waitM` is quiescent (waits for `inp`), which is neither divergence nor
  deadlock; `stuckM` is deadlocked.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Outcome.Examples

open Silmaril.Games.Abstract Silmaril.Games.Abstract.OMachine
open Silmaril.Proofs.Games.Abstract.Outcome

/-- Moves. -/
inductive Mv | ready | a | inp

/-- `inp` is the environment's; `ready` and `a` are the component's. -/
abbrev Gx : Game.{0} := Game.free Mv fun m => m = Mv.inp

/-- States. -/
inductive St | s0 | s1

/-! ## Trap against silent loop after an event -/

inductive TA : St → Option Gx.Move → St → Prop
  | a : TA .s0 (some Mv.a) .s1

inductive LA : St → Option Gx.Move → St → Prop
  | a : LA .s0 (some Mv.a) .s1
  | tau : LA .s1 none .s1

/-- Do `a`, then trap. -/
def trapA : OMachine Gx Unit := ⟨⟨St, .s0, TA⟩, fun _ _ => False, fun x => x = .s1⟩
/-- Do `a`, then loop silently. -/
def loopA : OMachine Gx Unit := ⟨⟨St, .s0, LA⟩, fun _ _ => False, fun _ => False⟩

theorem runTA_s1 {s : List Gx.Move} {y : St} (h : trapA.Run .s1 s y) : s = [] ∧ y = .s1 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨rfl, rfl⟩
  · cases h
  · cases h

theorem runTA_s0 {s : List Gx.Move} {y : St} (h : trapA.Run .s0 s y) :
    (s = [] ∧ y = .s0) ∨ (s = [Mv.a] ∧ y = .s1) := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h'⟩
  · exact .inl ⟨rfl, rfl⟩
  · cases h
  · cases h
    obtain ⟨rfl, rfl⟩ := runTA_s1 h'
    exact .inr ⟨rfl, rfl⟩

theorem runLA_s1 {x : loopA.State} {s : List Gx.Move} {y : St} (h : loopA.Run x s y)
    (hx : x = .s1) : s = [] ∧ y = .s1 := by
  induction h with
  | nil => exact ⟨rfl, hx⟩
  | tau h _ ih => subst hx; cases h; exact ih rfl
  | vis h _ _ => subst hx; cases h

theorem runLA_s0 {s : List Gx.Move} {y : St} (h : loopA.Run .s0 s y) :
    (s = [] ∧ y = .s0) ∨ (s = [Mv.a] ∧ y = .s1) := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h'⟩
  · exact .inl ⟨rfl, rfl⟩
  · cases h
  · cases h
    obtain ⟨rfl, rfl⟩ := runLA_s1 h' rfl
    exact .inr ⟨rfl, rfl⟩

theorem obs_trapA {o : Obs Gx Unit} :
    o ∈ trapA.obs ↔ o = .fin [] .run ∨ o = .fin [Mv.a] .run ∨ o = .fin [Mv.a] .trap := by
  constructor
  · intro h
    cases h with
    | fin y hr hs =>
      rcases runTA_s0 hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rename_i t
        cases t with
        | run => exact .inl rfl
        | ret r => exact hs.elim
        | trap => cases hs
        | div => obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this
        | wait => exact absurd (hs.2.2.1 _ _ TA.a) (fun h => by cases h)
        | stuck => exact (hs.2 _ _ TA.a).elim
      · rename_i t
        cases t with
        | run => exact .inr (.inl rfl)
        | ret r => exact hs.elim
        | trap => exact .inr (.inr rfl)
        | div => obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this
        | wait => exact absurd (.inr rfl) hs.1
        | stuck => exact absurd (.inr rfl) hs.1
    | inf x h0 hx =>
      have h₁ := hx 0
      rw [h0] at h₁
      rcases runTA_s0 h₁ with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · have h₂ := hx 1
        rw [h] at h₂
        cases (runTA_s1 h₂).1
  · rintro (rfl | rfl | rfl)
    · exact .fin _ (.nil _) trivial
    · exact .fin _ (.vis TA.a (.nil _)) trivial
    · exact .fin (y := St.s1) (.vis TA.a (.nil _)) rfl

theorem obs_loopA {o : Obs Gx Unit} :
    o ∈ loopA.obs ↔ o = .fin [] .run ∨ o = .fin [Mv.a] .run ∨ o = .fin [Mv.a] .div := by
  constructor
  · intro h
    cases h with
    | fin y hr hs =>
      rcases runLA_s0 hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rename_i t
        cases t with
        | run => exact .inl rfl
        | ret r => exact hs.elim
        | trap => exact hs.elim
        | div => obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this
        | wait => exact absurd (hs.2.2.1 _ _ LA.a) (fun h => by cases h)
        | stuck => exact (hs.2 _ _ LA.a).elim
      · rename_i t
        cases t with
        | run => exact .inr (.inl rfl)
        | ret r => exact hs.elim
        | trap => exact hs.elim
        | div => exact .inr (.inr rfl)
        | wait => exact (hs.2.1 _ LA.tau).elim
        | stuck => exact (hs.2 _ _ LA.tau).elim
    | inf x h0 hx =>
      have h₁ := hx 0
      rw [h0] at h₁
      rcases runLA_s0 h₁ with ⟨h, -⟩ | ⟨-, h⟩
      · cases h
      · have h₂ := hx 1
        rw [h] at h₂
        cases (runLA_s1 h₂ rfl).1
  · rintro (rfl | rfl | rfl)
    · exact .fin _ (.nil _) trivial
    · exact .fin _ (.vis LA.a (.nil _)) trivial
    · exact .fin (y := St.s1) (.vis LA.a (.nil _)) ⟨fun _ => .s1, rfl, fun _ => LA.tau⟩

theorem trapA_loopA_coarse : trapA.CoarseEquiv loopA := by
  rw [coarseEquiv_iff]
  refine ⟨fun o ho => ?_, fun s => ?_⟩
  · rw [obs_trapA, obs_loopA]
    have h₁ := ho [Mv.a]
    constructor
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact absurd (Or.inl h) h₁
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact absurd (Or.inr h) h₁
  · simp only [obs_trapA, obs_loopA, Obs.fin.injEq, reduceCtorEq, and_false, false_or, or_false,
      and_true]

theorem trapA_loopA_not_tag : ¬ trapA.TagEquiv loopA := by
  intro h
  have : Obs.fin [Mv.a] .trap ∈ loopA.obs := h ▸ obs_trapA.2 (.inr (.inr rfl))
  rcases obs_loopA.1 this with h | h | h <;> cases h

/-- A prefix is not a divergence: `trapA` shows `[a]` as a prefix and does not
diverge after it. -/
theorem trapA_prefix_not_div :
    Obs.fin [Mv.a] .run ∈ trapA.obs ∧ Obs.fin [Mv.a] .div ∉ trapA.obs :=
  ⟨obs_trapA.2 (.inr (.inl rfl)), fun h => by rcases obs_trapA.1 h with h | h | h <;> cases h⟩

/-! ## Trap or divergence during startup, against a trap after `ready` -/

inductive NoStep : St → Option Gx.Move → St → Prop

inductive LS : St → Option Gx.Move → St → Prop
  | tau : LS .s0 none .s0

inductive RT : St → Option Gx.Move → St → Prop
  | ready : RT .s0 (some Mv.ready) .s1

/-- Trap during startup. -/
def trapS : OMachine Gx Unit := ⟨⟨St, .s0, NoStep⟩, fun _ _ => False, fun x => x = .s0⟩
/-- Diverge during startup. -/
def loopS : OMachine Gx Unit := ⟨⟨St, .s0, LS⟩, fun _ _ => False, fun _ => False⟩
/-- Start (`ready`), then trap. -/
def readyTrap : OMachine Gx Unit := ⟨⟨St, .s0, RT⟩, fun _ _ => False, fun x => x = .s1⟩

theorem runLS {x : loopS.State} {s : List Gx.Move} {y : St} (h : loopS.Run x s y)
    (hx : x = .s0) : s = [] ∧ y = .s0 := by
  induction h with
  | nil => exact ⟨rfl, hx⟩
  | tau h _ ih => subst hx; cases h; exact ih rfl
  | vis h _ _ => subst hx; cases h

theorem runNS {s : List Gx.Move} {y : St} (h : trapS.Run .s0 s y) : s = [] ∧ y = .s0 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨rfl, rfl⟩
  · cases h
  · cases h

theorem obs_trapS {o : Obs Gx Unit} : o ∈ trapS.obs ↔ o = .fin [] .run ∨ o = .fin [] .trap := by
  constructor
  · intro h
    cases h with
    | fin y hr hs =>
      obtain ⟨rfl, rfl⟩ := runNS hr
      rename_i t
      cases t with
      | run => exact .inl rfl
      | ret r => exact hs.elim
      | trap => exact .inr rfl
      | div => obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this
      | wait => exact absurd (.inr rfl) hs.1
      | stuck => exact absurd (.inr rfl) hs.1
    | inf x h0 hx =>
      have h₁ := hx 0
      rw [h0] at h₁
      cases (runNS h₁).1
  · rintro (rfl | rfl)
    · exact .fin _ (.nil _) trivial
    · exact .fin (y := St.s0) (.nil _) rfl

theorem obs_loopS {o : Obs Gx Unit} : o ∈ loopS.obs ↔ o = .fin [] .run ∨ o = .fin [] .div := by
  constructor
  · intro h
    cases h with
    | fin y hr hs =>
      obtain ⟨rfl, rfl⟩ := runLS hr rfl
      rename_i t
      cases t with
      | run => exact .inl rfl
      | ret r => exact hs.elim
      | trap => exact hs.elim
      | div => exact .inr rfl
      | wait => exact (hs.2.1 _ LS.tau).elim
      | stuck => exact (hs.2 _ _ LS.tau).elim
    | inf x h0 hx =>
      have h₁ := hx 0
      rw [h0] at h₁
      cases (runLS h₁ rfl).1
  · rintro (rfl | rfl)
    · exact .fin _ (.nil _) trivial
    · exact .fin (y := St.s0) (.nil _) ⟨fun _ => .s0, rfl, fun _ => LS.tau⟩

theorem trapS_loopS_coarse : trapS.CoarseEquiv loopS := by
  rw [coarseEquiv_iff]
  refine ⟨fun o ho => ?_, fun s => ?_⟩
  · rw [obs_trapS, obs_loopS]
    have h₁ := ho []
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact absurd (Or.inl h) h₁
    · rintro (h | h)
      · exact .inl h
      · exact absurd (Or.inr h) h₁
  · simp [obs_trapS, obs_loopS]

theorem trapS_loopS_not_tag : ¬ trapS.TagEquiv loopS := by
  intro h
  have : Obs.fin [] .trap ∈ loopS.obs := h ▸ obs_trapS.2 (.inr rfl)
  rcases obs_loopS.1 this with h | h <;> cases h

theorem runRT_s0 {s : List Gx.Move} {y : St} (h : readyTrap.Run .s0 s y)
    (hs : s = []) : y = .s0 := by
  subst hs
  rcases h with _ | ⟨h, _⟩
  · rfl
  · cases h

/-- A trap during startup is not coarse-equivalent to a trap after `ready`. -/
theorem trapS_not_coarse_readyTrap : ¬ trapS.CoarseEquiv readyTrap := by
  intro h
  have hm : CObs.fin [] .abort ∈ readyTrap.cobs := h ▸ ⟨_, obs_trapS.2 (.inr rfl), rfl⟩
  obtain ⟨o, ho, he⟩ := hm
  rcases o with ⟨s, t⟩ | ω <;> simp only [Obs.collapse, CObs.fin.injEq, reduceCtorEq] at he
  obtain ⟨rfl, he⟩ := he
  cases ho with
  | fin y hr hs =>
    obtain rfl := runRT_s0 hr rfl
    cases t <;> simp only [Tag.collapse, reduceCtorEq] at he
    · cases hs
    · obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this

/-! ## Fairness: a silent loop that may exit -/

inductive EL : St → Option Gx.Move → St → Prop
  | loop : EL .s0 none .s0
  | exit : EL .s0 none .s1

/-- May loop silently forever, or exit and return. -/
def exitLoop : OMachine Gx Unit := ⟨⟨St, .s0, EL⟩, fun x _ => x = .s1, fun _ => False⟩
/-- Return at once. -/
def retM : OMachine Gx Unit := ⟨⟨St, .s0, NoStep⟩, fun x _ => x = .s0, fun _ => False⟩

theorem exitLoop_obs :
    Obs.fin [] .div ∈ exitLoop.obs ∧ Obs.fin [] (.ret ()) ∈ exitLoop.obs :=
  ⟨.fin (y := St.s0) (.nil _) ⟨fun _ => .s0, rfl, fun _ => EL.loop⟩,
    .fin (y := St.s1) (.tau EL.exit (.nil _)) rfl⟩

theorem runRet {s : List Gx.Move} {y : St} (h : retM.Run .s0 s y) : s = [] ∧ y = .s0 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨rfl, rfl⟩
  · cases h
  · cases h

/-- Without fairness, the possible silent loop is observed. -/
theorem exitLoop_not_coarse_retM : ¬ exitLoop.CoarseEquiv retM := by
  intro h
  have hm : CObs.fin [] .abort ∈ retM.cobs := h ▸ ⟨_, exitLoop_obs.1, rfl⟩
  obtain ⟨o, ho, he⟩ := hm
  rcases o with ⟨s, t⟩ | ω <;> simp only [Obs.collapse, CObs.fin.injEq, reduceCtorEq] at he
  obtain ⟨rfl, he⟩ := he
  cases ho with
  | fin y hr hs =>
    obtain ⟨-, rfl⟩ := runRet hr
    cases t <;> simp only [Tag.collapse, reduceCtorEq] at he
    · exact hs.elim
    · obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this

/-! ## Waiting is neither divergence nor deadlock -/

inductive WI : St → Option Gx.Move → St → Prop
  | inp : WI .s0 (some Mv.inp) .s1

/-- Wait for `inp`, then return. -/
def waitM : OMachine Gx Unit := ⟨⟨St, .s0, WI⟩, fun x _ => x = .s1, fun _ => False⟩
/-- Deadlocked from the start. -/
def stuckM : OMachine Gx Unit := ⟨⟨St, .s0, NoStep⟩, fun _ _ => False, fun _ => False⟩

theorem waitM_obs :
    Obs.fin [] .wait ∈ waitM.obs ∧ Obs.fin [] .div ∉ waitM.obs ∧
      Obs.fin [] .stuck ∉ waitM.obs := by
  refine ⟨.fin (y := St.s0) (.nil _) ⟨?_, fun _ h => (by cases h), fun m _ h => (by cases h; rfl),
    Mv.inp, .s1, WI.inp⟩, ?_, ?_⟩
  · rintro (⟨_, h⟩ | h)
    · cases h
    · exact h
  · intro h
    cases h with
    | fin y hr hs =>
      rcases hr with _ | ⟨h, _⟩
      · obtain ⟨f, h0, hf⟩ := hs; have := hf 0; rw [h0] at this; cases this
      · cases h
  · intro h
    cases h with
    | fin y hr hs =>
      rcases hr with _ | ⟨h, _⟩
      · exact hs.2 _ _ WI.inp
      · cases h

theorem stuckM_obs : Obs.fin [] .stuck ∈ stuckM.obs :=
  .fin (y := St.s0) (.nil _) ⟨fun h => by rcases h with ⟨_, h⟩ | h <;> exact h, fun _ _ h => by cases h⟩

end Silmaril.Proofs.Games.Abstract.Outcome.Examples
