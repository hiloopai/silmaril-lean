module

public import Silmaril.Compiler.Core.ExactRun.Defs
@[expose] public section

/-!
# Checking exact, terminating Core executions

The ordinary runner selects one schedule. This checker accepts a choice or
scheduling request only when it has exactly one alternative. At each accepted step all transitions have the
same successor, so a completed check characterises the entire behaviour set,
including the absence of undefined behaviour and infinite executions.
-/

namespace Silmaril.Compile.C.Sem.ExactCore

open Silmaril.Compile.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.C.Sem (Obs Exit)

/-- One alternative is a forced successor; zero or multiple alternatives decline. -/
def singletonNext (mem : Silmaril.Cerberus.Mem.Concrete.State) :
    List (Control × List Frame) → Option State
  | [(c, k)] => some ⟨c, k, mem⟩
  | _ => none

theorem singletonNext_eq {mem : Silmaril.Cerberus.Mem.Concrete.State}
    {xs : List (Control × List Frame)} {t : State}
    (h : singletonNext mem xs = some t) :
    ∃ c k, xs = [(c, k)] ∧ t = ⟨c, k, mem⟩ := by
  cases xs with
  | nil => simp [singletonNext] at h
  | cons x rest =>
    cases rest with
    | nil =>
      rcases x with ⟨c, k⟩
      exact ⟨c, k, rfl, (Option.some.inj h).symm⟩
    | cons _ _ => simp [singletonNext] at h

/-- Extend the existing checker only to singleton choice and schedule requests. -/
def forcedNext (mem : Silmaril.Cerberus.Mem.Concrete.State) (r : Request) : Option State :=
  match r with
  | .choose xs | .scheduled xs => singletonNext mem xs
  | _ => Compile.Core.forcedNext mem r

theorem forcedNext_sound {mem : Silmaril.Cerberus.Mem.Concrete.State}
    {r : Request} {t : State} (h : forcedNext mem r = some t) :
    ∃ a, Respond mem r a t := by
  cases r with
  | choose xs =>
    obtain ⟨c, k, rfl, rfl⟩ := singletonNext_eq h
    exact ⟨_, .choose (by simp)⟩
  | scheduled xs =>
    obtain ⟨c, k, rfl, rfl⟩ := singletonNext_eq h
    exact ⟨_, .scheduled (by simp)⟩
  | _ => exact Compile.Core.forcedNext_sound h

theorem forcedNext_unique {mem : Silmaril.Cerberus.Mem.Concrete.State}
    {r : Request} {t : State} (h : forcedNext mem r = some t)
    {a : Label} {u : State} (hu : Respond mem r a u) : u = t := by
  cases r with
  | choose xs =>
    obtain ⟨c, k, rfl, rfl⟩ := singletonNext_eq h
    cases hu
    simp_all
  | scheduled xs =>
    obtain ⟨c, k, rfl, rfl⟩ := singletonNext_eq h
    cases hu
    simp_all
  | _ =>
    apply Compile.Core.forcedNext_unique (hu := hu)
    simpa only [forcedNext] using h

/-- Removing a forced live step preserves all behaviours, not only a chosen run. -/
theorem behFrom_forced {file : Program} {labels : Labels} {s t : State}
    (live : ∀ o, s.control ≠ .halt o)
    (h : forcedNext s.memory (request file labels s) = some t) :
    behFrom file labels s = behFrom file labels t := by
  obtain ⟨a, ha⟩ := forcedNext_sound h
  have first : (lts file labels).Tr s a t := .respond live ha
  have unique : ∀ b u, (lts file labels).Tr s b u → u = t := by
    intro b u hu
    cases hu with
    | respond _ hu => exact forcedNext_unique h hu
  have noFinal : finalObs s = ∅ := by
    unfold finalObs
    cases hc : s.control <;> simp_all
  apply Set.ext
  intro o
  constructor
  · rintro (⟨acts, u, path, final⟩ | ⟨acts, u, loc, ub, path, bad⟩ | ⟨eq, div⟩)
    · cases path with
      | refl => exact False.elim (by simp [noFinal] at final)
      | stepL step tail =>
        have eq := unique _ _ step
        subst_vars
        exact .inl ⟨_, _, tail, final⟩
    · cases path with
      | refl => exact False.elim (live _ bad)
      | stepL step tail =>
        have eq := unique _ _ step
        subst_vars
        exact .inr (.inl ⟨_, _, loc, ub, tail, bad⟩)
    · obtain ⟨u, ⟨b, step⟩, tail⟩ := div.unfold
      have eq' := unique b u step
      subst u
      exact .inr (.inr ⟨eq, tail⟩)
  · rintro (⟨acts, u, path, final⟩ | ⟨acts, u, loc, ub, path, bad⟩ | ⟨eq, div⟩)
    · exact .inl ⟨_, _, .stepL first path, final⟩
    · exact .inr (.inl ⟨_, _, loc, ub, .stepL first path, bad⟩)
    · exact .inr (.inr ⟨eq, Silmaril.InfiniteTrace.fold ⟨a, first⟩ div⟩)

/-- Bounded checker for a forced execution ending in a specified integer. -/
def exactRun (file : Program) (labels : Labels) : Nat → State → Option Obs
  | 0, _ => none
  | n + 1, s =>
      match s.control with
      | .halt _ => exactFinal s
      | _ => do exactRun file labels n (← forcedNext s.memory (request file labels s))

theorem exactRun_sound (file : Program) (labels : Labels) (fuel : Nat)
    (s : State) (o : Obs) (h : exactRun file labels fuel s = some o) :
    behFrom file labels s = {o} := by
  induction fuel generalizing s with
  | zero => simp [exactRun] at h
  | succ n ih =>
    by_cases halted : ∃ result, s.control = .halt result
    · obtain ⟨result, hr⟩ := halted
      simp only [exactRun, hr] at h
      exact exactFinal_sound h
    · have live : ∀ result, s.control ≠ .halt result := by simpa using halted
      have unfoldRun : exactRun file labels (n + 1) s =
          (forcedNext s.memory (request file labels s)).bind (exactRun file labels n) := by
        cases hc : s.control <;> simp only [exactRun, hc]
        all_goals first | rfl | exact False.elim (live _ hc)
      rw [unfoldRun] at h
      cases hn : forcedNext s.memory (request file labels s) with
      | none => simp [hn] at h
      | some t =>
        simp only [hn, Option.bind_some] at h
        exact (behFrom_forced live hn).trans (ih t h)

/-- Check the complete startup and body of a closed Core file. -/
def exactProgram (fuel : Nat) (file : Program) : Option Obs :=
  match initial file with
  | .ok (s, labels) => exactRun file labels fuel s
  | .error _ => none

theorem exactProgram_sound {fuel : Nat} {file : Program} {o : Obs}
    (h : exactProgram fuel file = some o) : beh file = {o} := by
  unfold exactProgram at h
  unfold beh
  cases hi : initial file with
  | ok pair =>
    rcases pair with ⟨s, labels⟩
    simp only [hi] at h ⊢
    exact exactRun_sound _ _ _ _ _ h
  | error e => simp [hi] at h

end Silmaril.Compile.C.Sem.ExactCore
