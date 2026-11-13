module

public import Silmaril.Proofs.Wasm.Det.Shared.Game
public import Silmaril.Wasm.Det.Shared.Untyped.Defs
public import Silmaril.Wasm.Game.Untyped.Thms

/-!
# Determinism of the untyped store-passing instance strategy

The twin relation of `Silmaril.Proofs.Wasm.Det.Shared.Game`, over the hidden states of the untyped
system `U.lts P` (`Silmaril.Wasm.Game.Untyped`): both idle, or the threads of one export call `f`
reached from `invoke f.store (U.addr f.target) f.args` by store-writing runs (`RunsS`) with the
same trace, read off the play. The untyped system asks every callout raw and answers with the
raw result, so a non-trapping Core output determines the move without a typing filter.

New proofs (the structure follows `Silmaril.Proofs.Wasm.Det.Shared.Game`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Shared.Untyped

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game Silmaril.Wasm.Det.Shared
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Det.Shared (config_store' out_of_callout' config_resume steps_of_internal)

variable {U : UInstance} {P : Profile} {A : Store Nat → Store Nat → Prop}
  {S : Store Nat → Prop}

/-- The invocation of an export question, in the store it carries. -/
abbrev uInv (U : UInstance) (f : U.F.Op) : Config Nat :=
  invoke f.store (U.addr f.target) f.args

/-- Two hidden states of the untyped system reached along the same play. -/
inductive UTwin (P : Profile) (U : UInstance) (A : Store Nat → Store Nat → Prop)
    (S : Store Nat → Prop) : U.State → U.State → Prop where
  | idle : UTwin P U A S .idle .idle
  | running {f : U.F.Op} {s₁ s₂ : Store Nat} {t₁ t₂ : Thread} {tr : List SCall}
      (hS : S f.store) (r₁ : RunsS P A (uInv U f) tr (t₁.config s₁))
      (r₂ : RunsS P A (uInv U f) tr (t₂.config s₂)) :
      UTwin P U A S (.running f s₁ t₁) (.running f s₂ t₂)
  | waiting {f : U.F.Op} {s : Store Nat} {t₁ t₂ : Thread} {tr : List SCall} {e : U.E.Op}
      {h : Nat} {args : List Val} (hS : S f.store) (r₁ : RunsS P A (uInv U f) tr (t₁.config s))
      (r₂ : RunsS P A (uInv U f) tr (t₂.config s)) (he : e.store = s)
      (c₁ : CalloutAt s t₁ h args) (c₂ : CalloutAt s t₂ h args) :
      UTwin P U A S (.waiting f s t₁ e) (.waiting f s t₂ e)

theorem twin_tau_left {x₁ x₁' x₂ : U.State} (ht : UTwin P U A S x₁ x₂)
    (h : U.Trans P x₁ none x₁') : UTwin P U A S x₁' x₂ := by
  cases ht with
  | idle => cases h
  | waiting => cases h
  | running hS r₁ r₂ =>
    cases h with
    | tau hi => exact .running hS (runsS_steps r₁ (steps_of_internal hi)) r₂

theorem twin_tau_right {x₁ x₂ x₂' : U.State} (ht : UTwin P U A S x₁ x₂)
    (h : U.Trans P x₂ none x₂') : UTwin P U A S x₁ x₂' := by
  cases ht with
  | idle => cases h
  | waiting => cases h
  | running hS r₁ r₂ =>
    cases h with
    | tau hi => exact .running hS r₁ (runsS_steps r₂ (steps_of_internal hi))

theorem twin_taus_left {x₁ y₁ : (U.lts P).State} {x₂ : U.State} {l : List (Move U.E U.F)}
    (h : (U.lts P).Run x₁ l y₁) (hl : l = []) (ht : UTwin P U A S x₁ x₂) :
    UTwin P U A S y₁ x₂ := by
  induction h with
  | nil => exact ht
  | tau hs _ ih => exact ih hl (twin_tau_left ht hs)
  | vis => cases hl

theorem twin_taus_right {x₁ : U.State} {x₂ y₂ : (U.lts P).State} {l : List (Move U.E U.F)}
    (h : (U.lts P).Run x₂ l y₂) (hl : l = []) (ht : UTwin P U A S x₁ x₂) :
    UTwin P U A S x₁ y₂ := by
  induction h with
  | nil => exact ht
  | tau hs _ ih => exact ih hl (twin_tau_right ht hs)
  | vis => cases hl

/-- The Proponent moves of a running thread: a raw import question in the current store, or the
raw result with the final store. -/
theorem p_out {f : U.F.Op} {s : Store Nat} {t : Thread} {m : Move U.E U.F} {q' : U.State}
    (h : U.Trans P (.running f s t) (some m) q') :
    (∃ hh args, CalloutAt s t hh args ∧ m = .inl (.ask ⟨hh, s, args⟩) ∧
        q' = .waiting f s t ⟨hh, s, args⟩) ∨
      (∃ r, ResultAt s t r ∧ m = .inr (.ans f ⟨s, r⟩) ∧ q' = .idle) := by
  cases h with
  | ucall callout => exact .inl ⟨_, _, callout, rfl, rfl⟩
  | oret final => exact .inr ⟨_, final, rfl, rfl⟩

/-- The move a Core output of export call `f` in the store `s` is played as. -/
def UMoveOf (f : U.F.Op) (s : Store Nat) : Out → Move U.E U.F
  | .call hh args => .inl (.ask ⟨hh, s, args⟩)
  | .ret r => .inr (.ans f ⟨s, r⟩)

/-- A Proponent move of a running thread is a trap, or plays a non-trapping output. -/
theorem p_move {f : U.F.Op} {s : Store Nat} {t : Thread} {m : Move U.E U.F} {q' : U.State}
    (h : U.Trans P (.running f s t) (some m) q') :
    PTrap (uTraps U.X) m ∨ ∃ o, OutAt (t.config s) o ∧ m = UMoveOf f s o := by
  rcases p_out h with ⟨hh, args, hc, rfl, -⟩ | ⟨r, hr, rfl, -⟩
  · exact .inr ⟨_, out_of_callout' hc, rfl⟩
  · by_cases ht : r = .trap
    · subst ht
      exact .inl rfl
    · exact .inr ⟨_, .ret ht hr, rfl⟩

/-- Twin running threads: the next Proponent moves agree modulo traps. -/
theorem running_p (hD : ∀ f : U.F.Op, S f.store → DetCfgS P A (uInv U f)) {f : U.F.Op}
    {s₁ s₂ : Store Nat} {t₁ t₂ : Thread} {tr : List SCall} (hS : S f.store)
    (r₁ : RunsS P A (uInv U f) tr (t₁.config s₁)) (r₂ : RunsS P A (uInv U f) tr (t₂.config s₂))
    {q₁' q₂' : U.State} {m₁ m₂ : Move U.E U.F}
    (h₁ : U.Trans P (.running f s₁ t₁) (some m₁) q₁')
    (h₂ : U.Trans P (.running f s₂ t₂) (some m₂) q₂') :
    m₁ = m₂ ∨ PTrap (uTraps U.X) m₁ ∨ PTrap (uTraps U.X) m₂ := by
  rcases p_move h₁ with ht₁ | ⟨o₁, ho₁, rfl⟩
  · exact .inr (.inl ht₁)
  rcases p_move h₂ with ht₂ | ⟨o₂, ho₂, rfl⟩
  · exact .inr (.inr ht₂)
  have hd : o₁ = o₂ ∧ (t₁.config s₁).store = (t₂.config s₂).store :=
    hD _ hS _ _ _ _ _ r₁ r₂ ho₁ ho₂
  have hs : s₁ = s₂ := by rw [← config_store' s₁ t₁, ← config_store' s₂ t₂]; exact hd.2
  rw [hd.1, hs]
  exact .inl rfl

/-- **Twin states make the same next Proponent move, modulo traps.** -/
theorem twin_p (hD : ∀ f : U.F.Op, S f.store → DetCfgS P A (uInv U f))
    {q₁ q₂ q₁' q₂' : U.State} {m₁ m₂ : Move U.E U.F} (ht : UTwin P U A S q₁ q₂)
    (h₁ : U.Trans P q₁ (some m₁) q₁') (h₂ : U.Trans P q₂ (some m₂) q₂') (hm₁ : m₁.IsP) :
    m₁ = m₂ ∨ PTrap (uTraps U.X) m₁ ∨ PTrap (uTraps U.X) m₂ := by
  cases ht with
  | idle =>
    cases h₁
    exact hm₁.elim
  | waiting =>
    cases h₁
    exact hm₁.elim
  | running hS r₁ r₂ => exact running_p hD hS r₁ r₂ h₁ h₂

/-- A twin waiting thread resumed with an admissible answer. -/
theorem resume_run {f : U.F.Op} {s s' : Store Nat} {t : Thread} {tr : List SCall} {hh : Nat}
    {args : List Val} (r : RunsS P A (uInv U f) tr (t.config s)) (c : CalloutAt s t hh args)
    (res : Result) (hA : A s s') :
    RunsS P A (uInv U f) (tr ++ [⟨hh, args, res, s'⟩]) ((resumeResult s t res).config s') := by
  obtain ⟨E, a, hd⟩ := c
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, hh, args) := by
    rw [config_store']
    exact hd
  have hA' : A (t.config s).store s' := by
    rw [config_store']
    exact hA
  rw [config_resume hd]
  exact runsS_snoc r hd' res hA'

/-- Twin running threads after a common non-trapping Proponent move. -/
theorem running_vis {f : U.F.Op}
    {s₁ s₂ : Store Nat} {t₁ t₂ : Thread} {tr : List SCall} (hS : S f.store)
    (r₁ : RunsS P A (uInv U f) tr (t₁.config s₁)) (r₂ : RunsS P A (uInv U f) tr (t₂.config s₂))
    {q₁' q₂' : U.State} {m : Move U.E U.F}
    (h₁ : U.Trans P (.running f s₁ t₁) (some m) q₁')
    (h₂ : U.Trans P (.running f s₂ t₂) (some m) q₂') : UTwin P U A S q₁' q₂' := by
  rcases p_out h₁ with ⟨hh, args, hc₁, rfl, rfl⟩ | ⟨r, hr₁, rfl, rfl⟩
  · rcases p_out h₂ with ⟨hh', args', hc₂, hm', rfl⟩ | ⟨_, _, hm', _⟩
    · cases hm'
      exact .waiting hS r₁ r₂ rfl hc₁ hc₂
    · cases hm'
  · rcases p_out h₂ with ⟨_, _, _, hm', _⟩ | ⟨r', hr₂, hm', rfl⟩
    · cases hm'
    · exact .idle

/-- **Twin states stay twins along a common admissible move.** -/
theorem twin_vis {q₁ q₂ q₁' q₂' : U.State} {m : Move U.E U.F}
    (ht : UTwin P U A S q₁ q₂)
    (h₁ : U.Trans P q₁ (some m) q₁') (h₂ : U.Trans P q₂ (some m) q₂')
    (hok : UOk U A S m) : UTwin P U A S q₁' q₂' := by
  cases ht with
  | idle =>
    cases h₁
    cases h₂
    exact .running hok (.stop .refl) (.stop .refl)
  | @waiting f s t₁ t₂ tr e hh args hS r₁ r₂ he c₁ c₂ =>
    cases h₁ with
    | uret a =>
      cases h₂
      have hA : A s a.store := he ▸ hok
      exact .running hS (resume_run r₁ c₁ _ hA) (resume_run r₂ c₂ _ hA)
  | running hS r₁ r₂ => exact running_vis hS r₁ r₂ h₁ h₂

/-- **Along the same admissible trap-free play, twin states stay twins.** -/
theorem twin_run {x₁ y₁ : (U.lts P).State} {p : List (Move U.E U.F)} (h₁ : (U.lts P).Run x₁ p y₁) :
    ∀ {x₂ y₂ : (U.lts P).State}, (U.lts P).Run x₂ p y₂ → UTwin P U A S x₁ x₂ →
      (∀ m ∈ p, UOk U A S m) → UTwin P U A S y₁ y₂ := by
  induction h₁ with
  | nil => exact fun h₂ ht _ => twin_taus_right h₂ rfl ht
  | tau hs _ ih => exact fun h₂ ht hp => ih h₂ (twin_tau_left ht hs) hp
  | vis hs _ ih =>
    intro x₂ y₂ h₂ ht hp
    obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ := LTS.Run.cons_inv h₂
    have ht' := twin_taus_right hz₁ rfl ht
    exact ih hz (twin_vis ht' hs hz₂ (hp _ List.mem_cons_self))
      (fun m hm' => hp m (List.mem_cons_of_mem _ hm'))

/-- **Determinism of the untyped store-passing strategy on admissible plays.** -/
theorem detModOn_uStrategy (hD : ∀ f : U.F.Op, S f.store → DetCfgS P A (uInv U f)) :
    DetModOn (UOk U A S) (uTraps U.X) (U.strategy P) := by
  intro c m₁ m₂ h₁ h₂ hm₁ _ _ hok
  obtain ⟨y₁, hy₁⟩ := UInstance.mem_strategy_iff.1 h₁
  obtain ⟨y₂, hy₂⟩ := UInstance.mem_strategy_iff.1 h₂
  obtain ⟨z₁, hc₁, hl₁⟩ := LTS.Run.of_append hy₁
  obtain ⟨z₂, hc₂, hl₂⟩ := LTS.Run.of_append hy₂
  have ht : UTwin P U A S z₁ z₂ := twin_run hc₁ hc₂ .idle hok
  obtain ⟨w₁, w₁', hw₁, hs₁, -⟩ := LTS.Run.cons_inv hl₁
  obtain ⟨w₂, w₂', hw₂, hs₂, -⟩ := LTS.Run.cons_inv hl₂
  exact twin_p hD (twin_taus_right hw₂ rfl (twin_taus_left hw₁ rfl ht)) hs₁ hs₂ hm₁

end Silmaril.Proofs.Wasm.Det.Shared.Untyped
