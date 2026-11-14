module

public import Silmaril.Servers.Live.Defs

@[expose] public section

/-!
# Proofs: fair runs of a total machine answer every request

* `recv_pending`, `lin_ready`: a received request is pending; a handler run makes its
  response ready;
* `pending_persist`, `ready_persist`: a pending request stays pending until its handler run,
  and a ready response stays ready until it is sent;
* **`answered`**: in a fair run of the atomic-handler server of a total machine, every request
  is eventually answered;
* `prefix_steps`: every prefix of a run is a run of `Machine.serverStep` whose observable part
  is the prefix of the observation.
-/

namespace Silmaril.Proofs.Servers.Live

open Silmaril.Servers

variable {A : Sig} {σ : Type} {M : Machine A σ} {q₀ : σ}

theorem step_some (ρ : M.IRun q₀) {n : Nat} {e : LEvent A} (he : ρ.ev n = some e) :
    M.serverStep (ρ.st n) e (ρ.st (n + 1)) := by
  rcases ρ.step n with ⟨h, _⟩ | ⟨e', h, hs⟩
  · rw [he] at h; cases h
  · rw [he] at h; cases h; exact hs

theorem recv_pending (ρ : M.IRun q₀) {n : Nat} {i : ReqId} {r : A.Req}
    (he : ρ.ev n = some (.ev (.recv i r))) : (ρ.st (n + 1)).2.pending i = some r := by
  have hs := step_some ρ he
  generalize ρ.st n = x at hs
  generalize ρ.st (n + 1) = y at hs ⊢
  obtain ⟨q, m⟩ := x
  obtain ⟨q', m'⟩ := y
  obtain ⟨_, hm⟩ := hs
  cases hm
  simp

theorem lin_ready (ρ : M.IRun q₀) {n : Nat} {i : ReqId} {r : A.Req} {s : A.Resp}
    (he : ρ.ev n = some (.lin i r s)) : (ρ.st (n + 1)).2.ready i = some s := by
  have hs := step_some ρ he
  generalize ρ.st n = x at hs
  generalize ρ.st (n + 1) = y at hs ⊢
  obtain ⟨q, m⟩ := x
  obtain ⟨q', m'⟩ := y
  obtain ⟨_, hm⟩ := hs
  cases hm
  simp

theorem pending_step (ρ : M.IRun q₀) {i : ReqId} {n : Nat} (h : (ρ.st n).2.pending i ≠ none)
    (hn : ¬ ∃ r s, ρ.ev n = some (.lin i r s)) : (ρ.st (n + 1)).2.pending i ≠ none := by
  rcases ρ.step n with ⟨_, hst⟩ | ⟨e, he, hs⟩
  · rw [hst]; exact h
  · generalize ρ.st n = x at h hs
    generalize ρ.st (n + 1) = y at hs ⊢
    obtain ⟨q, m⟩ := x
    obtain ⟨q', m'⟩ := y
    cases e with
    | ev e =>
      obtain ⟨_, hm⟩ := hs
      cases hm with
      | @recv j r _ =>
        by_cases hij : i = j
        · subst hij; simp
        · simpa [Function.update_of_ne hij] using h
      | send _ => exact h
    | lin j r s =>
      obtain ⟨_, hm⟩ := hs
      cases hm
      have hij : i ≠ j := fun hij => hn ⟨r, s, by rw [he, hij]⟩
      simpa [Function.update_of_ne hij] using h

theorem ready_step (ρ : M.IRun q₀) {i : ReqId} {n : Nat} (h : (ρ.st n).2.ready i ≠ none)
    (hn : ¬ ∃ s, ρ.ev n = some (.ev (.send i s))) : (ρ.st (n + 1)).2.ready i ≠ none := by
  rcases ρ.step n with ⟨_, hst⟩ | ⟨e, he, hs⟩
  · rw [hst]; exact h
  · generalize ρ.st n = x at h hs
    generalize ρ.st (n + 1) = y at hs ⊢
    obtain ⟨q, m⟩ := x
    obtain ⟨q', m'⟩ := y
    cases e with
    | ev e =>
      obtain ⟨_, hm⟩ := hs
      cases hm with
      | recv _ => exact h
      | @send j s _ =>
        have hij : i ≠ j := fun hij => hn ⟨s, by rw [he, hij]⟩
        simpa [Function.update_of_ne hij] using h
    | lin j r s =>
      obtain ⟨_, hm⟩ := hs
      cases hm
      by_cases hij : i = j
      · subst hij; simp
      · simpa [Function.update_of_ne hij] using h

theorem pending_persist (ρ : M.IRun q₀) {i : ReqId} {a : Nat} (h : (ρ.st a).2.pending i ≠ none) :
    ∀ k, (∀ j, a ≤ j → j < a + k → ¬ ∃ r s, ρ.ev j = some (.lin i r s)) →
      (ρ.st (a + k)).2.pending i ≠ none
  | 0, _ => h
  | k + 1, hn => by
    have ih := pending_persist ρ h k fun j h1 h2 => hn j h1 (by omega)
    exact pending_step ρ ih (hn (a + k) (by omega) (by omega))

theorem ready_persist (ρ : M.IRun q₀) {i : ReqId} {a : Nat} (h : (ρ.st a).2.ready i ≠ none) :
    ∀ k, (∀ j, a ≤ j → j < a + k → ¬ ∃ s, ρ.ev j = some (.ev (.send i s))) →
      (ρ.st (a + k)).2.ready i ≠ none
  | 0, _ => h
  | k + 1, hn => by
    have ih := ready_persist ρ h k fun j h1 h2 => hn j h1 (by omega)
    exact ready_step ρ ih (hn (a + k) (by omega) (by omega))

theorem obs_eq_some (ρ : M.IRun q₀) {n : Nat} {e : Event A} :
    ρ.obs n = some e ↔ ρ.ev n = some (.ev e) := by
  unfold Machine.IRun.obs
  split <;> simp_all

/-- **Fair runs of a total machine answer every request.** -/
theorem answered (hM : M.Total) (ρ : M.IRun q₀) (hF : ρ.Fair) : ISen.answered ρ.obs := by
  intro n i r hn
  have hev := (obs_eq_some ρ).1 hn
  refine Classical.byContradiction fun hno => ?_
  have nosend : ∀ m, n < m → ¬ ∃ s, ρ.ev m = some (.ev (.send i s)) :=
    fun m hm ⟨s, he⟩ => hno ⟨m, s, hm, (obs_eq_some ρ).2 he⟩
  have hp : (ρ.st (n + 1)).2.pending i ≠ none := by rw [recv_pending ρ hev]; simp
  have hlin : ∃ m, n + 1 ≤ m ∧ ∃ r s, ρ.ev m = some (.lin i r s) := by
    refine Classical.byContradiction fun hex => hex (hF.1 i (n + 1) fun m hm => ?_)
    have hpm : (ρ.st m).2.pending i ≠ none := by
      have := pending_persist ρ hp (m - (n + 1)) fun j h1 _ hj => hex ⟨j, h1, hj⟩
      rwa [Nat.add_sub_cancel' hm] at this
    obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hpm
    exact ⟨r', hr', hM _ r'⟩
  obtain ⟨m₁, hm₁, r', s', hl⟩ := hlin
  have hrd : (ρ.st (m₁ + 1)).2.ready i ≠ none := by rw [lin_ready ρ hl]; simp
  obtain ⟨m, hm, hsend⟩ := hF.2 i (m₁ + 1) fun m hm => by
    have := ready_persist ρ hrd (m - (m₁ + 1)) fun j h1 _ hj => nosend j (by omega) hj
    rwa [Nat.add_sub_cancel' hm] at this
  exact nosend m (by omega) hsend

theorem steps_snoc {S E : Type} {step : S → E → S → Prop} {x y z : S} {l : List E} {e : E}
    (h : Steps step x l y) (he : step y e z) : Steps step x (l ++ [e]) z := by
  induction h with
  | nil => exact .cons he (.nil _)
  | cons hs _ ih => exact .cons hs (ih he)

/-- Every prefix of a run is a run of the server's steps, observed as the prefix. -/
theorem prefix_steps (ρ : M.IRun q₀) :
    ∀ n, Steps (Machine.serverStep M) (q₀, LMon.init A) ((List.range n).filterMap ρ.ev) (ρ.st n) ∧
      LEvent.erase ((List.range n).filterMap ρ.ev) = ρ.obs.prefix n
  | 0 => by rw [ρ.init]; exact ⟨.nil _, rfl⟩
  | n + 1 => by
    obtain ⟨hs, he⟩ := prefix_steps ρ n
    simp only [ITrace.prefix, List.range_succ, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil] at he ⊢
    rcases ρ.step n with ⟨h0, hst⟩ | ⟨e, h1, hstep⟩
    · rw [h0, hst]
      have : ρ.obs n = none := by simp [Machine.IRun.obs, h0]
      rw [this]; simpa using ⟨hs, he⟩
    · rw [h1]
      refine ⟨steps_snoc hs hstep, ?_⟩
      cases e with
      | ev e =>
        have : ρ.obs n = some e := (obs_eq_some ρ).2 h1
        rw [this]; simp [LEvent.erase, List.filterMap_append] at he ⊢; exact he
      | lin i r s =>
        have : ρ.obs n = none := by simp [Machine.IRun.obs, h1]
        rw [this]; simp [LEvent.erase, List.filterMap_append] at he ⊢; exact he

end Silmaril.Proofs.Servers.Live
