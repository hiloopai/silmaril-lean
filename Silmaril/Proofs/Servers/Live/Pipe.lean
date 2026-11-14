module

public import Silmaril.Servers.Live.Defs
public import Silmaril.Servers.Core.Thms
public import Silmaril.Proofs.Servers.Live.Basic

/-!
# Proofs: fair runs of the pipelining server answer every request

* `inv_at`: the linearization monitor's invariant holds along every run;
* `req_persist`, `recv_of_req`: a received identity stays received, and was received by a step
  of the run;
* `Done`, `done_persist`, `done_of_send`: a request that has been answered stays answered;
* **`pipe_answered`**: in a weakly fair run of the pipelining server of a total machine, every
  request is eventually answered. By strong induction on the position of the request on its
  connection: the earlier requests that ever arrive are answered by induction, so after some
  instant the response stays sendable, and fairness sends it.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Live

open Silmaril.Servers

variable {A : Sig} {σ : Type} {M : Machine A σ} {q₀ : σ}

theorem serverStep_mon {x y : σ × LMon A} {e : LEvent A} (h : M.serverStep x e y) :
    LMon.Step x.2 e y.2 := by
  obtain ⟨q, m⟩ := x
  obtain ⟨q', m'⟩ := y
  cases e with
  | ev e => exact h.2
  | lin i r s => exact h.2

theorem mon_step (ρ : M.IRun q₀) (n : Nat) :
    (ρ.st (n + 1)).2 = (ρ.st n).2 ∨
      ∃ e, ρ.ev n = some e ∧ LMon.Step (ρ.st n).2 e (ρ.st (n + 1)).2 := by
  rcases ρ.step n with ⟨_, h⟩ | ⟨e, he, hs⟩
  · exact .inl (by rw [h])
  · exact .inr ⟨e, he, serverStep_mon hs⟩

theorem inv_at (ρ : M.IRun q₀) : ∀ n, (ρ.st n).2.Inv
  | 0 => by rw [ρ.init]; exact LMon.inv_init
  | n + 1 => by
    rcases mon_step ρ n with h | ⟨_, _, hs⟩
    · rw [h]; exact inv_at ρ n
    · exact (inv_at ρ n).step hs

theorem req_step {m m' : LMon A} {e : LEvent A} (hs : LMon.Step m e m') {j : ReqId}
    (h : m.req j ≠ none) : m'.req j ≠ none := by
  cases hs with
  | @recv i r _ =>
    by_cases hji : j = i
    · subst hji; simp
    · simpa [Function.update_of_ne hji] using h
  | lin _ => exact h
  | send _ => exact h

theorem recv_of_req_step {m m' : LMon A} {e : LEvent A} (hs : LMon.Step m e m') {j : ReqId}
    (h : m.req j = none) (h' : m'.req j ≠ none) : ∃ r, e = .ev (.recv j r) := by
  cases hs with
  | @recv i r _ =>
    by_cases hji : j = i
    · subst hji; exact ⟨r, rfl⟩
    · simp [Function.update_of_ne hji, h] at h'
  | lin _ => exact absurd h h'
  | send _ => exact absurd h h'

theorem req_persist (ρ : M.IRun q₀) {j : ReqId} {a : Nat} (h : (ρ.st a).2.req j ≠ none) :
    ∀ k, (ρ.st (a + k)).2.req j ≠ none
  | 0 => h
  | k + 1 => by
    have ih := req_persist ρ h k
    rcases mon_step ρ (a + k) with he | ⟨_, _, hs⟩
    · rw [← Nat.add_assoc, he]; exact ih
    · exact req_step hs ih

theorem recv_of_req (ρ : M.IRun q₀) {j : ReqId} :
    ∀ m, (ρ.st m).2.req j ≠ none → ∃ n r, n < m ∧ ρ.ev n = some (.ev (.recv j r))
  | 0, h => by rw [ρ.init] at h; exact absurd rfl h
  | m + 1, h => by
    by_cases hm : (ρ.st m).2.req j = none
    · rcases mon_step ρ m with he | ⟨e, hev, hs⟩
      · rw [he] at h; exact absurd hm h
      · obtain ⟨r, rfl⟩ := recv_of_req_step hs hm h
        exact ⟨m, r, by omega, hev⟩
    · obtain ⟨n, r, hn, he⟩ := recv_of_req ρ m hm
      exact ⟨n, r, by omega, he⟩

/-- The request `j` has been answered: received, not pending, no response ready. -/
def Done (m : LMon A) (j : ReqId) : Prop := m.req j ≠ none ∧ m.pending j = none ∧ m.ready j = none

theorem done_step {m m' : LMon A} {e : LEvent A} (hs : LMon.Step m e m') {j : ReqId}
    (h : Done m j) : Done m' j := by
  obtain ⟨hq, hp, hr⟩ := h
  refine ⟨req_step hs hq, ?_⟩
  cases hs with
  | @recv i r hreq =>
    have hji : j ≠ i := by rintro rfl; exact hq hreq
    simp [Function.update_of_ne hji, hp, hr]
  | @lin i r s hpi =>
    have hji : j ≠ i := by rintro rfl; rw [hp] at hpi; cases hpi
    simp [Function.update_of_ne hji, hp, hr]
  | @send i s _ =>
    by_cases hji : j = i
    · subst hji; simp [hp]
    · simp [Function.update_of_ne hji, hp, hr]

theorem done_persist (ρ : M.IRun q₀) {j : ReqId} {a : Nat} (h : Done (ρ.st a).2 j) :
    ∀ k, Done (ρ.st (a + k)).2 j
  | 0 => h
  | k + 1 => by
    have ih := done_persist ρ h k
    rcases mon_step ρ (a + k) with he | ⟨_, _, hs⟩
    · rw [← Nat.add_assoc, he]; exact ih
    · exact done_step hs ih

theorem done_of_send {m m' : LMon A} {j : ReqId} {s : A.Resp} (hI : m.Inv)
    (hs : LMon.Step m (.ev (.send j s)) m') : Done m' j := by
  cases hs with
  | send hr =>
    obtain ⟨r, hq⟩ := hI.2 j s hr
    have hp : m.pending j = none := by
      cases hpj : m.pending j with
      | none => rfl
      | some r' => rw [(hI.1 j r' hpj).2] at hr; cases hr
    exact ⟨by simp [hq], hp, by simp⟩

/-- **Fair runs of the pipelining server of a total machine answer every request.** -/
theorem pipe_answered (hM : M.Total) (ρ : M.PRun q₀) (hF : ρ.Fair) : ISen.answered ρ.obs := by
  suffices H : ∀ k (i : ReqId), i.seq = k → ∀ n r, ρ.obs n = some (.recv i r) →
      ∃ m s, n < m ∧ ρ.obs m = some (.send i s) from
    fun n i r hn => H i.seq i rfl n r hn
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro i hik n r hn
  have hev := (obs_eq_some ρ.toIRun).1 hn
  refine Classical.byContradiction fun hno => ?_
  have nosend : ∀ m, n < m → ¬ ∃ s, ρ.ev m = some (.ev (.send i s)) :=
    fun m hm ⟨s, he⟩ => hno ⟨m, s, hm, (obs_eq_some ρ.toIRun).2 he⟩
  have hp : (ρ.st (n + 1)).2.pending i ≠ none := by
    rw [show ρ.st = ρ.toIRun.st from rfl, recv_pending ρ.toIRun hev]; simp
  have hlin : ∃ m, n + 1 ≤ m ∧ ∃ r s, ρ.ev m = some (.lin i r s) := by
    refine Classical.byContradiction fun hex => hex (hF.1 i (n + 1) fun m hm => ?_)
    have hpm : (ρ.toIRun.st m).2.pending i ≠ none := by
      have := pending_persist ρ.toIRun hp (m - (n + 1)) fun j h1 _ hj => hex ⟨j, h1, hj⟩
      rwa [Nat.add_sub_cancel' hm] at this
    obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hpm
    exact ⟨r', hr', hM _ r'⟩
  obtain ⟨m₁, hm₁, r', s', hl⟩ := hlin
  have hrd : (ρ.toIRun.st (m₁ + 1)).2.ready i ≠ none := by
    rw [lin_ready ρ.toIRun hl]; simp
  have hready : ∀ m, m₁ + 1 ≤ m → (ρ.st m).2.ready i ≠ none := fun m hm => by
    have := ready_persist ρ.toIRun hrd (m - (m₁ + 1)) fun j h1 _ hj => nosend j (by omega) hj
    rwa [Nat.add_sub_cancel' hm] at this
  -- the earlier requests on the connection of `i` that ever arrive are answered, for good
  have hE : ∀ b, b ≤ i.seq → ∃ N, ∀ m, N ≤ m → ∀ k' < b,
      (ρ.st m).2.req ⟨i.conn, k'⟩ ≠ none →
        (ρ.st m).2.pending ⟨i.conn, k'⟩ = none ∧ (ρ.st m).2.ready ⟨i.conn, k'⟩ = none := by
    intro b
    induction b with
    | zero => exact fun _ => ⟨0, fun _ _ k' hk' => absurd hk' (Nat.not_lt_zero k')⟩
    | succ b ihb =>
      intro hb
      obtain ⟨N, hN⟩ := ihb (by omega)
      by_cases hrecv : ∃ n' r', ρ.ev n' = some (.ev (.recv ⟨i.conn, b⟩ r'))
      · obtain ⟨n', r'', hr'⟩ := hrecv
        obtain ⟨a, s, -, ha⟩ := IH b (by omega) ⟨i.conn, b⟩ rfl n' r''
          ((obs_eq_some ρ.toIRun).2 hr')
        have ha' := (obs_eq_some ρ.toIRun).1 ha
        have hd : Done (ρ.toIRun.st (a + 1)).2 ⟨i.conn, b⟩ :=
          done_of_send (inv_at ρ.toIRun a) (serverStep_mon (step_some ρ.toIRun ha'))
        refine ⟨max N (a + 1), fun m hm k' hk' hq => ?_⟩
        by_cases hkb : k' < b
        · exact hN m (by omega) k' hkb hq
        · have hkb' : k' = b := by omega
          subst hkb'
          have := done_persist ρ.toIRun hd (m - (a + 1))
          rw [Nat.add_sub_cancel' (by omega)] at this
          exact this.2
      · refine ⟨N, fun m hm k' hk' hq => ?_⟩
        by_cases hkb : k' < b
        · exact hN m hm k' hkb hq
        · have hkb' : k' = b := by omega
          subst hkb'
          obtain ⟨n', r'', -, he⟩ := recv_of_req ρ.toIRun m hq
          exact absurd ⟨n', r'', he⟩ hrecv
  obtain ⟨N, hN⟩ := hE i.seq le_rfl
  obtain ⟨m, hm, hsend⟩ := hF.2 i (max N (m₁ + 1)) fun m hm => by
    refine ⟨hready m (by omega), fun j hjc hjs hq => ?_⟩
    have hj : j = ⟨i.conn, j.seq⟩ := by cases j; simp_all
    rw [hj] at hq ⊢
    exact hN m (by omega) j.seq hjs hq
  exact nosend m (by omega) hsend

end Silmaril.Proofs.Servers.Live

namespace Silmaril.Proofs.Servers.Live

open Silmaril.Servers

variable {A : Sig} {σ : Type} {M : Machine A σ} {q₀ : σ}

/-- Every prefix of a run of the pipelining server is one of its traces. -/
theorem pipe_prefix_steps (ρ : M.PRun q₀) :
    ∀ n, Steps (Machine.pipeStep M) (q₀, LMon.init A) ((List.range n).filterMap ρ.ev) (ρ.st n)
  | 0 => by rw [ρ.init]; exact .nil _
  | n + 1 => by
    have hs := pipe_prefix_steps ρ n
    simp only [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    rcases ρ.step n with ⟨h0, hst⟩ | ⟨e, h1, hstep⟩
    · rw [h0, hst]; simpa using hs
    · rw [h1]; exact steps_snoc hs hstep

theorem pipe_prefix_tr (ρ : M.PRun q₀) (n : Nat) : (M.pipeServer q₀).Tr (ρ.obs.prefix n) :=
  ⟨_, _, pipe_prefix_steps ρ n, (prefix_steps ρ.toIRun n).2⟩

end Silmaril.Proofs.Servers.Live
