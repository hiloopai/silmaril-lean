module

public import Silmaril.Http.State.Defs

@[expose] public section

/-!
# Proofs: hosts of atomic handlers are linearizable

* `Legal.snoc`, `Legal.mem`, `Legal.map`: sequential runs grow at the end, each operation is a
  handler run, and runs map along simulations;
* `pair_sublist_snoc`, `retBeforeCall_snoc`: the real-time order of a history with one more
  event;
* `LinInv`, **`linInv_of_reach`**: the invariant of reachable configurations of a host with an
  abstraction: the log of runs is a legal run of the abstract specification ending in the
  abstraction of the current state, and it explains the history in real-time order;
* `wellFormed_of_reach`: reachable histories are well formed;
* `refines_closed`: a server with an abstraction refines the closed server of the abstract
  specification (history inclusion, by a forward simulation of hosts).
-/

namespace Silmaril.Proofs.Http.State

open scoped List
open Silmaril.Http.State

variable {σ τ Req Resp : Type}


theorem legal_snoc {A : Atomic σ Req Resp} {s t u : σ} {L : List (Op Req Resp)}
    {o : Op Req Resp} (h : Legal A s L t) (ho : A t o.req o.resp u) : Legal A s (L ++ [o]) u := by
  induction L generalizing s with
  | nil => cases h; exact ⟨u, ho, rfl⟩
  | cons x L ih => obtain ⟨s', h1, h2⟩ := h; exact ⟨s', h1, ih h2⟩

theorem legal_mem {A : Atomic σ Req Resp} {s t : σ} {L : List (Op Req Resp)}
    (h : Legal A s L t) {o : Op Req Resp} (ho : o ∈ L) : ∃ u u', A u o.req o.resp u' := by
  induction L generalizing s with
  | nil => cases ho
  | cons x L ih =>
    obtain ⟨s', h1, h2⟩ := h
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨_, _, h1⟩
    · exact ih h2 ho

theorem pair_sublist_snoc {α : Type} {u v e : α} {H : List α} (h : [u, v] <+ H ++ [e]) :
    [u, v] <+ H ∨ (v = e ∧ u ∈ H) := by
  obtain ⟨l₁, l₂, heq, h1, h2⟩ := List.sublist_append_iff.1 h
  rcases l₂ with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp at heq; subst heq; exact .inl h1
  · have hx : x = e := by simpa using h2.subset (List.mem_singleton_self x)
    subst hx
    rcases l₁ with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at heq
    · simp at heq; obtain ⟨rfl, rfl⟩ := heq; exact .inr ⟨rfl, List.singleton_sublist.1 h1⟩
    · simp at heq
  · have := h2.length_le; simp at this

theorem retBeforeCall_snoc {H : Hist Req Resp} {e : Ev Req Resp} {a b : Nat}
    (h : RetBeforeCall (H ++ [e]) a b) :
    RetBeforeCall H a b ∨ ((∃ r, e = .call b r) ∧ Returned H a) := by
  obtain ⟨s, r, h⟩ := h
  rcases pair_sublist_snoc h with h | ⟨rfl, hu⟩
  · exact .inl ⟨s, r, h⟩
  · exact .inr ⟨⟨r, rfl⟩, s, hu⟩

/-- The invariant of a reachable configuration. -/
structure LinInv {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) (c : Conf M.σ Req Resp) : Prop where
  inv : F.inv c.st
  legal : Legal B t₀ c.log (F.α c.st)
  nodup : (c.log.map Op.id).Nodup
  called : ∀ o ∈ c.log, Ev.call o.id o.req ∈ c.hist
  answered : ∀ i s, Ev.ret i s ∈ c.hist → ∃ o ∈ c.log, o.id = i ∧ o.resp = s
  realTime : RealTime c.hist c.log

theorem linInv_of_reach {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) {c : Conf M.σ Req Resp} (hc : M.Reach c) : LinInv F c := by
  induction hc with
  | init =>
    refine ⟨F.inv_init, ?_, List.nodup_nil, by simp, by simp, ?_⟩
    · show t₀ = F.α M.init; exact F.α_init.symm
    · intro a b h; obtain ⟨_, _, h⟩ := h; simp at h
  | step _ hs ih =>
    cases hs with
    | @arrive i r hi =>
      refine ⟨ih.inv, ih.legal, ih.nodup, fun o ho => List.mem_append_left _ (ih.called o ho),
        fun j s hj => ?_, fun a b h y hy hyb => ?_⟩
      · rcases List.mem_append.1 hj with hj | hj
        · exact ih.answered j s hj
        · simp at hj
      · rcases retBeforeCall_snoc h with h | ⟨⟨r', hr⟩, -⟩
        · exact ih.realTime a b h y hy hyb
        · cases hr; exact absurd ⟨y.req, hyb ▸ ih.called y hy⟩ hi
    | @run i r resp s' hcall hfresh hA =>
      refine ⟨F.inv_handler _ _ _ _ ih.inv hA, legal_snoc ih.legal (F.sim _ _ _ _ ih.inv hA), ?_,
        fun o ho => ?_, fun j s hj => ?_, fun a b h y hy hyb => ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨ih.nodup, by simp, ?_⟩
        intro x hx y hy; simp at hy; subst hy; rintro rfl; exact hfresh hx
      · rcases List.mem_append.1 ho with ho | ho
        · exact ih.called o ho
        · simp at ho; subst ho; exact hcall
      · obtain ⟨o, ho, h1, h2⟩ := ih.answered j s hj
        exact ⟨o, List.mem_append_left _ ho, h1, h2⟩
      · rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨x, z, h1, h2, h3⟩ := ih.realTime a b h y hy hyb
          exact ⟨x, z, h1, h2, h3.trans (List.sublist_append_left _ _)⟩
        · simp at hy; subst hy
          obtain ⟨s, r', h⟩ := h
          obtain ⟨o, ho, h1, -⟩ := ih.answered a s (List.singleton_sublist.1 ((List.Sublist.cons_cons _ (List.nil_sublist _)).trans h))
          exact ⟨o, _, h1, hyb, (List.singleton_sublist.2 ho).append (List.Sublist.refl _)⟩
    | @respond o ho hret =>
      refine ⟨ih.inv, ih.legal, ih.nodup, fun o' ho' => List.mem_append_left _ (ih.called o' ho'),
        fun j s hj => ?_, fun a b h y hy hyb => ?_⟩
      · rcases List.mem_append.1 hj with hj | hj
        · exact ih.answered j s hj
        · simp at hj; obtain ⟨rfl, rfl⟩ := hj; exact ⟨o, ho, rfl, rfl⟩
      · rcases retBeforeCall_snoc h with h | ⟨⟨r', hr⟩, -⟩
        · exact ih.realTime a b h y hy hyb
        · cases hr
    | @env s' hE =>
      refine ⟨F.inv_env _ _ ih.inv hE, ?_, ih.nodup, ih.called, ih.answered, ih.realTime⟩
      dsimp only; rw [F.env_hidden _ _ ih.inv hE]; exact ih.legal


theorem sat_linearizable {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.Sat (Linearizable B t₀) := by
  rintro H ⟨c, hc, rfl⟩
  have I := linInv_of_reach F hc
  exact ⟨c.log, ⟨⟨_, I.legal⟩, I.nodup, I.called, I.answered⟩, I.realTime⟩

theorem wellFormed_of_reach {M : Server Req Resp} {c : Conf M.σ Req Resp} (hc : M.Reach c) :
    WellFormed c.hist ∧ ∀ o ∈ c.log, Ev.call o.id o.req ∈ c.hist := by
  induction hc with
  | init => exact ⟨⟨by simp, by simp, by simp⟩, by simp⟩
  | step _ hs ih =>
    obtain ⟨⟨hcu, hru, hrc⟩, hl⟩ := ih
    cases hs with
    | @arrive i r hi =>
      refine ⟨⟨fun j a b ha hb => ?_, fun j a b ha hb => ?_, fun j s hj => ?_⟩,
        fun o ho => List.mem_append_left _ (hl o ho)⟩
      · simp only [List.mem_append, List.mem_singleton, Ev.call.injEq] at ha hb
        rcases ha with ha | ⟨rfl, rfl⟩ <;> rcases hb with hb | ⟨hj, rfl⟩
        · exact hcu j a b ha hb
        · subst hj; exact absurd ⟨a, ha⟩ hi
        · exact absurd ⟨b, hb⟩ hi
        · rfl
      · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at ha hb
        exact hru j a b ha hb
      · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hj
        obtain ⟨r', h⟩ := hrc j s hj; exact ⟨r', List.mem_append_left _ h⟩
    | @run i r resp s' hcall hfresh hA =>
      refine ⟨⟨hcu, hru, hrc⟩, fun o ho => ?_⟩
      rcases List.mem_append.1 ho with ho | ho
      · exact hl o ho
      · simp at ho; subst ho; exact hcall
    | @respond o ho hret =>
      refine ⟨⟨fun j a b ha hb => ?_, fun j a b ha hb => ?_, fun j s hj => ?_⟩,
        fun o ho => List.mem_append_left _ (hl o ho)⟩
      · simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at ha hb
        exact hcu j a b ha hb
      · simp only [List.mem_append, List.mem_singleton, Ev.ret.injEq] at ha hb
        rcases ha with ha | ⟨rfl, rfl⟩ <;> rcases hb with hb | ⟨hj, rfl⟩
        · exact hru j a b ha hb
        · subst hj; exact absurd ⟨a, ha⟩ hret
        · exact absurd ⟨b, hb⟩ hret
        · rfl
      · simp only [List.mem_append, List.mem_singleton, Ev.ret.injEq] at hj
        rcases hj with hj | ⟨rfl, rfl⟩
        · obtain ⟨r', h⟩ := hrc j s hj; exact ⟨r', List.mem_append_left _ h⟩
        · exact ⟨o.req, List.mem_append_left _ (hl o ho)⟩
    | @env s' hE => exact ⟨⟨hcu, hru, hrc⟩, hl⟩

theorem linearizable_answer {B : Atomic τ Req Resp} {t₀ : τ} {H : Hist Req Resp}
    (hw : WellFormed H) (h : Linearizable B t₀ H) {i : Nat} {r : Req} {s : Resp}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ t t', B t r s t' := by
  obtain ⟨L, ⟨⟨u, hL⟩, -, hcalled, hans⟩, -⟩ := h
  obtain ⟨o, ho, rfl, rfl⟩ := hans i s hr
  have := hw.callUnique _ _ _ (hcalled o ho) hc
  subst this
  exact legal_mem hL ho

theorem legal_map {A : Atomic σ Req Resp} {B : Atomic τ Req Resp} (α : σ → τ)
    (hsim : ∀ s r resp s', A s r resp s' → B (α s) r resp (α s')) {s t : σ}
    {L : List (Op Req Resp)} (h : Legal A s L t) : Legal B (α s) L (α t) := by
  induction L generalizing s with
  | nil => cases h; rfl
  | cons x L ih => obtain ⟨s', h1, h2⟩ := h; exact ⟨α s', hsim _ _ _ _ h1, ih h2⟩

theorem linearizable_map {A : Atomic σ Req Resp} {B : Atomic τ Req Resp} (α : σ → τ)
    (hsim : ∀ s r resp s', A s r resp s' → B (α s) r resp (α s')) {s₀ : σ} {H : Hist Req Resp}
    (h : Linearizable A s₀ H) : Linearizable B (α s₀) H := by
  obtain ⟨L, ⟨⟨u, hL⟩, h1, h2, h3⟩, h4⟩ := h
  exact ⟨L, ⟨⟨α u, legal_map α hsim hL⟩, h1, h2, h3⟩, h4⟩


theorem reach_inv {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) {c : Conf M.σ Req Resp} (hc : M.Reach c) : F.inv c.st :=
  (linInv_of_reach F hc).inv

theorem sat_wellFormed (M : Server Req Resp) : M.Sat WellFormed := by
  rintro H ⟨c, hc, rfl⟩; exact (wellFormed_of_reach hc).1

theorem sat_answer {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) {H : Hist Req Resp} (hH : M.Hists H) {i : Nat} {r : Req}
    {s : Resp} (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ t t', B t r s t' :=
  linearizable_answer (sat_wellFormed M H hH) (sat_linearizable F H hH) hc hr

theorem perRequest_answer {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (hH : (Server.perRequest A s₀).Hists H) {i : Nat} {r : Req} {s : Resp}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ s', A s₀ r s s' := by
  obtain ⟨_, _, h⟩ := sat_answer (Abstraction.closed (A.fresh s₀) ()) hH hc hr
  exact h

theorem refines_closed {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.Refines (Server.closed B t₀) := by
  have key : ∀ c, M.Reach c →
      F.inv c.st ∧ (Server.closed B t₀).Reach ⟨F.α c.st, c.log, c.hist⟩ := by
    intro c hc
    induction hc with
    | init => refine ⟨F.inv_init, ?_⟩; rw [F.α_init]; exact .init
    | step _ hs ih =>
      obtain ⟨hi, hr⟩ := ih
      cases hs with
      | arrive h => exact ⟨hi, .step hr (Step.arrive h)⟩
      | run h1 h2 h3 =>
        exact ⟨F.inv_handler _ _ _ _ hi h3, .step hr (Step.run h1 h2 (F.sim _ _ _ _ hi h3))⟩
      | respond h1 h2 => exact ⟨hi, .step hr (Step.respond h1 h2)⟩
      | env h =>
        refine ⟨F.inv_env _ _ hi h, ?_⟩
        dsimp only; rw [F.env_hidden _ _ hi h]; exact hr
  rintro H ⟨c, hc, rfl⟩
  exact ⟨_, (key c hc).2, rfl⟩

end Silmaril.Proofs.Http.State
