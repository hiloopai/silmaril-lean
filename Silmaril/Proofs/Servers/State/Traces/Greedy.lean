module

public import Silmaril.Servers.State.Traces.Defs

@[expose] public section

/-!
# Proofs: a linearizable orderly history is a history of the closed host

The converse of `Abstraction.sat_linearizable` for closed servers: if a sequential run `L` of
`A` explains the orderly history `H` in real-time order, the host of `A` can produce `H`. The
host replays `H` event by event: a request arrives as in `H`; before the response to `i` is
issued, the host runs the operations of `L` up to the one of `i` (each of them has arrived,
by the real-time order), then responds.

* `legal_append`, `pair_sublist_contra`, `inj_of_nodup_map`: lemmas on runs and lists;
* `run_ops`: the host runs a list of arrived operations one after another;
* **`hists_of_linearizable`**.
-/

namespace Silmaril.Proofs.Servers.State.Traces

open scoped List
open Silmaril.Servers.State

variable {σ Req Resp : Type}

theorem legal_append {A : Atomic σ Req Resp} :
    ∀ {s s'' : σ} {X Y : List (Op Req Resp)}, Legal A s (X ++ Y) s'' →
      ∃ s', Legal A s X s' ∧ Legal A s' Y s''
  | s, _, [], _, h => ⟨s, rfl, h⟩
  | _, _, _ :: _, _, h =>
    let ⟨s1, h1, h2⟩ := h
    let ⟨s', a, b⟩ := legal_append h2
    ⟨s', ⟨s1, h1, a⟩, b⟩

theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => nomatch hx
  | a :: l, h, x, hx, y, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with hx' | hx' <;> rcases List.mem_cons.1 hy with hy' | hy'
    · rw [hx', hy']
    · subst hx'; exact absurd (hxy ▸ List.mem_map_of_mem hy') h.1
    · subst hy'; exact absurd (hxy.symm ▸ List.mem_map_of_mem hx') h.1
    · exact inj_of_nodup_map h.2 x hx' y hy' hxy

theorem nodup_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.2 ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_nodup_map h.2⟩

theorem pair_sublist_contra {α : Type} {X Y : List α} {a b : α} (hn : (X ++ a :: Y).Nodup)
    (h : [a, b] <+ X ++ a :: Y) (hb : b ∈ X ++ [a]) : False := by
  rw [List.nodup_append, List.nodup_cons] at hn
  obtain ⟨_, ⟨haY, _⟩, hdisj⟩ := hn
  have haX : a ∉ X := fun hx => hdisj a hx a List.mem_cons_self rfl
  obtain ⟨l₁, l₂, heq, h1, h2⟩ := List.sublist_append_iff.1 h
  rcases l₁ with _ | ⟨x, l₁⟩
  · simp only [List.nil_append] at heq
    subst heq
    have hbY : b ∈ Y := List.singleton_sublist.1 (List.cons_sublist_cons.1 h2)
    rcases List.mem_append.1 hb with hb | hb
    · exact hdisj b hb b (List.mem_cons_of_mem _ hbY) rfl
    · rw [List.mem_singleton.1 hb] at hbY; exact haY hbY
  · simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, _⟩ := heq
    exact haX (h1.subset List.mem_cons_self)

/-- The closed host runs a list of arrived operations one after another. -/
theorem run_ops (A : Atomic σ Req Resp) (s₀ : σ) :
    ∀ (X : List (Op Req Resp)) {c : Conf σ Req Resp} {Y : List (Op Req Resp)} {e : σ},
      (Server.closed A s₀).Reach c → Legal A c.st (X ++ Y) e →
      ((c.log ++ X).map Op.id).Nodup → (∀ x ∈ X, Ev.call x.id x.req ∈ c.hist) →
      ∃ c' : Conf σ Req Resp, (Server.closed A s₀).Reach c' ∧ c'.hist = c.hist ∧
        c'.log = c.log ++ X ∧ Legal A c'.st Y e
  | [], c, _, _, hc, hl, _, _ => ⟨c, hc, rfl, by simp, hl⟩
  | x :: X, c, Y, e, hc, hl, hn, hx => by
    obtain ⟨s1, h1, h2⟩ := hl
    have hni : x.id ∉ c.log.map Op.id := by
      intro hm
      rw [List.map_append, List.nodup_append] at hn
      exact hn.2.2 _ hm _ (by simp) rfl
    have hc1 : (Server.closed A s₀).Reach { c with st := s1, log := c.log ++ [x] } :=
      .step hc (Step.run (i := x.id) (r := x.req) (resp := x.resp)
        (hx x List.mem_cons_self) hni h1)
    obtain ⟨c', hc', hh, hlog, hl'⟩ := run_ops A s₀ X hc1 h2 (by simpa using hn)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    exact ⟨c', hc', hh, by simp [hlog], hl'⟩

/-- **The greedy replay**: the host reproduces the rest `Q` of the history. -/
theorem greedy (A : Atomic σ Req Resp) (s₀ : σ) {H : Hist Req Resp} {L : List (Op Req Resp)}
    (hE : Explains A s₀ H L) (hRT : RealTime H L) :
    ∀ (Q : Hist Req Resp) {c : Conf σ Req Resp} {R : List (Op Req Resp)} {e : σ},
      (Server.closed A s₀).Reach c → H = c.hist ++ Q → c.log ++ R = L → Legal A c.st R e →
      Orderly c.hist Q → ∃ c' : Conf σ Req Resp, (Server.closed A s₀).Reach c' ∧ c'.hist = H
  | [], c, _, _, hc, hH, _, _, _ => ⟨c, hc, by simp [hH]⟩
  | .call i r :: Q, c, R, e, hc, hH, hL, hl, ho => by
    obtain ⟨hnc, ho⟩ := ho
    exact greedy A s₀ hE hRT Q (c := { c with hist := c.hist ++ [.call i r] })
      (.step hc (Step.arrive hnc)) (by simp [hH]) hL hl ho
  | .ret i s :: Q, c, R, e, hc, hH, hL, hl, ho => by
    obtain ⟨_, hnr, ho⟩ := ho
    have hnL : (L.map Op.id).Nodup := hE.nodup
    obtain ⟨o, hoL, hoi, hos⟩ := hE.answered i s (by rw [hH]; simp)
    subst hoi hos
    by_cases hlog : o ∈ c.log
    · exact greedy A s₀ hE hRT Q (c := { c with hist := c.hist ++ [.ret o.id o.resp] })
        (.step hc (Step.respond hlog hnr)) (by simp [hH]) hL hl ho
    · have hoR : o ∈ R := by
        rw [← hL] at hoL
        rcases List.mem_append.1 hoL with h | h
        · exact absurd h hlog
        · exact h
      obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hoR
      have hLeq : L = (c.log ++ R₁) ++ o :: R₂ := by rw [← hL]; simp
      have hnodup : L.Nodup := nodup_of_nodup_map hnL
      have hcalls : ∀ x ∈ R₁ ++ [o], Ev.call x.id x.req ∈ c.hist := by
        intro x hx
        have hxL : x ∈ L := by
          rw [hLeq]; rcases List.mem_append.1 hx with hx | hx
          · simp [hx]
          · rw [List.mem_singleton.1 hx]; simp
        have hcall := hE.called x hxL
        rw [hH] at hcall
        rcases List.mem_append.1 hcall with h | h
        · exact h
        · exfalso
          rcases List.mem_cons.1 h with h | h
          · cases h
          · have hrb : RetBeforeCall H o.id x.id := by
              refine ⟨o.resp, x.req, ?_⟩
              rw [hH]
              exact ((List.singleton_sublist.2 h).cons_cons _).trans (List.sublist_append_right _ _)
            obtain ⟨a, b, ha, hb, hab⟩ := hRT o.id x.id hrb x hxL rfl
            have haL : a ∈ L := hab.subset (by simp)
            have hbL : b ∈ L := hab.subset (by simp)
            have ha' : a = o := inj_of_nodup_map hnL a haL o hoL ha
            have hb' : b = x := inj_of_nodup_map hnL b hbL x hxL hb
            subst ha' hb'
            rw [hLeq] at hab hnodup
            exact pair_sublist_contra hnodup hab (by rw [List.append_assoc]; exact List.mem_append_right _ hx)
      have hn' : ((c.log ++ (R₁ ++ [o])).map Op.id).Nodup := by
        have : (c.log ++ (R₁ ++ [o])) <+ L := by
          rw [hLeq]; simp
        exact hnL.sublist (this.map _)
      obtain ⟨c', hc', hh, hlog', hl'⟩ :=
        run_ops A s₀ (R₁ ++ [o]) (Y := R₂) hc (by simpa using hl) hn' hcalls
      have hoc' : o ∈ c'.log := by rw [hlog']; simp
      have hnr' : ¬ Returned c'.hist o.id := by rw [hh]; exact hnr
      exact greedy A s₀ hE hRT Q (c := { c' with hist := c'.hist ++ [.ret o.id o.resp] })
        (.step hc' (Step.respond hoc' hnr')) (by simp [hH, hh]) (by rw [hlog', hLeq]; simp)
        hl' (by rw [hh]; exact ho)

/-- **A linearizable orderly history is a history of the closed host.** -/
theorem hists_of_linearizable {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (ho : Orderly [] H) (h : Linearizable A s₀ H) : (Server.closed A s₀).Hists H := by
  obtain ⟨L, hE, hRT⟩ := h
  obtain ⟨e, hl⟩ := hE.legal
  obtain ⟨c, hc, hh⟩ := greedy A s₀ hE hRT H (c := ⟨s₀, [], []⟩) .init (by simp) (by simp) hl ho
  exact ⟨c, hc, hh⟩

end Silmaril.Proofs.Servers.State.Traces
