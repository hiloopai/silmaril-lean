module

public import Silmaril.Servers.State.Traces.Defs

@[expose] public section

/-!
# Proofs: the closed host is the core's atomic-handler server

Two simulations between the host of a closed server (`Server.closed A s₀`) and the core's
atomic-handler server of the same handler, read as a machine (`Machine.server`):

* **`forward`**: every reachable configuration of the host is matched by a run of the server
  with the same state, whose observable trace is the history's trace (`arrive` is a `recv`,
  `run` a linearization point, `respond` a `send`);
* **`backward`**: every run of the server from a configuration it stands for, whose trace has
  one connection per request, is matched by a run of the host.
-/

namespace Silmaril.Proofs.Servers.State.Traces

open Silmaril.Servers Silmaril.Servers.State

variable {σ Req Resp : Type}

theorem steps_snoc {S E : Type} {step : S → E → S → Prop} {x y z : S} {l : List E} {e : E}
    (h : Steps step x l y) (he : step y e z) : Steps step x (l ++ [e]) z := by
  induction h with
  | nil => exact .cons he (.nil _)
  | cons hs _ ih => exact .cons hs (ih he)

theorem erase_snoc_ev {A : Sig} (t : List (LEvent A)) (e : Event A) :
    LEvent.erase (t ++ [.ev e]) = LEvent.erase t ++ [e] := by
  simp [LEvent.erase, List.filterMap_append]

theorem erase_snoc_lin {A : Sig} (t : List (LEvent A)) (i : ReqId) (r : A.Req) (s : A.Resp) :
    LEvent.erase (t ++ [.lin i r s]) = LEvent.erase t := by
  simp [LEvent.erase, List.filterMap_append]

theorem mem_snoc_ret {H : Hist Req Resp} {i j : Nat} {r : Req} {s : Resp}
    (h : Ev.call j r ∈ H ++ [.ret i s]) : Ev.call j r ∈ H := by
  rcases List.mem_append.1 h with h | h
  · exact h
  · simp at h

theorem returned_snoc_call {H : Hist Req Resp} {i j : Nat} {r : Req}
    (h : Returned (H ++ [.call i r]) j) : Returned H j := by
  obtain ⟨s, h⟩ := h
  rcases List.mem_append.1 h with h | h
  · exact ⟨s, h⟩
  · simp at h

theorem ne_zero_of_ne {i j : Nat} (h : j ≠ i) : (⟨j, 0⟩ : ReqId) ≠ ⟨i, 0⟩ := by
  simp [h]

theorem serverStep_ev {A : Sig} {M : Machine A σ} {q : σ} {m m' : LMon A} {e : Event A}
    (h : LMon.Step m (.ev e) m') : M.serverStep (q, m) (.ev e) (q, m') := ⟨rfl, h⟩

theorem serverStep_lin {A : Sig} {M : Machine A σ} {q q' : σ} {m m' : LMon A} {i : ReqId}
    {r : A.Req} {s : A.Resp} (hM : M q r s q') (h : LMon.Step m (.lin i r s) m') :
    M.serverStep (q, m) (.lin i r s) (q', m') := ⟨hM, h⟩

/-! ## The forward simulation -/

/-- How a linearization monitor stands for a configuration of the host. -/
structure FRel (c : Conf σ Req Resp) (m : LMon (sig Req Resp)) : Prop where
  req : ∀ j, m.req ⟨j, 0⟩ ≠ none → Called c.hist j
  pend : ∀ j r, Ev.call j r ∈ c.hist → j ∉ c.log.map Op.id → m.pending ⟨j, 0⟩ = some r
  ready : ∀ o ∈ c.log, ¬ Returned c.hist o.id → m.ready ⟨o.id, 0⟩ = some o.resp
  logCalled : ∀ o ∈ c.log, Ev.call o.id o.req ∈ c.hist

theorem forward {A : Atomic σ Req Resp} {s₀ : σ} {c : Conf (Server.closed A s₀).σ Req Resp}
    (hc : (Server.closed A s₀).Reach c) :
    ∃ (t' : List (LEvent (sig Req Resp))) (m : LMon (sig Req Resp)),
      Steps (Machine.serverStep A.machine) (s₀, LMon.init _) t' (c.st, m) ∧
      LEvent.erase t' = toTrace c.hist ∧ FRel c m := by
  induction hc with
  | init =>
    refine ⟨[], LMon.init _, .nil _, rfl, ⟨fun _ h => absurd rfl h, fun _ _ h => (nomatch h),
      fun _ h => (nomatch h), fun _ h => (nomatch h)⟩⟩
  | @step c c' _ hs ih =>
    obtain ⟨t', m, hst, her, hR⟩ := ih
    cases hs with
    | @arrive i r hnc =>
      have hreq : m.req ⟨i, 0⟩ = none := by
        cases h : m.req ⟨i, 0⟩ with
        | none => rfl
        | some _ => exact absurd (hR.req i (by simp [h])) hnc
      refine ⟨t' ++ [.ev (.recv ⟨i, 0⟩ r)], _, steps_snoc hst (serverStep_ev (LMon.Step.recv hreq)),
        by rw [erase_snoc_ev, her]; simp [toTrace, Ev.toEvent], ⟨?_, ?_, ?_, ?_⟩⟩
      · intro j hj
        by_cases hji : j = i
        · subst hji; exact ⟨r, by simp⟩
        · dsimp only at hj; rw [Function.update_of_ne (ne_zero_of_ne hji)] at hj
          obtain ⟨r', h⟩ := hR.req j hj; exact ⟨r', List.mem_append_left _ h⟩
      · intro j r' hj hnl
        dsimp only at hj hnl ⊢
        by_cases hji : j = i
        · subst hji
          rcases List.mem_append.1 hj with h | h
          · exact absurd ⟨r', h⟩ hnc
          · simp at h; subst h; simp
        · rw [Function.update_of_ne (ne_zero_of_ne hji)]
          rcases List.mem_append.1 hj with h | h
          · exact hR.pend j r' h hnl
          · simp at h; exact absurd h.1 hji
      · intro o ho hnr
        exact hR.ready o ho (fun h => hnr (by obtain ⟨s, h⟩ := h; exact ⟨s, List.mem_append_left _ h⟩))
      · intro o ho; exact List.mem_append_left _ (hR.logCalled o ho)
    | @run i r resp s' hcall hni hA =>
      have hp := hR.pend i r hcall hni
      refine ⟨t' ++ [.lin ⟨i, 0⟩ r resp], ⟨m.req, Function.update m.pending ⟨i, 0⟩ none,
        Function.update m.ready ⟨i, 0⟩ (some resp)⟩,
        steps_snoc hst (serverStep_lin (M := A.machine) hA (LMon.Step.lin hp)),
        by rw [erase_snoc_lin, her], ⟨fun j hj => hR.req j hj, ?_, ?_, ?_⟩⟩
      · intro j r' hj hnl
        dsimp only at hj hnl ⊢
        have hji : j ≠ i := fun h => hnl (by simp [h])
        rw [Function.update_of_ne (ne_zero_of_ne hji)]
        exact hR.pend j r' hj (fun h => hnl (by simp only [List.map_append]; exact List.mem_append_left _ h))
      · intro o ho hnr
        dsimp only at ho hnr ⊢
        rcases List.mem_append.1 ho with ho | ho
        · have hoi : o.id ≠ i := fun h => hni (h ▸ List.mem_map_of_mem ho)
          rw [Function.update_of_ne (ne_zero_of_ne hoi)]
          exact hR.ready o ho hnr
        · simp at ho; subst ho; simp
      · intro o ho
        rcases List.mem_append.1 ho with ho | ho
        · exact hR.logCalled o ho
        · simp at ho; subst ho; exact hcall
    | @respond o ho hnr =>
      have hrd := hR.ready o ho hnr
      refine ⟨t' ++ [.ev (.send ⟨o.id, 0⟩ o.resp)], _, steps_snoc hst (serverStep_ev (LMon.Step.send hrd)),
        by rw [erase_snoc_ev, her]; simp [toTrace, Ev.toEvent], ⟨?_, ?_, ?_, ?_⟩⟩
      · intro j hj; obtain ⟨r', h⟩ := hR.req j hj; exact ⟨r', List.mem_append_left _ h⟩
      · intro j r' hj hnl; exact hR.pend j r' (mem_snoc_ret hj) hnl
      · intro o' ho' hnr'
        dsimp only at hnr' ⊢
        have hne : o'.id ≠ o.id := fun h => hnr' ⟨o.resp, by simp [h]⟩
        rw [Function.update_of_ne (ne_zero_of_ne hne)]
        exact hR.ready o' ho' (fun ⟨s, h⟩ => hnr' ⟨s, List.mem_append_left _ h⟩)
      · intro o' ho'; exact List.mem_append_left _ (hR.logCalled o' ho')
    | env h => exact h.elim

/-! ## The backward simulation -/

/-- How a configuration of the host stands for a linearization monitor. -/
structure BRel (c : Conf σ Req Resp) (m : LMon (sig Req Resp)) : Prop where
  req : ∀ j r, Ev.call j r ∈ c.hist → m.req ⟨j, 0⟩ ≠ none
  pend : ∀ (k : ReqId) r, m.pending k = some r →
    k.seq = 0 ∧ Ev.call k.conn r ∈ c.hist ∧ k.conn ∉ c.log.map Op.id
  ready : ∀ (k : ReqId) s, m.ready k = some s →
    k.seq = 0 ∧ ∃ o ∈ c.log, o.id = k.conn ∧ o.resp = s ∧ ¬ Returned c.hist k.conn
  logCalled : ∀ o ∈ c.log, Ev.call o.id o.req ∈ c.hist
  retLog : ∀ j, Returned c.hist j → j ∈ c.log.map Op.id

theorem bRel_init (s₀ : σ) : BRel (⟨s₀, [], []⟩ : Conf σ Req Resp) (LMon.init _) :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
    fun _ h => (nomatch h), fun _ ⟨_, h⟩ => (nomatch h)⟩

theorem backward {A : Atomic σ Req Resp} {s₀ : σ} :
    ∀ {x y : σ × LMon (sig Req Resp)} {t' : List (LEvent (sig Req Resp))},
      Steps (Machine.serverStep A.machine) x t' y → ∀ c : Conf (Server.closed A s₀).σ Req Resp,
      (Server.closed A s₀).Reach c → x.1 = c.st → BRel c x.2 → OnePerConn (LEvent.erase t') →
      ∃ c' : Conf (Server.closed A s₀).σ Req Resp, (Server.closed A s₀).Reach c' ∧
        toTrace c'.hist = toTrace c.hist ++ LEvent.erase t' := by
  intro x y t' h
  induction h with
  | nil => intro c hc _ _ _; exact ⟨c, hc, by simp [LEvent.erase]⟩
  | @cons x x' y e es hs _ ih =>
    intro c hc hq hR hone
    obtain ⟨q, m⟩ := x
    obtain ⟨q', m'⟩ := x'
    change q = c.st at hq
    change BRel c m at hR
    subst hq
    cases e with
    | ev e =>
      obtain ⟨hq', hm⟩ := hs
      subst hq'
      have hone' : OnePerConn (LEvent.erase es) := fun e he => hone e (by simp [LEvent.erase] at he ⊢; exact .inr he)
      have hseq : e.id.seq = 0 := hone e (by simp [LEvent.erase])
      cases hm with
      | @recv k r hreq =>
        obtain ⟨j, k0⟩ := k
        simp only [Event.id] at hseq; subst hseq
        have hnc : ¬ Called c.hist j := fun ⟨r', h⟩ => hR.req j r' h hreq
        have hc1 : (Server.closed A s₀).Reach { c with hist := c.hist ++ [.call j r] } :=
          .step hc (Step.arrive hnc)
        have hR1 : BRel { c with hist := c.hist ++ [.call j r] }
            ⟨Function.update m.req ⟨j, 0⟩ (some r), Function.update m.pending ⟨j, 0⟩ (some r),
              m.ready⟩ := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro j' r' hj
            by_cases hji : j' = j
            · subst hji; simp
            · dsimp only; rw [Function.update_of_ne (ne_zero_of_ne hji)]
              rcases List.mem_append.1 hj with h | h
              · exact hR.req j' r' h
              · simp at h; exact absurd h.1 hji
          · intro k' r' hk
            by_cases hki : k' = ⟨j, 0⟩
            · subst hki
              simp at hk; subst hk
              refine ⟨rfl, by simp, fun hm => hnc ?_⟩
              obtain ⟨o, ho, hoj⟩ := List.mem_map.1 hm
              have := hR.logCalled o ho
              simp only at hoj; rw [hoj] at this; exact ⟨o.req, this⟩
            · dsimp only at hk; rw [Function.update_of_ne hki] at hk
              obtain ⟨h1, h2, h3⟩ := hR.pend k' r' hk
              exact ⟨h1, List.mem_append_left _ h2, h3⟩
          · intro k' s hk
            obtain ⟨h1, o, ho, h2, h3, h4⟩ := hR.ready k' s hk
            exact ⟨h1, o, ho, h2, h3, fun h => h4 (returned_snoc_call h)⟩
          · intro o ho; exact List.mem_append_left _ (hR.logCalled o ho)
          · intro j' h; exact hR.retLog j' (returned_snoc_call h)
        obtain ⟨c', hc', ht⟩ := ih { c with hist := c.hist ++ [.call j r] } hc1 rfl hR1 hone'
        exact ⟨c', hc', by rw [ht]; simp [toTrace, LEvent.erase, Ev.toEvent]⟩
      | @send k s hrd =>
        obtain ⟨j, k0⟩ := k
        simp only [Event.id] at hseq; subst hseq
        obtain ⟨_, o, ho, hoj, hos, hnr⟩ := hR.ready ⟨j, 0⟩ s hrd
        dsimp only at hoj hnr
        subst hoj hos
        have hc1 : (Server.closed A s₀).Reach { c with hist := c.hist ++ [.ret o.id o.resp] } :=
          .step hc (Step.respond ho hnr)
        have hR1 : BRel { c with hist := c.hist ++ [.ret o.id o.resp] }
            ⟨m.req, m.pending, Function.update m.ready ⟨o.id, 0⟩ none⟩ := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro j' r' hj; exact hR.req j' r' (mem_snoc_ret hj)
          · intro k' r' hk
            obtain ⟨h1, h2, h3⟩ := hR.pend k' r' hk
            exact ⟨h1, List.mem_append_left _ h2, h3⟩
          · intro k' s' hk
            by_cases hki : k' = ⟨o.id, 0⟩
            · subst hki; simp at hk
            · dsimp only at hk; rw [Function.update_of_ne hki] at hk
              obtain ⟨h1, o', ho', h2, h3, h4⟩ := hR.ready k' s' hk
              refine ⟨h1, o', ho', h2, h3, fun ⟨s'', h⟩ => ?_⟩
              rcases List.mem_append.1 h with h | h
              · exact h4 ⟨s'', h⟩
              · simp at h; obtain ⟨h, _⟩ := h
                apply hki; cases k'; simp_all
          · intro o' ho'; exact List.mem_append_left _ (hR.logCalled o' ho')
          · intro j' ⟨s'', h⟩
            rcases List.mem_append.1 h with h | h
            · exact hR.retLog j' ⟨s'', h⟩
            · simp at h; obtain ⟨rfl, _⟩ := h; exact List.mem_map_of_mem ho
        obtain ⟨c', hc', ht⟩ := ih { c with hist := c.hist ++ [.ret o.id o.resp] } hc1 rfl hR1 hone'
        exact ⟨c', hc', by rw [ht]; simp [toTrace, LEvent.erase, Ev.toEvent]⟩
    | lin k r s =>
      obtain ⟨hA, hm⟩ := hs
      cases hm with
      | lin hp =>
        obtain ⟨hk0, hcall, hni⟩ := hR.pend k r hp
        obtain ⟨j, k0⟩ := k
        dsimp only at hk0 hcall hni; subst hk0
        have hc1 : (Server.closed A s₀).Reach
            { c with st := q', log := c.log ++ [⟨j, r, s⟩] } :=
          .step hc (Step.run hcall hni hA)
        have hR1 : BRel { c with st := q', log := c.log ++ [⟨j, r, s⟩] }
            ⟨m.req, Function.update m.pending ⟨j, 0⟩ none, Function.update m.ready ⟨j, 0⟩ (some s)⟩ := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro j' r' hj; exact hR.req j' r' hj
          · intro k' r' hk
            by_cases hki : k' = ⟨j, 0⟩
            · subst hki; simp at hk
            · dsimp only at hk; rw [Function.update_of_ne hki] at hk
              obtain ⟨h1, h2, h3⟩ := hR.pend k' r' hk
              refine ⟨h1, h2, fun hm => ?_⟩
              simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
                List.mem_singleton] at hm
              rcases hm with hm | hm
              · exact h3 hm
              · apply hki; cases k'; simp_all
          · intro k' s' hk
            by_cases hki : k' = ⟨j, 0⟩
            · subst hki
              simp at hk; subst hk
              refine ⟨rfl, ⟨j, r, s⟩, by simp, rfl, rfl, fun h => hni (hR.retLog j h)⟩
            · dsimp only at hk; rw [Function.update_of_ne hki] at hk
              obtain ⟨h1, o', ho', h2, h3, h4⟩ := hR.ready k' s' hk
              exact ⟨h1, o', List.mem_append_left _ ho', h2, h3, h4⟩
          · intro o ho
            rcases List.mem_append.1 ho with ho | ho
            · exact hR.logCalled o ho
            · simp at ho; subst ho; exact hcall
          · intro j' h
            simp only [List.map_append, List.mem_append]
            exact .inl (hR.retLog j' h)
        obtain ⟨c', hc', ht⟩ := ih { c with st := q', log := c.log ++ [⟨j, r, s⟩] } hc1 rfl hR1 hone
        exact ⟨c', hc', by rw [ht]; simp [LEvent.erase]⟩

end Silmaril.Proofs.Servers.State.Traces
