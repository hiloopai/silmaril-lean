module

public import Silmaril.Servers.State.Conn.Defs
public import Silmaril.Servers.State.Traces.Thms

@[expose] public section

/-!
# Proofs: state histories read per connection

* `onConn_toTrace`; `toEvent_inj`, `mem_toTrace`;
* `Explains.congr`, **`sc_serializable`**: a sequentially consistent reordering of the trace
  has the same events, so its explanation explains the history;
* `perRequest_onId`, **`perRequest_perConn`**: the events of one request of a host with a
  fresh instance per request are a history of the component-state host (a projection of
  configurations);
* **`perConn_perRequest`**: a component-state history with one request is answered from the
  initial state.
-/

namespace Silmaril.Proofs.Servers.State.Conn

open Silmaril.Servers Silmaril.Servers.State

variable {σ Req Resp : Type}

theorem onConn_toTrace (c : Nat) (H : Hist Req Resp) :
    (toTrace H).onConn c = toTrace (H.onId c) := by
  unfold toTrace Trace.onConn Hist.onId
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  cases e <;> rfl

theorem toEvent_inj : Function.Injective (Ev.toEvent (Req := Req) (Resp := Resp)) := by
  intro a b h
  cases a <;> cases b <;> simp [Ev.toEvent] at h ⊢ <;> exact h

theorem mem_toTrace {H : Hist Req Resp} {e : Ev Req Resp} : e ∈ H ↔ e.toEvent ∈ toTrace H := by
  constructor
  · intro h; exact List.mem_map.2 ⟨e, h, rfl⟩
  · intro h
    obtain ⟨e', he', heq⟩ := List.mem_map.1 h
    exact toEvent_inj heq ▸ he'

theorem Explains.congr {A : Atomic σ Req Resp} {s₀ : σ} {H H' : Hist Req Resp}
    {L : List (Op Req Resp)} (hm : ∀ e, e ∈ H ↔ e ∈ H') (h : Explains A s₀ H L) :
    Explains A s₀ H' L :=
  ⟨h.legal, h.nodup, fun o ho => (hm _).1 (h.called o ho),
    fun i s hs => h.answered i s ((hm _).2 hs)⟩

theorem sc_serializable {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (h : Sen.sc (A.machine.Hist s₀) (toTrace H)) : Serializable A s₀ H := by
  obtain ⟨t₂, hc, hl⟩ := h
  have hmem : ∀ e, e ∈ t₂ ↔ e ∈ toTrace H := by
    intro e
    constructor
    · intro he
      have h1 : e ∈ t₂.onConn e.id.conn := List.mem_filter.2 ⟨he, by simp⟩
      rw [hc] at h1
      exact (List.mem_filter.1 h1).1
    · intro he
      have h1 : e ∈ (toTrace H).onConn e.id.conn := List.mem_filter.2 ⟨he, by simp⟩
      rw [← hc] at h1
      exact (List.mem_filter.1 h1).1
  have hone : OnePerConn t₂ := fun e he => toTrace_onePerConn H e ((hmem e).1 he)
  have ht₂ : toTrace (t₂.map ofEvent) = t₂ := by
    unfold toTrace
    rw [List.map_map]
    conv => rhs; rw [← List.map_id t₂]
    apply List.map_congr_left
    intro e he
    have h0 := hone e he
    cases e with
    | recv i r => cases i; simp only [Event.id] at h0; subst h0; rfl
    | send i s => cases i; simp only [Event.id] at h0; subst h0; rfl
  rw [← ht₂] at hl
  obtain ⟨L, hE, -⟩ := linearizable_of_lin hl
  refine ⟨L, Explains.congr (fun e => ?_) hE⟩
  rw [mem_toTrace, ht₂, hmem, ← mem_toTrace]

/-- The projection of a host with a fresh instance per request onto the request `c`. -/
theorem perRequest_onId {A : Atomic σ Req Resp} {s₀ : σ}
    {d : Conf (Server.perRequest A s₀).σ Req Resp} (h : (Server.perRequest A s₀).Reach d)
    (c : Nat) :
    ∃ e : Conf (Server.closed A s₀).σ Req Resp, (Server.closed A s₀).Reach e ∧
      e.hist = d.hist.onId c ∧ e.log = d.log.filter (·.id == c) ∧
      (c ∉ d.log.map Op.id → e.st = s₀) := by
  induction h with
  | init => exact ⟨⟨s₀, [], []⟩, .init, rfl, rfl, fun _ => rfl⟩
  | @step d d₁ _ hs ih =>
    obtain ⟨e, he, hh, hl, hst⟩ := ih
    cases hs with
    | @arrive i r hi =>
      by_cases hic : i = c
      · subst hic
        refine ⟨{ e with hist := e.hist ++ [.call i r] }, .step he (.arrive ?_), ?_, hl, hst⟩
        · rintro ⟨r', hr'⟩
          rw [hh] at hr'
          exact hi ⟨r', (List.mem_filter.1 hr').1⟩
        · simp [hh, Hist.onId, List.filter_append, Ev.id]
      · refine ⟨e, he, ?_, hl, hst⟩
        simp [hh, Hist.onId, List.filter_append, Ev.id, hic]
    | @run i r resp s' hci hi hA =>
      by_cases hic : i = c
      · subst hic
        obtain ⟨s'', hA⟩ := hA
        have hst0 : e.st = s₀ := hst hi
        refine ⟨{ e with st := s'', log := e.log ++ [⟨i, r, resp⟩] },
          .step he (.run ?_ ?_ (hst0 ▸ hA)), hh, ?_, ?_⟩
        · rw [hh]; exact List.mem_filter.2 ⟨hci, by simp [Ev.id]⟩
        · intro hm
          rw [hl] at hm
          obtain ⟨o, ho, hoi⟩ := List.mem_map.1 hm
          exact hi (List.mem_map.2 ⟨o, (List.mem_filter.1 ho).1, hoi⟩)
        · simp [hl, List.filter_append]
        · intro hn; exact absurd (List.mem_map.2 ⟨(⟨i, r, resp⟩ : Op Req Resp), by simp, rfl⟩) hn
      · refine ⟨e, he, hh, ?_, fun hn => hst fun hm => hn ?_⟩
        · simp [hl, List.filter_append, hic]
        · simp only [List.map_append, List.mem_append]; exact Or.inl hm
    | @respond o ho hnr =>
      by_cases hoc : o.id = c
      · refine ⟨{ e with hist := e.hist ++ [.ret o.id o.resp] }, .step he (.respond ?_ ?_), ?_, hl,
          hst⟩
        · rw [hl]; exact List.mem_filter.2 ⟨ho, by simp [hoc]⟩
        · rintro ⟨s, hs⟩
          rw [hh] at hs
          exact hnr ⟨s, (List.mem_filter.1 hs).1⟩
        · simp [hh, Hist.onId, List.filter_append, Ev.id, hoc]
      · refine ⟨e, he, ?_, hl, hst⟩
        simp [hh, Hist.onId, List.filter_append, Ev.id, hoc]
    | @env s' hE => exact hE.elim

theorem perRequest_perConn (A : Atomic σ Req Resp) (s₀ : σ) :
    (Server.perRequest A s₀).model.Refines (Model.perConn (Server.closed A s₀).model) := by
  rintro _ ⟨H, ⟨d, hd, rfl⟩, rfl⟩
  refine ⟨?_, fun c => ?_⟩
  · have h := (closed_model_tr_iff (A.fresh s₀) () (toTrace d.hist)).1 ⟨d.hist, ⟨d, hd, rfl⟩, rfl⟩
    exact Sen.wf_of_lin (Machine.server_sat_lin _ _ _ h.1)
  · obtain ⟨e, he, hh, -, -⟩ := perRequest_onId hd c
    exact ⟨e.hist, ⟨e, he, rfl⟩, by rw [hh, onConn_toTrace]⟩

theorem perConn_perRequest {A : Atomic σ Req Resp} {s₀ : σ} {t : Trace (sig Req Resp)}
    (h : (Model.perConn (Server.closed A s₀).model).Tr t) (hone : OnePerConn t) :
    (Server.perRequest A s₀).model.Tr t := by
  obtain ⟨hw, hc⟩ := h
  suffices key : Sen.atomic (A := sig Req Resp) (fun r s => ∃ s', A s₀ r s s') t from
    (closed_model_tr_iff (A.fresh s₀) () t).2
      ⟨(Machine.server_ofRel_tr_iff (A := sig Req Resp) _ t).2 ⟨hw, key⟩, hone⟩
  rintro ⟨c, q⟩ r s hr hs
  have hq : q = 0 := hone _ hr
  subst hq
  obtain ⟨Hu, ⟨e, he, rfl⟩, hu⟩ := hc c
  have hin : ∀ x : Event (sig Req Resp), x ∈ t → x.id = ⟨c, 0⟩ → x ∈ toTrace e.hist := by
    intro x hx hxi
    rw [hu]; exact List.mem_filter.2 ⟨hx, by simp [hxi]⟩
  have hcall : Ev.call c r ∈ e.hist := mem_toTrace.2 (hin _ hr rfl)
  have hret : Ev.ret c s ∈ e.hist := mem_toTrace.2 (hin _ hs rfl)
  have hid : ∀ x ∈ e.hist, x.id = c := by
    intro x hx
    have h1 := mem_toTrace.1 hx
    rw [hu] at h1
    have h2 := (List.mem_filter.1 h1).2
    cases x <;> simpa [Ev.toEvent, Event.id, Ev.id] using h2
  obtain ⟨L, hE, -⟩ := closed_linearizable A s₀ e.hist ⟨e, he, rfl⟩
  obtain ⟨o, hoL, hoid, hores⟩ := hE.answered c s hret
  have hwf := Server.sat_wellFormed (Server.closed A s₀) e.hist ⟨e, he, rfl⟩
  have hreq : o.req = r := hwf.callUnique c _ _ (hoid ▸ hE.called o hoL) hcall
  have hLid : ∀ x ∈ L, x.id = c := fun x hx => hid _ (hE.called x hx)
  have hL : L = [o] := by
    match L, hoL, hE.nodup, hLid with
    | [a], hoL, _, _ => rw [List.mem_singleton.1 hoL]
    | a :: b :: L', _, hn, hLid' =>
      exfalso
      have ha := hLid' a (by simp)
      have hb := hLid' b (by simp)
      simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn
      exact hn.1 (Or.inl (ha.trans hb.symm))
  obtain ⟨_, hleg⟩ := hE.legal
  rw [hL] at hleg
  obtain ⟨s', hA, -⟩ := hleg
  exact ⟨s', hreq ▸ hores ▸ hA⟩

end Silmaril.Proofs.Servers.State.Conn
