module

public import Silmaril.Servers.State.Reduct.Defs

@[expose] public section

/-!
# Proofs: reducts of servers

* `called_map`, `returned_map`, `ids_map`: mapping requests and responses keeps the
  identities that arrived, that were answered and that ran;
* `Rel`, **`comap_reach`**: every reachable configuration of `M.comap f g` is related to one of
  `M` with the same state, and runs and histories equal after mapping;
* **`hists_comap`**, **`hists_mapResp`**.
-/

namespace Silmaril.Proofs.Servers.State.Reduct

open Silmaril.Servers.State

variable {σ Req Resp Req' Resp' : Type}

theorem called_map {f : Req → Req'} {g : Resp → Resp'} {H : Hist Req Resp} {i : Nat} :
    Called (H.map (Ev.map f g)) i ↔ Called H i := by
  constructor
  · rintro ⟨r, h⟩
    obtain ⟨e, he, hfe⟩ := List.mem_map.1 h
    cases e with
    | call j r' => cases hfe; exact ⟨r', he⟩
    | ret j s => cases hfe
  · rintro ⟨r, h⟩
    exact ⟨f r, List.mem_map.2 ⟨_, h, rfl⟩⟩

theorem returned_map {f : Req → Req'} {g : Resp → Resp'} {H : Hist Req Resp} {i : Nat} :
    Returned (H.map (Ev.map f g)) i ↔ Returned H i := by
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨e, he, hfe⟩ := List.mem_map.1 h
    cases e with
    | call j r => cases hfe
    | ret j s' => cases hfe; exact ⟨s', he⟩
  · rintro ⟨s, h⟩
    exact ⟨g s, List.mem_map.2 ⟨_, h, rfl⟩⟩

theorem ids_map (f : Req → Req') (g : Resp → Resp') (L : List (Op Req Resp)) :
    (L.map (Op.map f g)).map Op.id = L.map Op.id := by
  simp [Op.map]

/-- Configurations related along maps: the same state, runs and histories equal once mapped. -/
structure Rel (f : Req → Req') (g : Resp' → Resp) (c : Conf σ Req Resp)
    (c' : Conf σ Req' Resp') : Prop where
  st : c.st = c'.st
  log : c.log.map (Op.map f id) = c'.log.map (Op.map id g)
  hist : c.hist.map (Ev.map f id) = c'.hist.map (Ev.map id g)

theorem called_rel {f : Req → Req'} {g : Resp' → Resp} {c : Conf σ Req Resp}
    {c' : Conf σ Req' Resp'} (R : Rel f g c c') (i : Nat) :
    Called c.hist i ↔ Called c'.hist i := by
  rw [← called_map (f := f) (g := id), R.hist, called_map]

theorem returned_rel {f : Req → Req'} {g : Resp' → Resp} {c : Conf σ Req Resp}
    {c' : Conf σ Req' Resp'} (R : Rel f g c c') (i : Nat) : Returned c.hist i ↔ Returned c'.hist i := by
  rw [← returned_map (f := f) (g := id), R.hist, returned_map]

theorem logIds_rel {f : Req → Req'} {g : Resp' → Resp} {c : Conf σ Req Resp}
    {c' : Conf σ Req' Resp'} (R : Rel f g c c') : c.log.map Op.id = c'.log.map Op.id := by
  rw [← ids_map f id, R.log, ids_map]

/-- **Forward simulation of the reduct by the server.** -/
theorem comap_reach {M : Server Req' Resp'} {f : Req → Req'} {g : Resp' → Resp}
    {c : Conf (M.comap f g).σ Req Resp} (h : (M.comap f g).Reach c) :
    ∃ c' : Conf M.σ Req' Resp', M.Reach c' ∧ Rel (σ := M.σ) f g c c' := by
  induction h with
  | init => exact ⟨⟨M.init, [], []⟩, .init, ⟨rfl, rfl, rfl⟩⟩
  | @step c c₁ _ hs ih =>
    obtain ⟨c', hc', R⟩ := ih
    cases hs with
    | @arrive i r hi =>
      refine ⟨{ c' with hist := c'.hist ++ [.call i (f r)] },
        .step hc' (.arrive fun h => hi ((called_rel R i).2 h)), ⟨R.st, R.log, ?_⟩⟩
      simp only [List.map_append, R.hist]
      rfl
    | @run i r resp s' hc hi hA =>
      obtain ⟨x, hx, rfl⟩ := hA
      have hc2 : Ev.call i (f r) ∈ c'.hist := by
        have h1 : Ev.map f id (Ev.call i r) ∈ c.hist.map (Ev.map f id) := List.mem_map.2 ⟨_, hc, rfl⟩
        rw [R.hist] at h1
        obtain ⟨e, he, hfe⟩ := List.mem_map.1 h1
        cases e with
        | call j r' => cases hfe; exact he
        | ret j s => cases hfe
      refine ⟨{ c' with st := s', log := c'.log ++ [⟨i, f r, x⟩] },
        .step hc' (.run hc2 (by rw [← logIds_rel R]; exact hi) (R.st ▸ hx)),
        ⟨rfl, ?_, R.hist⟩⟩
      simp only [List.map_append, R.log]
      rfl
    | @respond o ho hnr =>
      have h1 : Op.map f id o ∈ c.log.map (Op.map f id) := List.mem_map.2 ⟨_, ho, rfl⟩
      rw [R.log] at h1
      obtain ⟨o', ho', he⟩ := List.mem_map.1 h1
      have hid : o'.id = o.id := congrArg Op.id he
      have hresp : g o'.resp = o.resp := congrArg Op.resp he
      refine ⟨{ c' with hist := c'.hist ++ [.ret o'.id o'.resp] },
        .step hc' (.respond ho' fun h => hnr (hid ▸ (returned_rel R _).2 h)), ⟨R.st, R.log, ?_⟩⟩
      simp only [List.map_append, R.hist]
      simp [Ev.map, hid, hresp]
    | @env s' hE =>
      exact ⟨{ c' with st := s' }, .step hc' (.env (R.st ▸ hE)), ⟨rfl, R.log, R.hist⟩⟩

theorem hists_comap {M : Server Req' Resp'} {f : Req → Req'} {g : Resp' → Resp}
    {H : Hist Req Resp} (h : (M.comap f g).Hists H) :
    ∃ H', M.Hists H' ∧ H.map (Ev.map f id) = H'.map (Ev.map id g) := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', R⟩ := comap_reach hc
  exact ⟨c'.hist, ⟨c', hc', rfl⟩, R.hist⟩

/-- **Backward**: every reachable configuration of `M` has a mapped one in `M.mapResp g`. -/
theorem mapResp_reach {M : Server Req Resp} {g : Resp → Resp'} {c' : Conf M.σ Req Resp}
    (h : M.Reach c') :
    ∃ c : Conf (M.mapResp g).σ Req Resp', (M.mapResp g).Reach c ∧ c.st = c'.st ∧ c.log = c'.log.map (Op.map id g) ∧
      c.hist = c'.hist.map (Ev.map id g) := by
  induction h with
  | init => exact ⟨⟨M.init, [], []⟩, .init, rfl, rfl, rfl⟩
  | @step c' c₁ _ hs ih =>
    obtain ⟨c, hc, hst, hlog, hhist⟩ := ih
    cases hs with
    | @arrive i r hi =>
      refine ⟨{ c with hist := c.hist ++ [.call i r] }, .step hc (.arrive ?_), hst, hlog, ?_⟩
      · rw [hhist, called_map]; exact hi
      · simp only [hhist, List.map_append]; rfl
    | @run i r resp s' hc' hi hA =>
      refine ⟨{ c with st := s', log := c.log ++ [⟨i, r, g resp⟩] },
        .step hc (.run ?_ ?_ ⟨resp, hst ▸ hA, rfl⟩), rfl, ?_, hhist⟩
      · rw [hhist]; exact List.mem_map.2 ⟨_, hc', rfl⟩
      · rw [hlog, ids_map]; exact hi
      · simp only [hlog, List.map_append]; rfl
    | @respond o ho hnr =>
      refine ⟨{ c with hist := c.hist ++ [.ret o.id (g o.resp)] },
        .step hc (.respond (o := Op.map id g o) ?_ ?_), hst, hlog, ?_⟩
      · rw [hlog]; exact List.mem_map.2 ⟨_, ho, rfl⟩
      · rw [hhist, returned_map]; exact hnr
      · simp only [hhist, List.map_append]; rfl
    | @env s' hE =>
      exact ⟨{ c with st := s' }, .step hc (.env (hst ▸ hE)), rfl, hlog, hhist⟩

theorem map_id_id (H : Hist Req Resp) : H.map (Ev.map id id) = H := by
  have : Ev.map (id : Req → Req) (id : Resp → Resp) = id := by funext e; cases e <;> rfl
  rw [this, List.map_id]

theorem hists_mapResp {M : Server Req Resp} {g : Resp → Resp'} {H : Hist Req Resp'} :
    (M.mapResp g).Hists H ↔ ∃ H', M.Hists H' ∧ H = H'.map (Ev.map id g) := by
  constructor
  · intro h
    obtain ⟨H', hH', he⟩ := hists_comap h
    exact ⟨H', hH', by rw [← he, map_id_id]⟩
  · rintro ⟨H', ⟨c', hc', rfl⟩, rfl⟩
    obtain ⟨c, hc, -, -, hh⟩ := mapResp_reach (g := g) hc'
    exact ⟨c, hc, hh⟩

end Silmaril.Proofs.Servers.State.Reduct
