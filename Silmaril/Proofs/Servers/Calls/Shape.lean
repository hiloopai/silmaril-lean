module

public import Silmaril.Servers.Calls.Defs
public import Silmaril.Games.Play.Thms

/-!
# The shape of the plays of a component body

Every play of `ofBody h` is a sequence of completed export calls, each a complete run of `h`,
followed by at most one call in progress (`shape`). The completed calls read back by `calls`
are those runs (`calls_of_mem`).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Calls

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Calls
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName} {h : Body I X}

/-- Extending a run by one answered import call. -/
theorem _root_.Silmaril.Servers.Calls.Leads.snoc {p : BProg I} {t : List WEv} {m : (nsig I).Op}
    {k : Option (List Val) → BProg I} (hl : Leads p t (.call m k)) (n : Option (List Val)) :
    Leads p (t ++ [.req m.1.1 m.2, .imp m.1.1 m.2 n]) (k n) := by
  generalize hp : (Prog.call m k : BProg I) = p' at hl
  induction hl with
  | refl => subst hp; exact .call m k n (.refl _)
  | call m' k' n' _ ih => exact .call m' k' n' (ih hp)

/-- The events of a run are import calls and answers. -/
theorem _root_.Silmaril.Servers.Calls.Leads.not_exp {p p' : BProg I} {t : List WEv} (hl : Leads p t p') :
    ∀ e ∈ t, e.isExp = false := by
  induction hl with
  | refl => simp
  | call m k n _ ih =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · rfl
    · rfl
    · exact ih e he

/-- The events of a list of completed calls. -/
def flat (cs : List ((nsig X).Op × Call)) : List WEv := (cs.map fun x => x.2.events).flatten

/-- The trace of a play leading to the control state `c`, after the completed calls `cs`. -/
def ShapeAt (h : Body I X) (cs : List ((nsig X).Op × Call)) (t : List WEv) : CSt I X → Prop
  | .idle => t = flat cs
  | .run q p => ∃ u, Leads (h q) u p ∧ t = flat cs ++ .call q.1.1 q.2 :: u
  | .wait q m k => ∃ u, Leads (h q) u (.call m k) ∧
      t = flat cs ++ .call q.1.1 q.2 :: (u ++ [.req m.1.1 m.2])

/-- **The shape of a play.** -/
theorem shape {s : List (Move (nsig I) (nsig X))} {c : CSt I X} (hs : Reach h s c) :
    ∃ cs, (∀ x ∈ cs, Done h x.1 x.2) ∧ ShapeAt h cs (wtrace s) c := by
  induction hs with
  | nil => exact ⟨[], by simp, rfl⟩
  | @snoc s c c' o _ hc ih =>
    obtain ⟨cs, hcs, hsh⟩ := ih
    have ht : wtrace (s ++ [o]) = wtrace s ++ [wev o] := List.map_append
    cases hc with
    | ask q =>
      refine ⟨cs, hcs, [], .refl _, ?_⟩
      rw [ht, hsh]
      rfl
    | call q m k =>
      obtain ⟨u, hu, hut⟩ := hsh
      refine ⟨cs, hcs, u, hu, ?_⟩
      rw [ht, hut]
      simp [wev]
    | reply q m k n =>
      obtain ⟨u, hu, hut⟩ := hsh
      refine ⟨cs, hcs, u ++ [.req m.1.1 m.2, .imp m.1.1 m.2 n], hu.snoc n, ?_⟩
      rw [ht, hut]
      simp [wev]
    | ret q r =>
      obtain ⟨u, hu, hut⟩ := hsh
      refine ⟨cs ++ [(q, ⟨q.1.1, q.2, u, r⟩)], ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hcs x hx
        · rw [List.mem_singleton.1 hx]
          exact ⟨rfl, rfl, hu⟩
      · rw [ShapeAt, ht, hut]
        simp [flat, Call.events, wev]

/-! ## Reading back the calls -/

/-- Import events extend the call in progress. -/
theorem callsAux_inner (f : FnName) (a : List Val) (v : List WEv) {u : List WEv}
    (hu : ∀ e ∈ u, e.isExp = false) (rest : List WEv) :
    callsAux (some (f, a, v)) (u ++ rest) = callsAux (some (f, a, v ++ u)) rest := by
  induction u generalizing v with
  | nil => simp
  | cons e u ih =>
    have he := hu e List.mem_cons_self
    have hu' : ∀ e ∈ u, e.isExp = false := fun e' he' => hu e' (List.mem_cons_of_mem _ he')
    cases e with
    | req g b =>
      rw [List.cons_append, callsAux, ih _ hu']
      simp
    | imp g b r =>
      rw [List.cons_append, callsAux, ih _ hu']
      simp
    | call => exact absurd he (by simp [WEv.isExp])
    | ret => exact absurd he (by simp [WEv.isExp])

/-- A completed call is read back. -/
theorem callsAux_events (x : Option (FnName × List Val × List WEv)) (c : Call)
    (hc : ∀ e ∈ c.inner, e.isExp = false) (rest : List WEv) :
    callsAux x (c.events ++ rest) = c :: callsAux none rest := by
  rw [Call.events, List.cons_append, callsAux, List.append_assoc, callsAux_inner _ _ _ hc]
  simp [callsAux]

/-- The completed calls are read back. -/
theorem callsAux_flat (x : Option (FnName × List Val × List WEv)) (cs : List ((nsig X).Op × Call))
    (hcs : ∀ y ∈ cs, Done h y.1 y.2) (rest : List WEv) (hx : x = none ∨ cs ≠ []) :
    callsAux x (flat cs ++ rest) =
      cs.map Prod.snd ++ (if cs = [] then callsAux x rest else callsAux none rest) := by
  induction cs generalizing x with
  | nil => simp [flat]
  | cons y cs ih =>
    have hy := hcs y List.mem_cons_self
    have hcs' : ∀ y ∈ cs, Done h y.1 y.2 := fun y' hy' => hcs y' (List.mem_cons_of_mem _ hy')
    rw [show flat (y :: cs) = y.2.events ++ flat cs from rfl, List.append_assoc,
      callsAux_events _ _ hy.2.2.not_exp, ih none hcs' (.inl rfl)]
    by_cases hc : cs = [] <;> simp [hc]

/-- A call in progress is not read back. -/
theorem callsAux_part (x : Option (FnName × List Val × List WEv)) (f : FnName) (a : List Val)
    {u : List WEv} (hu : ∀ e ∈ u, e.isExp = false) :
    callsAux x (.call f a :: u) = [] := by
  rw [callsAux, ← List.append_nil u, callsAux_inner _ _ _ hu]
  rfl

/-- The completed calls of a list of completed calls. -/
theorem calls_flat_append (cs : List ((nsig X).Op × Call)) (hcs : ∀ y ∈ cs, Done h y.1 y.2)
    (rest : List WEv) : calls (flat cs ++ rest) = cs.map Prod.snd ++ calls rest := by
  rw [calls, callsAux_flat none cs hcs rest (.inl rfl)]
  by_cases hc : cs = [] <;> simp [hc, calls]

/-- **The completed calls of a play** are complete runs whose events occur in the play. -/
theorem calls_of_mem {s : List (Move (nsig I) (nsig X))} (hs : s ∈ ofBody h) :
    ∃ cs : List ((nsig X).Op × Call), (∀ x ∈ cs, Done h x.1 x.2) ∧
      (∀ x ∈ cs, ∀ e ∈ x.2.inner, e ∈ wtrace s) ∧ calls (wtrace s) = cs.map Prod.snd := by
  obtain ⟨c, hc⟩ := hs
  obtain ⟨cs, hcs, hsh⟩ := shape hc
  have hmem : ∀ rest, wtrace s = flat cs ++ rest → ∀ x ∈ cs, ∀ e ∈ x.2.inner, e ∈ wtrace s := by
    intro rest hr x hx e he
    rw [hr]
    refine List.mem_append_left _ (List.mem_flatten.2 ⟨x.2.events, List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩)
    simp [Call.events, he]
  cases c with
  | idle =>
    refine ⟨cs, hcs, hmem [] (by rw [hsh]; simp), ?_⟩
    have : wtrace s = flat cs ++ [] := by rw [hsh]; simp
    rw [this, calls_flat_append cs hcs]
    simp [calls, callsAux]
  | run q p =>
    obtain ⟨u, hu, hut⟩ := hsh
    refine ⟨cs, hcs, hmem _ hut, ?_⟩
    rw [hut, calls_flat_append cs hcs, calls, callsAux_part _ _ _ hu.not_exp]
    simp
  | wait q m k =>
    obtain ⟨u, hu, hut⟩ := hsh
    refine ⟨cs, hcs, hmem _ hut, ?_⟩
    have hu' : ∀ e ∈ u ++ [.req m.1.1 m.2], e.isExp = false := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hu.not_exp e he
      · rw [List.mem_singleton.1 he]
        rfl
    rw [hut, calls_flat_append cs hcs, calls, callsAux_part _ _ _ hu']
    simp

/-! ## Servers of components -/

/-- A member of the right list of `Forall₂` is related to a member of the left. -/
theorem forall₂_mem {α β : Type} {R : α → β → Prop} {l : List α} {t : List β}
    (h : List.Forall₂ R l t) {y : β} (hy : y ∈ t) : ∃ x ∈ l, R x y := by
  induction h with
  | nil => simp at hy
  | cons hxy _ ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨x, hx, h⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

/-- **Per-call reasoning**: if every complete run of `h` on which the host satisfies `T`
explains its exchanges by `R`, the component satisfies `each R`. -/
theorem sat_each {J : Iface} {T : WEv → Prop} {ans : Call → Bool} {obs : Call → Exch J → Prop}
    {R : J.Req → J.Resp → Prop}
    (hR : ∀ q c, Done h q c → (∀ e ∈ c.inner, T e) → ans c = true → ∀ x, obs c x → R x.1 x.2) :
    Sat (model T ans obs (ofBody h)) (each R) := by
  rintro t ⟨s, hs, hT, hF⟩ e he
  obtain ⟨c, hc, hce⟩ := forall₂_mem hF he
  obtain ⟨cs, hd, hin, hcalls⟩ := calls_of_mem hs
  rw [hcalls, List.mem_filter] at hc
  obtain ⟨hc, hans⟩ := hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  exact hR x.1 x.2 (hd x hx) (fun e' he' => hT e' (hin x hx e' he')) hans e hce

/-! ## Plays of runs -/

/-- A run of the program of a call extends a play. -/
theorem reach_of_leads {q : (nsig X).Op} {p p' : BProg I} {u : List WEv} (hl : Leads p u p')
    {s : List (Move (nsig I) (nsig X))} (hs : Reach h s (.run q p)) :
    ∃ s', Reach h s' (.run q p') ∧ wtrace s' = wtrace s ++ u := by
  induction hl generalizing s with
  | refl => exact ⟨s, hs, by simp⟩
  | call m k n _ ih =>
    have hs' := (hs.snoc (.call q m k)).snoc (.reply q m k n)
    obtain ⟨s', hr, ht⟩ := ih hs'
    refine ⟨s', hr, ?_⟩
    rw [ht]
    simp [wtrace, wev]

/-- **A complete run is a play**: its only completed call is the run. -/
theorem exists_play {q : (nsig X).Op} {u : List WEv} {r : Option (List Val)}
    (hl : Leads (h q) u (.pure r)) :
    ∃ s ∈ ofBody h, calls (wtrace s) = [⟨q.1.1, q.2, u, r⟩] ∧
      wtrace s = Call.events ⟨q.1.1, q.2, u, r⟩ := by
  obtain ⟨s, hs, ht⟩ := reach_of_leads hl (Reach.nil.snoc (.ask q))
  have hs' := hs.snoc (.ret q r)
  have ht' : wtrace (s ++ [.inr (.ans q r)]) = Call.events ⟨q.1.1, q.2, u, r⟩ := by
    have hc : wtrace (s ++ [.inr (.ans q r)]) = wtrace s ++ [wev (.inr (.ans q r))] :=
      List.map_append
    rw [hc, ht]
    simp [wtrace, wev, Call.events]
  refine ⟨_, ⟨_, hs'⟩, ?_, ht'⟩
  rw [ht', calls, ← List.append_nil (Call.events _), callsAux_events _ _ hl.not_exp]
  rfl

/-- **A single answered call is a trace** of the component read as a server. -/
theorem mem_model_single {J : Iface} {T : WEv → Prop} {ans : Call → Bool}
    {obs : Call → Exch J → Prop} {q : (nsig X).Op} {u : List WEv} {r : Option (List Val)}
    (hl : Leads (h q) u (.pure r)) (hT : ∀ e ∈ Call.events ⟨q.1.1, q.2, u, r⟩, T e)
    (ha : ans ⟨q.1.1, q.2, u, r⟩ = true) {x : Exch J} (hx : obs ⟨q.1.1, q.2, u, r⟩ x) :
    [x] ∈ model T ans obs (ofBody h) := by
  obtain ⟨s, hs, hc, ht⟩ := exists_play hl
  refine ⟨s, hs, ht ▸ hT, ?_⟩
  rw [hc, List.filter_cons_of_pos ha, List.filter_nil]
  exact .cons hx .nil

end Silmaril.Proofs.Servers.Calls
