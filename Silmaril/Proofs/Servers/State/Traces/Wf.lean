module

public import Silmaril.Servers.State.Traces.Defs

@[expose] public section

/-!
# Proofs: well-formed core traces of histories are orderly

* `toTrace_injective`: the one-connection-per-request reading loses nothing;
* `toTrace_onePerConn`: its traces have one connection per request;
* **`orderly_of_wf`**: a history whose core trace is well formed is orderly, event by event.
-/

namespace Silmaril.Proofs.Servers.State.Traces

open Silmaril.Servers Silmaril.Servers.State

variable {Req Resp : Type}

theorem toEvent_injective : Function.Injective (Ev.toEvent (Req := Req) (Resp := Resp)) := by
  intro a b h
  cases a <;> cases b <;> simp [Ev.toEvent] at h ⊢ <;> exact h

theorem toTrace_injective : Function.Injective (toTrace (Req := Req) (Resp := Resp)) := by
  intro a
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons _ _ => simp [toTrace] at h
  | cons x a ih => intro b h; cases b with
    | nil => simp [toTrace] at h
    | cons y b =>
      simp only [toTrace, List.map_cons, List.cons.injEq] at h
      rw [toEvent_injective h.1, ih h.2]

theorem toTrace_onePerConn (H : Hist Req Resp) : OnePerConn (toTrace H) := by
  intro e he
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 he
  cases x <;> rfl

theorem toTrace_append (H H' : Hist Req Resp) : toTrace (H ++ H') = toTrace H ++ toTrace H' :=
  List.map_append

theorem called_append_iff {P : Hist Req Resp} {e : Ev Req Resp} {j : Nat} :
    Called (P ++ [e]) j ↔ Called P j ∨ ∃ r, e = .call j r := by
  simp only [Called, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨r, h | h⟩
    · exact .inl ⟨r, h⟩
    · exact .inr ⟨r, h.symm⟩
  · rintro (⟨r, h⟩ | ⟨r, h⟩)
    · exact ⟨r, .inl h⟩
    · exact ⟨r, .inr h.symm⟩

theorem returned_append_iff {P : Hist Req Resp} {e : Ev Req Resp} {j : Nat} :
    Returned (P ++ [e]) j ↔ Returned P j ∨ ∃ s, e = .ret j s := by
  simp only [Returned, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨r, h | h⟩
    · exact .inl ⟨r, h⟩
    · exact .inr ⟨r, h.symm⟩
  · rintro (⟨r, h⟩ | ⟨r, h⟩)
    · exact ⟨r, .inl h⟩
    · exact ⟨r, .inr h.symm⟩

/-- How a well-formedness monitor stands for a history. -/
structure WRel (w : WMon (sig Req Resp)) (P : Hist Req Resp) : Prop where
  called : ∀ i, Called P i → w.req ⟨i, 0⟩ ≠ none
  open_ : ∀ i r, w.open_ ⟨i, 0⟩ = some r → Called P i ∧ ¬ Returned P i
  returned : ∀ i, Returned P i → Called P i

theorem wRel_init : WRel (WMon.init (sig Req Resp)) [] :=
  ⟨fun _ ⟨_, h⟩ => (nomatch h), fun _ _ h => (nomatch h), fun _ ⟨_, h⟩ => (nomatch h)⟩

theorem orderly_of_wsteps : ∀ (Q : Hist Req Resp) {P : Hist Req Resp} {w w' : WMon (sig Req Resp)},
    Steps WMon.Step w (toTrace Q) w' → WRel w P → Orderly P Q
  | [], _, _, _, _, _ => trivial
  | .call i r :: Q, P, w, w', h, hR => by
    cases h with
    | cons hs h' =>
      cases hs with
      | recv hreq =>
        have hnc : ¬ Called P i := fun hc => hR.called i hc hreq
        refine ⟨hnc, orderly_of_wsteps Q h' ⟨fun j hj => ?_, fun j r' hj => ?_, fun j hj => ?_⟩⟩
        · by_cases hji : j = i
          · subst hji; simp
          · have hne : (⟨j, 0⟩ : ReqId) ≠ ⟨i, 0⟩ := by simp [hji]
            dsimp only at *; rw [Function.update_of_ne hne]
            rcases called_append_iff.1 hj with hj | ⟨_, he⟩
            · exact hR.called j hj
            · cases he; exact absurd rfl hji
        · by_cases hji : j = i
          · subst hji
            refine ⟨called_append_iff.2 (.inr ⟨r, rfl⟩), fun hret => ?_⟩
            rcases returned_append_iff.1 hret with hret | ⟨_, he⟩
            · exact hnc (hR.returned j hret)
            · cases he
          · have hne : (⟨j, 0⟩ : ReqId) ≠ ⟨i, 0⟩ := by simp [hji]
            dsimp only at hj; rw [Function.update_of_ne hne] at hj
            obtain ⟨h1, h2⟩ := hR.open_ j r' hj
            refine ⟨called_append_iff.2 (.inl h1), fun hret => ?_⟩
            rcases returned_append_iff.1 hret with hret | ⟨_, he⟩
            · exact h2 hret
            · cases he
        · rcases returned_append_iff.1 hj with hj | ⟨_, he⟩
          · exact called_append_iff.2 (.inl (hR.returned j hj))
          · cases he
  | .ret i s :: Q, P, w, w', h, hR => by
    cases h with
    | cons hs h' =>
      cases hs with
      | send hopen =>
        obtain ⟨hc, hnr⟩ := hR.open_ i _ hopen
        refine ⟨hc, hnr, orderly_of_wsteps Q h' ⟨fun j hj => ?_, fun j r' hj => ?_, fun j hj => ?_⟩⟩
        · rcases called_append_iff.1 hj with hj | ⟨_, he⟩
          · exact hR.called j hj
          · cases he
        · by_cases hji : j = i
          · subst hji; simp at hj
          · have hne : (⟨j, 0⟩ : ReqId) ≠ ⟨i, 0⟩ := by simp [hji]
            dsimp only at hj; rw [Function.update_of_ne hne] at hj
            obtain ⟨h1, h2⟩ := hR.open_ j r' hj
            refine ⟨called_append_iff.2 (.inl h1), fun hret => ?_⟩
            rcases returned_append_iff.1 hret with hret | ⟨_, he⟩
            · exact h2 hret
            · cases he; exact hji rfl
        · rcases returned_append_iff.1 hj with hj | ⟨_, he⟩
          · exact called_append_iff.2 (.inl (hR.returned j hj))
          · cases he; exact called_append_iff.2 (.inl hc)

theorem orderly_of_wf {H : Hist Req Resp} (h : Sen.WF (toTrace H)) : Orderly [] H := by
  obtain ⟨w, hw⟩ := h
  exact orderly_of_wsteps H hw wRel_init

end Silmaril.Proofs.Servers.State.Traces
