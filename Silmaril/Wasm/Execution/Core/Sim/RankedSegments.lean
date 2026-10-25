module

public import Silmaril.Wasm.Execution.Core.Sim.Rank

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A trap/exception discard strictly decreases every lawful contextual rank. -/
theorem Step.exitShape_cut_rank {rank : List Admin → Nat} [LawfulCodeRank rank] {s s' : Store H} {f f' : Frame} {U : List Val} {k X es' : List Admin}
    (hk : k = [.trap] ∨ ∃ a, k = throwing a)
    (h : Step P host ⟨s, f, vals U ++ k ++ X⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ (∃ U' X', es' = vals U' ++ k ++ X') ∧
      rank es' < rank (vals U ++ k ++ X) := by
  rcases hk with rfl | ⟨a, rfl⟩
  · have h' : Step P host ⟨s, f, vals U ++ Admin.trap :: X⟩ ⟨s', f', es'⟩ := by simpa using h
    rcases Step.split_head val?_trap h' with ⟨ws, us, is', rfl, hst, rfl⟩ |
        ⟨-, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ | ⟨hc, -⟩
    · obtain ⟨hs, hf, p, w, q, rfl, hw, he⟩ := Step.trap_redex_aux hst us rfl
      dsimp only at hs hf he
      subst hs hf he
      refine ⟨rfl, rfl, ⟨ws ++ (p ++ q), X, by simp⟩, ?_⟩
      have := LawfulCodeRank.drop_vals_lt (rank := rank) (ws ++ p) w q ([.trap] ++ X) hw
      simpa using this
    · exact ⟨rfl, rfl, ⟨ws, r', rfl⟩, LawfulCodeRank.discard_lt (rank := rank) ws us _ r r' hne⟩
    · cases hc
  · have e : vals U ++ throwing a ++ X =
        vals (U ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: X := by
      simp [vals, throwing, Val.toAdmin]
    rw [e] at h
    rcases Step.split_head val?_throwRef h with ⟨ws, us, is', hU, hst, rfl⟩ | ⟨hc, -⟩ |
        ⟨-, rfl, rfl, ws, us, x, r, r', hU, rfl, hne, rfl⟩
    · obtain ⟨hs, hf, hdisj⟩ := Step.throwRef_redex_aux hst us rfl
      dsimp only at hs hf hdisj
      subst hs hf
      rcases hdisj with ⟨p, w, q, a', rfl, hw, he⟩ | ⟨u, u', rfl, -⟩
      · have hU' : U ++ [.ref (.exn a)] = (ws ++ p ++ w ++ q) ++ [.ref (.exn a')] := by
          rw [hU]; simp
        obtain ⟨rfl, ha⟩ := List.append_inj' hU' rfl
        have ha' : a = a' := by simpa using ha
        subst ha' he
        refine ⟨rfl, rfl, ⟨ws ++ (p ++ q), X, by simp⟩, ?_⟩
        have := LawfulCodeRank.drop_vals_lt (rank := rank) (ws ++ p) w q (throwing a ++ X) hw
        simpa using this
      · have hU' : U ++ [.ref (.exn a)] = (ws ++ u) ++ [.ref .null] := by
          rw [hU]; simp
        have := (List.append_inj' hU' rfl).2
        simp at this
    · cases hc
    · have hU' : U ++ [.ref (.exn a)] = (ws ++ us) ++ [.ref (.exn x)] := by
        rw [hU]
      obtain ⟨rfl, ha⟩ := List.append_inj' hU' rfl
      have ha' : a = x := by simpa using ha
      subst ha'
      exact ⟨rfl, rfl, ⟨ws, r', rfl⟩, LawfulCodeRank.discard_lt (rank := rank) ws us _ r r' hne⟩


end Silmaril.Wasm.Execution.Core.Sim
