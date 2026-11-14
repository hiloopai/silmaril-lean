module

public import Silmaril.Servers.Hosts.Defs

/-!
# Proofs: host interpretations
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Hosts

open Silmaril.Servers Silmaril.Servers.Observe Silmaril.Servers.Hosts

theorem mem_under {H : Type} {A : Sig} {Hs : Set H} {C : Open H A} {o : Obs A} :
    o ∈ under Hs C ↔ ∃ η ∈ Hs, o ∈ C η := by simp [under]

/-- **Merging hosts loses refinement**: two open servers with the same merged behaviour where
neither refines the other host by host. -/
theorem under_not_refinesAt (A : Sig) :
    ∃ C D : Open Bool A, under Set.univ C = under Set.univ D ∧
      ¬ RefinesAt Set.univ C D := by
  refine ⟨fun b => if b then {Obs.initFail} else ∅, fun b => if b then ∅ else {Obs.initFail},
    ?_, fun h => ?_⟩
  · ext o; simp [mem_under]
  · simpa using h true trivial (Set.mem_singleton Obs.initFail)

theorem pure_answers {Q R : Type} (f : Pure Q R) (qs : List Q) :
    (Pure.toStateful f).answers () qs = qs.map f := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [Stateful.answers, Pure.toStateful] at ih ⊢; exact ih

theorem oracle_answers {Q R : Type} (o : Oracle R) (qs : List Q) (k : Nat) :
    (Oracle.toStateful (Q := Q) o).answers k qs = (List.range' k qs.length).map o := by
  induction qs generalizing k with
  | nil => rfl
  | cons q qs ih =>
    rw [show (Oracle.toStateful (Q := Q) o).answers k (q :: qs) =
      o k :: (Oracle.toStateful (Q := Q) o).answers (k + 1) qs from rfl, ih]
    rfl

theorem answers_append {σ Q R : Type} (h : Stateful σ Q R) (s : σ) (qs qs' : List Q) :
    h.answers s (qs ++ qs') =
      h.answers s qs ++ h.answers ((qs.foldl (fun s q => (h.step s q).2) s)) qs' := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih => simp [Stateful.answers, ih]

end Silmaril.Proofs.Servers.Hosts
