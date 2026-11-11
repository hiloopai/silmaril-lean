module

public import Silmaril.Wasm.Tools.Suggest.Defs

/-!
# Suggestions name a candidate

`didYouMean_mem`: a suggestion is one of the candidates (clap never suggests a flag the
command does not have).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Suggest

theorem fold_mem (v : String) (cs : List String) :
    ∀ (l : List String) (best : Option (Float × String)),
      (∀ p, best = some p → p.2 ∈ cs) → (∀ x ∈ l, x ∈ cs) →
      ∀ p, l.foldl (fun (best : Option (Float × String)) c =>
        let s := jaro v c
        if s > 0.7 then
          match best with
          | some (bs, _) => if s ≥ bs then some (s, c) else best
          | none => some (s, c)
        else best) best = some p → p.2 ∈ cs
  | [], best, hb, _, p, h => hb p h
  | c :: l, best, hb, hl, p, h => by
    simp only [List.foldl_cons] at h
    refine fold_mem v cs l _ ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) p h
    intro q hq
    have hc : c ∈ cs := hl c List.mem_cons_self
    split at hq
    · split at hq
      · split at hq
        · cases hq; exact hc
        · exact hb q hq
      · cases hq; exact hc
    · exact hb q hq

/-- **A suggestion is one of the candidates.** -/
theorem didYouMean_mem {v c : String} {cs : List String} (h : didYouMean v cs = some c) :
    c ∈ cs := by
  unfold didYouMean at h
  cases hf : cs.foldl _ none with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact fold_mem v cs cs none (fun _ h => by cases h) (fun _ h => h) p hf

theorem mem_insertAsc {s : Float} {c : String} {p : Float × String} :
    ∀ {l : List (Float × String)}, p ∈ insertAsc s c l → p = (s, c) ∨ p ∈ l
  | [], h => by simp [insertAsc] at h; exact .inl h
  | (t, d) :: rest, h => by
    unfold insertAsc at h
    split at h
    · simpa using h
    · rcases List.mem_cons.mp h with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases mem_insertAsc h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

theorem foldAll_mem (v : String) (cs : List String) :
    ∀ (l : List String) (acc : List (Float × String)),
      (∀ p ∈ acc, p.2 ∈ cs) → (∀ x ∈ l, x ∈ cs) →
      ∀ p ∈ l.foldl (fun acc c =>
        let s := jaro v c
        if s > 0.7 then insertAsc s c acc else acc) acc, p.2 ∈ cs
  | [], _, ha, _ => ha
  | c :: l, acc, ha, hl => by
    simp only [List.foldl_cons]
    refine foldAll_mem v cs l _ ?_ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    intro p hp
    split at hp
    · rcases mem_insertAsc hp with h | h
      · subst h; exact hl c List.mem_cons_self
      · exact ha p h
    · exact ha p hp

/-- **Every suggestion of `didYouMeanAll` is one of the candidates.** -/
theorem didYouMeanAll_mem {v c : String} {cs : List String} (h : c ∈ didYouMeanAll v cs) :
    c ∈ cs := by
  unfold didYouMeanAll at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact foldAll_mem v cs cs [] (by simp) (fun _ hx => hx) p hp

end Silmaril.Wasm.Tools.Suggest

end
