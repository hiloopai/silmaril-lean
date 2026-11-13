module

public import Silmaril.Games.Div.Thms
public import Mathlib.Data.List.Forall2

/-!
# The middle of an image of an infinite play

`inf_mid`: if every finite prefix of the infinite play `I` is the `R`-image of a member of the
infinite play `J`, and `R` factors through `R₁` and `R₂`, then there is an increasing unbounded
chain `c` of middle plays: each `c n` is an `R₁`-image of a member of `J` and has an `R₂`-image
in `I`, and every member of `I` is the `R₂`-image of some `c n`.

The middle moves are chosen one index at a time, from the members of `J` and `I` of length
`i + 1`. Members of an infinite play of the same length coincide, so the choices are consistent.
-/

public section

namespace Silmaril.Proofs.Games.DInstitution

open Silmaril.Games

universe v

variable {α β γ : Type v}

/-- Members of an infinite play agree at every index below both lengths. -/
theorem getElem_eq {I : Set (List α)} (h : IsInfPlay I) {s t : List α} (hs : s ∈ I) (ht : t ∈ I)
    {i : ℕ} (hi : i < s.length) (hj : i < t.length) : s[i] = t[i] := by
  rcases le_total s.length t.length with hl | hl
  · exact (h.prefix_of_length_le hs ht hl).getElem hi
  · exact ((h.prefix_of_length_le ht hs hl).getElem hj).symm

/-- A member of an infinite play is its member of the same length. -/
theorem eq_seq {I : Set (List α)} (h : IsInfPlay I) {p : List α} (hp : p ∈ I) :
    p = h.seq p.length := by
  have hl : p.length ≤ (h.seq p.length).length := by rw [h.seq_length]
  exact (h.prefix_of_length_le hp (h.seq_mem _) hl).eq_of_length (by rw [h.seq_length])

/-- The prefixes of `List.map b (List.range n)` increase with `n`. -/
theorem rangeMap_mono (b : ℕ → β) : Chain.Mono fun n => (List.range n).map b := by
  intro n
  change (List.range n).map b <+: (List.range (n + 1)).map b
  rw [List.range_succ, List.map_append]
  exact List.prefix_append _ _

theorem rangeMap_unbounded (b : ℕ → β) : Chain.Unbounded fun n => (List.range n).map b :=
  fun k => ⟨k, by simp⟩

/-- **The middle chain of an image of an infinite play.** -/
theorem inf_mid {R : α → γ → Prop} {R₁ : α → β → Prop} {R₂ : β → γ → Prop}
    (hdec : ∀ a c, R a c → ∃ b, R₁ a b ∧ R₂ b c) {I : Set (List γ)} {J : Set (List α)}
    (hI : IsInfPlay I) (hJ : IsInfPlay J) (hIJ : ∀ p ∈ I, ∃ s ∈ J, List.Forall₂ R s p) :
    ∃ c : Chain β, c.Mono ∧ c.Unbounded ∧
      (∀ n, ∃ s ∈ J, ∃ p ∈ I, List.Forall₂ R₁ s (c n) ∧ List.Forall₂ R₂ (c n) p) ∧
      ∀ p ∈ I, ∃ n, List.Forall₂ R₂ (c n) p := by
  choose sOf hsJ hsR using fun n => hIJ (hI.seq n) (hI.seq_mem n)
  have hsl : ∀ n, (sOf n).length = n := fun n => by
    rw [(hsR n).length_eq, hI.seq_length]
  have hRi : ∀ i, R ((sOf (i + 1))[i]'(by rw [hsl]; omega))
      ((hI.seq (i + 1))[i]'(by rw [hI.seq_length]; omega)) := fun i =>
    (hsR (i + 1)).get (by rw [hsl]; omega) (by rw [hI.seq_length]; omega)
  choose b hb₁ hb₂ using fun i => hdec _ _ (hRi i)
  let c : Chain β := fun n => (List.range n).map b
  have hcl : ∀ n, (c n).length = n := fun n => by simp [c]
  have hcget : ∀ n i (hi : i < (c n).length), (c n)[i] = b i := fun n i hi => by simp [c]
  refine ⟨c, rangeMap_mono b, rangeMap_unbounded b, fun n => ?_, fun p hp => ?_⟩
  · show ∃ s ∈ J, ∃ p ∈ I, List.Forall₂ R₁ s (c n) ∧ List.Forall₂ R₂ (c n) p
    refine ⟨sOf n, hsJ n, hI.seq n, hI.seq_mem n, ?_, ?_⟩
    · refine List.forall₂_iff_get.2 ⟨by rw [hsl, hcl], fun i h₁ h₂ => ?_⟩
      have heq : (sOf n)[i] = (sOf (i + 1))[i]'(by rw [hsl]; omega) :=
        getElem_eq hJ (hsJ n) (hsJ (i + 1)) h₁ _
      simp only [List.get_eq_getElem, hcget n i h₂, heq]
      exact hb₁ i
    · refine List.forall₂_iff_get.2 ⟨by rw [hcl, hI.seq_length], fun i h₁ h₂ => ?_⟩
      have heq : (hI.seq n)[i] = (hI.seq (i + 1))[i]'(by rw [hI.seq_length]; omega) :=
        getElem_eq hI (hI.seq_mem n) (hI.seq_mem (i + 1)) h₂ _
      simp only [List.get_eq_getElem, hcget n i h₁, heq]
      exact hb₂ i
  · refine ⟨p.length, ?_⟩
    rw [eq_seq hI hp]
    refine List.forall₂_iff_get.2 ⟨by rw [hcl, hI.seq_length], fun i h₁ h₂ => ?_⟩
    have heq : (hI.seq p.length)[i] = (hI.seq (i + 1))[i]'(by rw [hI.seq_length]; omega) :=
      getElem_eq hI (hI.seq_mem _) (hI.seq_mem (i + 1)) h₂ _
    simp only [List.get_eq_getElem, hcget _ i h₁, heq]
    exact hb₂ i

end Silmaril.Proofs.Games.DInstitution
