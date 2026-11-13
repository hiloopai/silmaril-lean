module

public import Silmaril.Automata.Institution.Defs
public import Silmaril.Automata.Spec.Thms

/-!
# The machine institution: proofs

The satisfaction condition and the functoriality of sentence translation.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata Silmaril.Automata.Inst

theorem reach_map_iff {A B : Sig} (σ : Sig.Hom A B) (M : Model B) (ls : List A.Lb) (x y : M.S) :
    ReachVia M.lts (· ∈ ls.map σ.lb) x y ↔ ReachVia (M.reduct σ).lts (· ∈ ls) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨k, hk, htr⟩ := hst
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
      exact Relation.ReflTransGen.tail ih ⟨l, hl, htr⟩
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨l, hl, htr⟩ := hst
      exact Relation.ReflTransGen.tail ih ⟨σ.lb l, List.mem_map_of_mem hl, htr⟩

theorem sat_map_iff {A B : Sig} (σ : Sig.Hom A B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ := by
  induction φ with
  | step a l b => rfl
  | reach ls a b => exact reach_map_iff σ M ls _ _
  | neg φ ih => exact not_congr ih
  | conj φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem map_id {A : Sig} (φ : Sen A) : φ.map (⟨id, id⟩ : Sig.Hom A A) = φ := by
  induction φ with
  | step => rfl
  | reach ls a b => simp [Sen.map]
  | neg φ ih => simp [Sen.map, ih]
  | conj φ ψ ih₁ ih₂ => simp [Sen.map, ih₁, ih₂]

theorem map_comp {A B C : Sig} (σ : Sig.Hom A B) (τ : Sig.Hom B C) (φ : Sen A) :
    φ.map (⟨τ.st ∘ σ.st, τ.lb ∘ σ.lb⟩ : Sig.Hom A C) = (φ.map σ).map τ := by
  induction φ with
  | step => rfl
  | reach ls a b => simp [Sen.map, List.map_map]
  | neg φ ih => simp [Sen.map, ih]
  | conj φ ψ ih₁ ih₂ => simp [Sen.map, ih₁, ih₂]

theorem reach_toSpec_iff {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L)
    (ls : List L) (a b : S) :
    ReachVia M.toLTS (· ∈ ls) a b ↔
      ReachVia ((specModel M.toSpec).reduct (nameHom S L)).lts (· ∈ ls)
        (FinNamed.name a) (FinNamed.name b) := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨l, hl, htr⟩ := hst
      exact Relation.ReflTransGen.tail ih ⟨l, hl, (toSpec_step_iff M _ l _).mpr htr⟩
  · intro h
    -- every state reachable from a name is a name
    have key : ∀ y, ReachVia ((specModel M.toSpec).reduct (nameHom S L)).lts (· ∈ ls)
        (FinNamed.name a) y → ∃ c : S, FinNamed.name c = y ∧ ReachVia M.toLTS (· ∈ ls) a c := by
      intro y hy
      induction hy with
      | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hst ih =>
        obtain ⟨c, rfl, hc⟩ := ih
        obtain ⟨l, hl, htr⟩ := hst
        change M.toSpec.Step (FinNamed.name c) (FinNamed.name l) _ at htr
        obtain ⟨s, k, s', hstep, he⟩ := (mem_toSpec_edges M _).mp htr
        obtain ⟨h1, h2, h3⟩ := Edge.mk.inj he
        rw [← FinNamed.name_inj h1, ← FinNamed.name_inj h2] at hstep
        exact ⟨s', h3.symm, Relation.ReflTransGen.tail hc ⟨l, hl, hstep⟩⟩
    obtain ⟨c, hc, hr⟩ := key _ h
    rw [FinNamed.name_inj hc] at hr
    exact hr

theorem sat_toSpec_iff {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L)
    (φ : Sen (sigOf S L)) :
    Sat (DMachine.model M) φ ↔ Sat (specModel M.toSpec) (φ.map (nameHom S L)) := by
  rw [sat_map_iff]
  induction φ with
  | step a l b => exact (toSpec_step_iff M a l b).symm
  | reach ls a b => exact reach_toSpec_iff M ls a b
  | neg φ ih => exact not_congr ih
  | conj φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

end Silmaril.Proofs.Automata
