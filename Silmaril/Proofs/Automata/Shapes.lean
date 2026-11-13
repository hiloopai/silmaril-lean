module

public import Silmaril.Automata.Shapes.Defs
public import Silmaril.Automata.Spec.Thms
public import Silmaril.Automata.Institution.Thms

/-!
# Standard problem shapes for finite machines: proofs

Transfer between typed machines and the JSON documents they are bound to.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata Silmaril.Automata.Shapes

theorem toLTS_eq_of_canon_eq {sp sp' : Spec} (h : sp.canon = sp'.canon) : sp.toLTS = sp'.toLTS := by
  have : ∀ s l d, sp.Step s l d ↔ sp'.Step s l d := fun s l d => by
    rw [← Spec.canon_step_iff, h, Spec.canon_step_iff]
  unfold Spec.toLTS
  congr 1
  funext s l d
  exact propext (this s l d)

theorem jsonReach_iff_of_bound {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L)
    (d : Document) (h : M.toSpec.canon = d.spec.canon) (P : L → Bool) (a b : S) :
    Reach M P a b ↔ JsonReach d (((FinNamed.elems (α := L)).filter P).map FinNamed.name)
      (FinNamed.name a) (FinNamed.name b) := by
  have h1 : Reach M P a b ↔
      Inst.Sat (Inst.DMachine.model M) (.reach ((FinNamed.elems (α := L)).filter P) a b) := by
    unfold Reach Inst.Sat
    simp only [Inst.DMachine.model, List.mem_filter, FinNamed.complete, true_and]
    rfl
  rw [h1, Inst.sat_toSpec_iff]
  unfold JsonReach
  rw [← toLTS_eq_of_canon_eq h]
  rfl

theorem jsonBisimilar_iff_of_bound {S T L : Type} [FinNamed S] [FinNamed T] [FinNamed L]
    (M : DMachine S L) (N : DMachine T L) (d e : Document) (hd : M.toSpec.canon = d.spec.canon)
    (he : N.toSpec.canon = e.spec.canon) (s : S) (t : T) :
    Bisimilar M N s t ↔ JsonBisimilar d e (FinNamed.name s) (FinNamed.name t) := by
  unfold Bisimilar JsonBisimilar
  rw [← toLTS_eq_of_canon_eq hd, ← toLTS_eq_of_canon_eq he]
  constructor
  · rintro ⟨R, hR, hb⟩
    refine ⟨fun x y => ∃ s t, R s t ∧ x = FinNamed.name s ∧ y = FinNamed.name t,
      ⟨s, t, hR, rfl, rfl⟩, ?_⟩
    rintro x y ⟨s₁, t₁, hr, rfl, rfl⟩ μ
    constructor
    · intro x' hx
      change M.toSpec.Step _ μ x' at hx
      obtain ⟨a, l, a', hst, hed⟩ := (mem_toSpec_edges M _).mp hx
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1] at hst
      obtain ⟨t', ht', hr'⟩ := (hb hr l).1 a' hst
      exact ⟨FinNamed.name t', by
        change N.toSpec.Step _ _ _
        rw [h2]; exact (toSpec_step_iff N _ _ _).mpr ht', a', t', hr', h3, rfl⟩
    · intro y' hy
      change N.toSpec.Step _ μ y' at hy
      obtain ⟨a, l, a', hst, hed⟩ := (mem_toSpec_edges N _).mp hy
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1] at hst
      obtain ⟨s', hs', hr'⟩ := (hb hr l).2 a' hst
      exact ⟨FinNamed.name s', by
        change M.toSpec.Step _ _ _
        rw [h2]; exact (toSpec_step_iff M _ _ _).mpr hs', s', a', hr', rfl, h3⟩
  · rintro ⟨R, hR, hb⟩
    refine ⟨fun s t => R (FinNamed.name s) (FinNamed.name t), hR, ?_⟩
    intro s₁ t₁ hr l
    constructor
    · intro s' hs'
      obtain ⟨y, hy, hr'⟩ := (hb hr (FinNamed.name l)).1 (FinNamed.name s')
        ((toSpec_step_iff M _ _ _).mpr hs')
      change N.toSpec.Step _ _ _ at hy
      obtain ⟨a, k, a', hst, hed⟩ := (mem_toSpec_edges N _).mp hy
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1, ← FinNamed.name_inj h2] at hst
      exact ⟨a', hst, by show R _ _; rw [← h3]; exact hr'⟩
    · intro t' ht'
      obtain ⟨x, hx, hr'⟩ := (hb hr (FinNamed.name l)).2 (FinNamed.name t')
        ((toSpec_step_iff N _ _ _).mpr ht')
      change M.toSpec.Step _ _ _ at hx
      obtain ⟨a, k, a', hst, hed⟩ := (mem_toSpec_edges M _).mp hx
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1, ← FinNamed.name_inj h2] at hst
      exact ⟨a', hst, by show R _ _; rw [← h3]; exact hr'⟩

end Silmaril.Proofs.Automata
