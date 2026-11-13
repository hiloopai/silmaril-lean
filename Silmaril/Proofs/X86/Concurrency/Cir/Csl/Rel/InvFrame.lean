module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.Frame

/-!
# CSL with release stores: the invariant frame rule

`safeR_inv_frame`: a thread `SafeR`-safe under the invariant `I` stays safe when the invariant is
extended by any `J` (physical and ghost) that the thread never opens: `SafeR I Q → SafeR (I ∗ J) Q`
with `∗` the ghost-aware separating conjunction `Rel.gsep`. The base version is
`Mutex.safe_inv_frame`; here the shared clause re-splits the ghost heap as well, and the release
obligation is framed by the untouched `J` part (the released cells are the thread's, so they are
disjoint from `J`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

section IF
variable {I J : GProp} {Q : Bool → Regs → Heap → Heap → Prop}

/-- A label that touches only cells of `A` keeps the domain of `A`. -/
theorem dom_updH {l : Lab} {A : Heap} (ht : ∀ a, l.Touches a → (A a).isSome) :
    Dom (l.updH A) A := fun a e => by
  rw [updH_apply, or_isSome] at e
  cases ew : (l.wval a).isSome
  · rw [ew, Bool.false_or] at e; exact e
  · exact ht a (wval_touch ew)

theorem union_left_eq {A B : Heap} {a : Nat} (e : (A a).isSome) : Heap.union A B a = A a := by
  rw [union_apply]; cases e' : A a with
  | none => rw [e'] at e; cases e
  | some v => rfl

/-- **The release obligation, framed.** -/
theorem oblig_frameI {e : Ent} {hR gR H G : Heap} (dR : Dom hR H) (dG : Dom gR G)
    (ob : Oblig I e hR gR H G) : Oblig (gsep I J) e hR gR H G := by
  intro hIJ gIJ hIJi dH dG'
  obtain ⟨hI, hJ, gI, gJ, dIJ, rfl, dgIJ, rfl, iI, jJ⟩ := hIJi
  have dHI : Heap.Disjoint H hI := disj_of_dom dH (dom_refl _) (dom_union_left _ _)
  have dHJ : Heap.Disjoint H hJ := disj_of_dom dH (dom_refl _) (dom_union_right _ _)
  have dGI : Heap.Disjoint G gI := disj_of_dom dG' (dom_refl _) (dom_union_left _ _)
  have dGJ : Heap.Disjoint G gJ := disj_of_dom dG' (dom_refl _) (dom_union_right _ _)
  obtain ⟨⟨a, v, w, rfl, ha⟩, iI'⟩ := ob hI gI iI dHI dGI
  refine ⟨⟨a, v, w, rfl, ?_⟩, ?_⟩
  · rw [← union_assoc]; exact dom_union_left _ _ a ha
  · have dRI : Heap.Disjoint (Heap.union hR hI) hJ :=
      disj_union_left (disj_of_dom dHJ dR (dom_refl _)) dIJ
    refine ⟨(Ent.st a v w).apply (Heap.union hR hI), hJ, Heap.union gR gI, gJ,
      disj_of_dom dRI (dom_apply ha) (dom_refl _), ?_,
      disj_union_left (disj_of_dom dGJ dG (dom_refl _)) dgIJ, (union_assoc _ _ _).symm, iI', jJ⟩
    funext x
    rw [union_apply, apply_st, apply_st, ← union_assoc]
    by_cases hx : x = a
    · simp [hx]
    · simp only [hx, ite_false]; rw [union_apply]

/-- **A label step's obligations, framed by an untouched invariant part.** -/
theorem labOkR_frameI {K : Bool → Heap → Heap → Prop} {p : Bool} {l : Lab} {h g : Heap}
    (H : LabOkR I K p l h g) : LabOkR (gsep I J) K p l h g := by
  obtain ⟨hm, H⟩ := H
  refine ⟨hm, ?_⟩
  rcases H with H | ⟨hna, hp, H⟩ | ⟨m, fl, a, sz, v, el, hm', h', hR, g', gR, d1, e1, d2, e2, k, ob⟩
  · exact Or.inl H
  · refine Or.inr (Or.inl ⟨hna, hp, fun hIJ gIJ hIJi dh dg => ?_⟩)
    obtain ⟨hI, hJ, gI, gJ, dIJ, rfl, dgIJ, rfl, iI, jJ⟩ := hIJi
    have dhI : Heap.Disjoint h hI := disj_of_dom dh (dom_refl _) (dom_union_left _ _)
    have dhJ : Heap.Disjoint h hJ := disj_of_dom dh (dom_refl _) (dom_union_right _ _)
    have dgI : Heap.Disjoint g gI := disj_of_dom dg (dom_refl _) (dom_union_left _ _)
    have dgJ : Heap.Disjoint g gJ := disj_of_dom dg (dom_refl _) (dom_union_right _ _)
    obtain ⟨t1, t2, t3⟩ := H hI gI iI dhI dgI
    have eA : Heap.union h (Heap.union hI hJ) = Heap.union (Heap.union h hI) hJ :=
      (union_assoc _ _ _).symm
    have dAJ : Heap.Disjoint (Heap.union h hI) hJ := disj_union_left dhJ dIJ
    have dGJ : Heap.Disjoint (Heap.union g gI) gJ := disj_union_left dgJ dgIJ
    refine ⟨fun a ha => ?_, t2, fun hok => ?_⟩
    · rw [eA]; exact dom_union_left _ _ a (t1 a ha)
    · rw [eA] at hok
      have hok' : l.okH (Heap.union h hI) :=
        okH_congr (fun a ha => union_left_eq (t1 a ha)) hok
      obtain ⟨h₁, hI₁, g₁, gI₁, d₁, e₁, dg₁, eg₁, iI₁, k₁, dm₁⟩ := t3 hok'
      have dN : Dom (Heap.union h₁ hI₁) (Heap.union h hI) := by rw [e₁]; exact dom_updH t1
      have dNg : Dom (Heap.union g₁ gI₁) (Heap.union g gI) := by rw [eg₁]; exact dom_refl _
      have dh₁ : Dom h₁ (Heap.union h hI) := dom_trans (dom_union_left _ _) dN
      have dI₁ : Dom hI₁ (Heap.union h hI) := dom_trans (dom_union_right _ _) dN
      have dg₁' : Dom g₁ (Heap.union g gI) := dom_trans (dom_union_left _ _) dNg
      have dgI₁ : Dom gI₁ (Heap.union g gI) := dom_trans (dom_union_right _ _) dNg
      refine ⟨h₁, Heap.union hI₁ hJ, g₁, Heap.union gI₁ gJ,
        disj_union_right d₁ (disj_of_dom dAJ dh₁ (dom_refl _)), ?_,
        disj_union_right dg₁ (disj_of_dom dGJ dg₁' (dom_refl _)), ?_,
        ⟨hI₁, hJ, gI₁, gJ, disj_of_dom dAJ dI₁ (dom_refl _), rfl,
          disj_of_dom dGJ dgI₁ (dom_refl _), rfl, iI₁, jJ⟩, k₁, dm₁⟩
      · rw [← union_assoc, e₁, eA, updH_union (Heap.union h hI) hJ]
      · rw [← union_assoc, eg₁, union_assoc]
  · refine Or.inr (Or.inr ⟨m, fl, a, sz, v, el, hm', h', hR, g', gR, d1, e1, d2, e2, k, ?_⟩)
    exact oblig_frameI (by rw [e1]; exact dom_union_right _ _)
      (by rw [e2]; exact dom_union_right _ _) ob

/-- **The invariant frame rule**: `SafeR I Q → SafeR (I ∗ J) Q`. -/
theorem safeR_inv_frame {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I Q p s rs h g) : SafeR (gsep I J) Q p s rs h g := by
  refine safeR_coind (I := gsep I J) (fun p s rs h g => SafeR I Q p s rs h g) ?_ H
  intro p s rs h g H
  have F := safeR_unfold H
  exact ⟨F.1, fun s' rs' st => Or.inl (F.2.1 s' rs' st),
    fun l s' rs' st => labOkR_mono (fun _ _ _ x => Or.inl x) (labOkR_frameI (F.2.2 l s' rs' st))⟩

end IF

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel
