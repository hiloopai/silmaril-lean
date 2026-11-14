module

public import Iris.BI
public import Silmaril.Wasm.Logic.V1.Assertions.Defs

/-!
# A `BI` instance for Wasm Logic's heap assertions

`HAssert := Sto → AHeap → Prop` (`Silmaril.Wasm.Logic.V1.Assertions.Defs`) is a
classical (non-affine) separation logic over `AHeap`'s partial heaps (disjoint
union, commutative and associative when disjoint, with `AHeap.emp` as unit).
This gives it upstream iris-lean's `BI` structure, modelled on
`Iris.Instances.Classical.Instance`'s `HeapProp`; the store `Sto` is threaded
through unchanged. With it, the proof mode (`iintro`, `iframe`, `isplit`, ...)
and the generic `BI` lemmas apply to Wasm Logic assertions
(`Silmaril.Wasm.Logic.Iris.V1.Thms`). The later modality is the identity: the
logic is not step-indexed.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisV1

open _root_.Iris _root_.Iris.BI _root_.Iris.Std
open Silmaril.Wasm.Logic.V1

instance : BIBase HAssert where
  Entails P Q    := ∀ ρ h, P ρ h → Q ρ h
  emp            := HAssert.emp
  pure φ _ _     := φ
  and            := HAssert.and
  or             := HAssert.or
  imp P Q ρ h    := P ρ h → Q ρ h
  sForall Ψ ρ h  := ∀ p, Ψ p → p ρ h
  sExists Ψ ρ h  := ∃ p, Ψ p ∧ p ρ h
  sep            := HAssert.star
  wand P Q ρ h   := ∀ h', AHeap.Disj h h' → P ρ h' → Q ρ (h ∪ h')
  persistently P ρ _ := P ρ AHeap.emp
  later          := id

instance hassertPreorder : Std.IsPreorder HAssert where
  le_refl := fun _ _ _ h => h
  le_trans := fun _ _ _ h_xy h_yz ρ h h_x => h_yz ρ h (h_xy ρ h h_x)

instance : COFE HAssert := COFE.ofDiscrete _

instance : BI HAssert where
  entails_refl := hassertPreorder.le_refl _
  entails_trans := hassertPreorder.le_trans _ _ _
  equiv_iff {P Q} := ⟨
    fun h => h ▸ ⟨Std.IsPreorder.le_refl P, Std.IsPreorder.le_refl P⟩,
    fun ⟨h₁, h₂⟩ => funext fun ρ => funext fun h => propext ⟨h₁ ρ h, h₂ ρ h⟩
  ⟩

  and_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne           := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne         := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne        := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl

  pure_intro h _ _ _ := h
  pure_elim' h_φP ρ h h_φ := h_φP h_φ ρ h ⟨⟩

  and_elim_l := by
    simp only [BI.Entails, BI.and, HAssert.and]
    intro _ _ ρ h hPQ
    exact hPQ.left
  and_elim_r := by
    simp only [BI.Entails, BI.and, HAssert.and]
    intro _ _ ρ h hPQ
    exact hPQ.right
  and_intro := by
    simp only [BI.Entails, BI.and, HAssert.and]
    intro _ _ _ h_PQ h_PR ρ h h_P
    exact ⟨h_PQ ρ h h_P, h_PR ρ h h_P⟩

  or_intro_l := by
    simp only [BI.Entails, BI.or, HAssert.or]
    intro _ _ ρ h hP
    exact Or.inl hP
  or_intro_r := by
    simp only [BI.Entails, BI.or, HAssert.or]
    intro _ _ ρ h hQ
    exact Or.inr hQ
  or_elim := by
    simp only [BI.Entails, BI.or, HAssert.or]
    intro _ _ _ h_PR h_QR ρ h h_PQ
    rcases h_PQ with h_P | h_Q
    · exact h_PR ρ h h_P
    · exact h_QR ρ h h_Q

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and, HAssert.and]
    intro _ _ _ h_PQR ρ h h_P h_Q
    exact h_PQR ρ h ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and, HAssert.and]
    intro _ _ _ h_PQR ρ h ⟨h_P, h_Q⟩
    exact h_PQR ρ h h_P h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ ρ h h_P p hp
    exact h_PΨ p hp ρ h h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ p hp ρ h h_Ψ
    exact h_Ψ p hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ p hp ρ h h_P
    exact ⟨p, hp, h_P⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ ρ h ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp ρ h h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep, HAssert.star]
    intro _ _ _ _ h_PQ h_P'Q' ρ _ ⟨h₁, h₂, h_disjoint, h_union, h_P, h_P'⟩
    exact ⟨h₁, h₂, h_disjoint, h_union, h_PQ ρ h₁ h_P, h_P'Q' ρ h₂ h_P'⟩
  emp_sep.mp := by
    simp only [BI.Entails, BI.sep, BI.emp, HAssert.star, HAssert.emp]
    intro ρ _ ⟨h₁, h₂, _, h_union, h_emp, h_P⟩
    rw [h_emp, AHeap.emp_union] at h_union
    rwa [h_union]
  emp_sep.mpr := by
    simp only [BI.Entails, BI.sep, BI.emp, HAssert.star, HAssert.emp]
    intro ρ h h_P
    exact ⟨AHeap.emp, h, AHeap.emp_disj h, (AHeap.emp_union h).symm, rfl, h_P⟩
  sep_symm := by
    simp only [BI.Entails, BI.sep, HAssert.star]
    intro _ _ ρ _ ⟨h₁, h₂, h_disjoint, h_union, h_P, h_Q⟩
    exact ⟨h₂, h₁, h_disjoint.symm, h_union.trans (AHeap.union_comm h_disjoint), h_Q, h_P⟩
  sep_assoc_l := by
    simp only [BI.Entails, BI.sep, HAssert.star]
    intro _ _ _ ρ _
      ⟨h₁, h₂, h_disjoint₁₂, h_union₁₂, ⟨h₃, h₄, h_disjoint₃₄, h_union₃₄, h_P, h_Q⟩, h_R⟩
    subst h_union₃₄
    refine ⟨h₃, h₄ ∪ h₂, ?_, ?_, h_P, h₄, h₂, AHeap.disj_union_right h_disjoint₁₂, rfl, h_Q, h_R⟩
    · exact (AHeap.disj_union h_disjoint₃₄.symm (AHeap.disj_union_left h_disjoint₁₂).symm).symm
    · rw [h_union₁₂, AHeap.union_assoc]

  wand_intro := by
    simp only [BI.Entails, BI.wand, BI.sep, HAssert.star]
    intro _ _ _ h_PQR ρ h h_P h' h_disjoint h_Q
    exact h_PQR ρ (h ∪ h') ⟨h, h', h_disjoint, rfl, h_P, h_Q⟩
  wand_elim := by
    simp only [BI.Entails, BI.wand, BI.sep, HAssert.star]
    intro _ _ _ h_PQR ρ _ ⟨h, h', h_disjoint, h_union, h_P, h_Q⟩
    subst h_union
    exact h_PQR ρ h h_P h' h_disjoint h_Q

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ ρ _ h_P
    exact h_PQ ρ AHeap.emp h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ _ h
    exact h
  persistently_emp_2 := fun ρ h (_ : h = AHeap.emp) => (rfl : AHeap.emp = AHeap.emp)
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and, HAssert.and]
    intro _ _ _ _ h
    exact h
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep, HAssert.star]
    intro _ _ ρ _ ⟨_, _, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep, HAssert.and, HAssert.star]
    intro _ _ ρ h ⟨h_P, h_Q⟩
    exact ⟨AHeap.emp, h, AHeap.emp_disj h, (AHeap.emp_union h).symm, h_P, h_Q⟩

  later_mono := id
  later_intro _ _ := id
  later_sForall_2 := by
    intro _ ρ h h_H p hp
    exact h_H _ ⟨p, rfl⟩ hp
  later_sExists_false := by
    intro _ ρ h h_H
    obtain ⟨p, hp, h_p⟩ := h_H
    exact Or.inr ⟨_, ⟨p, rfl⟩, hp, h_p⟩
  later_sep := ⟨by intro _ _ h; exact h, by intro _ _ h; exact h⟩
  later_persistently := ⟨by intro _ _ h; exact h, by intro _ _ h; exact h⟩
  later_false_em := by
    intro _ ρ h h_P
    exact Or.inr fun _ => h_P

end Silmaril.Wasm.Logic.IrisV1
