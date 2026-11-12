module

public import Silmaril.Libc.X86Alloc.Spec.Defs
public import Silmaril.X86.Sep.AllocS.Thms

/-!
# Proofs: the allocator specification layers refine each other

`mallocSpecF ⊑ mallocSpecL ⊑ₕ mallocSpec` and `freeSpecL ⊑ₕ freeSpec`, and the transport of a
functional spec along a simulation to a liveness spec of another capacity model.
-/

@[expose] public section

namespace Silmaril.Raw.Libc.X86Alloc.Spec

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc

/-- `P ⊢ P ∗ ⌜φ⌝` when `φ` holds. -/
theorem sep_spure_intro {φ : Prop} {P : SProp} (hφ : φ) : P ⊢ₛ (P ∗ ⌜φ⌝) := by
  rw [sep_comm]; exact spure_sep_intro hφ (entails_refl _)

theorem fresh_ne {A : Iface} {v : Word} {n : Nat} {Q R : SProp}
    (h : v ≠ 0 → (A.Fresh v n ∗ Q) ⊢ₛ R) : (A.Fresh v n ∗ Q) ⊢ₛ R := by
  intro f hf
  have hf' := hf
  unfold Iface.Fresh at hf'
  rw [sep_assoc, spure_sep_apply] at hf'
  exact h hf'.1.1 f hf

theorem mallocSpecL_subH {C : CapModel} (B : IfaceL C) :
    (mallocSpecL B).SubH (mallocSpec B.toIface) where
  stack := Nat.le_refl _
  arg y h hpre := by
    obtain ⟨s, hs⟩ := hpre
    refine ⟨(s, y), rfl, emp, by rw [sep_emp]; exact hs, fun v => ?_⟩
    refine entails_trans (entails_of_eq (sep_emp _)) (sor_elim ?_ ?_)
    · refine spure_sep_elim fun ⟨hv, _⟩ => entails_trans (sep_spure_intro hv)
        (sep_mono (sexists_intro s (entails_refl _)) (sor_intro_left _ _))
    · rw [sep_comm]
      exact sep_mono (sexists_intro _ (entails_refl _)) (sor_intro_right _ _)

theorem freeSpecL_subH {C : CapModel} (B : IfaceL C) :
    (freeSpecL B).SubH (freeSpec B.toIface) where
  stack := Nat.le_refl _
  arg y h hpre := by
    obtain ⟨p, n⟩ := y
    cases n with
    | none =>
      have hpre' : (sexists B.mmS ∗ ⌜p = 0⌝) h := hpre
      rw [sexists_sep] at hpre'
      obtain ⟨s, hs⟩ := hpre'
      exact ⟨⟨s, p, none⟩, rfl, emp, by rw [sep_emp]; exact hs,
        fun _ => entails_trans (entails_of_eq (sep_emp _)) (sexists_intro _ (entails_refl _))⟩
    | some n =>
      have hpre' : (sexists B.mmS ∗ B.tok p n ∗ blockAny p.toNat n) h := hpre
      rw [sexists_sep] at hpre'
      obtain ⟨s, hs⟩ := hpre'
      exact ⟨⟨s, p, some n⟩, rfl, emp, by rw [sep_emp]; exact hs,
        fun _ => entails_trans (entails_of_eq (sep_emp _)) (sexists_intro _ (entails_refl _))⟩

theorem mallocSpecF_sub {R : RefModel} (B : IfaceL R.toCap) :
    (mallocSpecF B).Sub (mallocSpecL B) where
  stack := Nat.le_refl _
  arg y := by
    refine ⟨y, rfl, emp, entails_of_eq (sep_emp _).symm, fun v => ?_⟩
    refine entails_trans (entails_of_eq (sep_emp _)) (spure_sep_elim fun hv => sor_elim ?_ ?_)
    · refine spure_sep_elim fun h0 => entails_trans ?_ (sor_intro_left _ _)
      have hfail : v = 0 ∧ ¬ R.toCap.avail y.1 y.2.toNat := ⟨h0, fun hne => hne (hv ▸ h0)⟩
      exact spure_sep_intro hfail (entails_refl _)
    · exact sor_intro_right _ _

theorem mallocSpecF_subH_along {R : RefModel} {C : CapModel} {α : R.St → C.St}
    {Inv : R.St → Prop} (hsim : R.Sim C α Inv) (B : IfaceL R.toCap) :
    (mallocSpecF B).SubH (mallocSpecL (B.along α Inv)) where
  stack := Nat.le_refl _
  arg y h hpre := by
    obtain ⟨c, n⟩ := y
    obtain ⟨s, hs⟩ := hpre
    rw [spure_sep_apply] at hs
    obtain ⟨⟨hα, hI⟩, hs⟩ := hs
    subst hα
    refine ⟨(s, n), rfl, emp, by rw [sep_emp]; exact hs, fun v => ?_⟩
    refine entails_trans (entails_of_eq (sep_emp _)) (spure_sep_elim fun hv => sor_elim ?_ ?_)
    · refine spure_sep_elim fun h0 => entails_trans ?_ (sor_intro_left _ _)
      have hfail : v = 0 ∧ ¬ C.avail (α s) n.toNat :=
        ⟨h0, fun ha => hsim.avail s n.toNat hI ha (hv ▸ h0)⟩
      refine spure_sep_intro hfail ?_
      show B.mmS s ⊢ₛ sexists fun s' => ⌜α s' = α s ∧ Inv s'⌝ ∗ B.mmS s'
      exact sexists_intro s (spure_sep_intro ⟨rfl, hI⟩ (entails_refl _))
    · refine fresh_ne fun hne => entails_trans ?_ (sor_intro_right _ _)
      obtain ⟨hI', hα'⟩ := hsim.alloc s n.toNat hI (hv ▸ hne)
      show (B.toIface.Fresh v n.toNat ∗ B.mmS (R.alloc s n.toNat)) ⊢ₛ
        ((⌜v ≠ 0 ∧ v.toNat % B.align = 0⌝ ∗ (⌜v ≠ 0⌝ ∗ B.tok v n.toNat) ∗
          blockAny v.toNat n.toNat) ∗
          sexists fun s' => ⌜α s' = C.alloc (α s) n.toNat v ∧ Inv s'⌝ ∗ B.mmS s')
      refine sep_mono ?_ (sexists_intro (R.alloc s n.toNat)
        (spure_sep_intro ⟨by rw [hα', ← hv], hI'⟩ (entails_refl _)))
      unfold Iface.Fresh IfaceL.toIface
      exact sep_mono_right _ (sep_mono_left _ (spure_sep_intro hne (entails_refl _)))

theorem freeSpecL_subH_along {R : RefModel} {C : CapModel} {α : R.St → C.St}
    {Inv : R.St → Prop} (hsim : R.Sim C α Inv) (B : IfaceL R.toCap) :
    (freeSpecL B).SubH (freeSpecL (B.along α Inv)) where
  stack := Nat.le_refl _
  arg y h hpre := by
    obtain ⟨c, p, n⟩ := y
    cases n with
    | none =>
      have hpre' : ((sexists fun s => ⌜α s = c ∧ Inv s⌝ ∗ B.mmS s) ∗ ⌜p = 0⌝) h := hpre
      rw [sexists_sep] at hpre'
      obtain ⟨s, hs⟩ := hpre'
      rw [sep_assoc, spure_sep_apply] at hs
      obtain ⟨⟨hα, hI⟩, hs⟩ := hs
      exact ⟨⟨s, p, none⟩, rfl, emp, by rw [sep_emp]; exact hs,
        fun _ => entails_trans (entails_of_eq (sep_emp _))
          (sexists_intro s (spure_sep_intro ⟨hα, hI⟩ (entails_refl _)))⟩
    | some n =>
      have hpre' : ((sexists fun s => ⌜α s = c ∧ Inv s⌝ ∗ B.mmS s) ∗
          (⌜p ≠ 0⌝ ∗ B.tok p n) ∗ blockAny p.toNat n) h := hpre
      rw [sexists_sep] at hpre'
      obtain ⟨s, hs⟩ := hpre'
      rw [sep_assoc, spure_sep_apply] at hs
      obtain ⟨⟨hα, hI⟩, hs⟩ := hs
      rw [sep_left_comm, sep_assoc, spure_sep_apply] at hs
      obtain ⟨hp, hs⟩ := hs
      rw [← sep_assoc, sep_comm (B.tok p n), sep_assoc] at hs
      obtain ⟨hI', hα'⟩ := hsim.dealloc s p n hI hp
      refine ⟨⟨s, p, some n⟩, rfl, emp, by rw [sep_emp]; exact hs, fun _ => ?_⟩
      refine entails_trans (entails_of_eq (sep_emp _))
        (sexists_intro _ (spure_sep_intro ⟨?_, hI'⟩ (entails_refl _)))
      show α (R.dealloc s p n) = C.dealloc c p n
      rw [hα', hα]

end Silmaril.Raw.Libc.X86Alloc.Spec
