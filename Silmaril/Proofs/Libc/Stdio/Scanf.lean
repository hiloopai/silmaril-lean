module

public import Silmaril.Libc.Stdio.Scanf.Defs

/-!
# Proofs: the `scanf` tiers are nested

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.Stdio.Scanf

open Silmaril.Libc.Stdio.Scanf
open Silmaril.Libc.Stdio.Printf (Tier)

theorem Spec.leet_intc {c : Spec} (h : c.leet = true) : c.intc = true := by
  obtain ⟨sk, w, ln, k⟩ := c
  simp only [Spec.leet, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  cases ln <;> cases k <;> simp_all [Spec.intc, Spec.lenOk]

theorem Spec.inTier_mono {t t' : Tier} (ht : t.le t') {c : Spec} (h : c.inTier t = true) :
    c.inTier t' = true := by
  cases t <;> cases t' <;> simp [Tier.le, Tier.rank] at ht <;> simp only [Spec.inTier] at h ⊢
  all_goals first
    | exact h
    | exact Spec.leet_intc h

theorem InTier.mono {t t' : Tier} (ht : t.le t') {is : List Item} (h : InTier t is) :
    InTier t' is := fun c hc => Spec.inTier_mono ht (h c hc)

end Silmaril.Proofs.Libc.Stdio.Scanf

