module

public import Silmaril.Libc.Stdio.Printf.Defs

/-!
# Proofs: the `printf` tiers are nested, and a fixed `%p` keeps every text

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.Stdio.Printf

open Silmaril.Libc.Stdio.Printf
open Silmaril.X86 (Byte)

theorem Spec.leet_intc {c : Spec} (h : c.leet = true) : c.intc = true := by
  obtain ⟨fl, w, p, ln, k⟩ := c
  simp only [Spec.leet, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
  cases ln <;> cases k <;> simp_all [Spec.intc, Spec.flagsOk, Kind.hashOk, Kind.isInt, Kind.isFloat]

theorem Spec.intc_c99 {c : Spec} (h : c.intc = true) : c.c99 = true := by
  simp [Spec.c99, h]

theorem Spec.inTier_mono {t t' : Tier} (ht : t.le t') {c : Spec} (h : c.inTier t = true) :
    c.inTier t' = true := by
  cases t <;> cases t' <;> simp [Tier.le, Tier.rank] at ht <;> simp only [Spec.inTier] at h ⊢
  all_goals first
    | exact h
    | exact Spec.leet_intc h
    | exact Spec.intc_c99 h
    | exact Spec.intc_c99 (Spec.leet_intc h)

theorem convText_mono {pt pt' : Option (Nat → List Byte)} (hp : PtrLe pt pt') {c : Spec}
    {fl : Flags} {wn : Nat} {pn : Option Nat} {a : PArg} {t : List Byte}
    (h : convText pt c fl wn pn a = some t) : convText pt' c fl wn pn a = some t := by
  cases a with
  | ptr q =>
    cases hpt : pt with
    | none => simp [convText, hpt] at h
    | some f => simpa [convText, hpt, hp f hpt] using h
  | _ => exact h

theorem renderSpec_mono {pt pt' : Option (Nat → List Byte)} (hp : PtrLe pt pt') {c : Spec}
    {as : List PArg} {x : List Byte × List PArg} (h : renderSpec pt c as = some x) :
    renderSpec pt' c as = some x := by
  unfold renderSpec at h ⊢
  cases hw : takeCount c.width as with
  | none => simp [hw] at h
  | some y =>
    cases hq : takeCount c.prec y.2 with
    | none => simp [hw, hq] at h
    | some z =>
      cases hz : z.2 with
      | nil => simp [hw, hq, hz] at h
      | cons a as' =>
        simp only [hw, hq, hz, Option.map_eq_some_iff] at h ⊢
        obtain ⟨t, ht, rfl⟩ := h
        exact ⟨t, convText_mono hp ht, rfl⟩

theorem render_mono {pt pt' : Option (Nat → List Byte)} (hp : PtrLe pt pt') :
    ∀ {is : List Item} {as : List PArg} {out : List Byte}, render pt is as = some out →
      render pt' is as = some out
  | [], _, _, h => h
  | .lit b :: is, as, out, h => by
    simp only [render, Option.map_eq_some_iff] at h ⊢
    obtain ⟨o, ho, rfl⟩ := h
    exact ⟨o, render_mono hp ho, rfl⟩
  | .spec c :: is, as, out, h => by
    simp only [render] at h ⊢
    cases hs : renderSpec pt c as with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some x =>
      rw [hs] at h
      rw [renderSpec_mono hp hs]
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨o, ho, rfl⟩ := h
      exact ⟨o, render_mono hp ho, rfl⟩

theorem InTier.mono {t t' : Tier} {pt pt' : Option (Nat → List Byte)} (ht : t.le t')
    (hp : PtrLe pt pt') {is : List Item} (h : InTier t pt is) : InTier t' pt' is := by
  intro c hc
  rcases h c hc with h | ⟨h1, h2⟩
  · exact Or.inl (Spec.inTier_mono ht h)
  · refine Or.inr ⟨?_, h2⟩
    cases hpt : pt with
    | none => simp [hpt] at h1
    | some f => simp [hp f hpt]

theorem Text.mono {t t' : Tier} {pt pt' : Option (Nat → List Byte)} (ht : t.le t')
    (hp : PtrLe pt pt') {fmt : List Byte} {as : List PArg} {out : List Byte}
    (h : Text t pt fmt as out) : Text t' pt' fmt as out :=
  let ⟨is, h1, h2, h3⟩ := h
  ⟨is, h1, InTier.mono ht hp h2, render_mono hp h3⟩

end Silmaril.Proofs.Libc.Stdio.Printf

