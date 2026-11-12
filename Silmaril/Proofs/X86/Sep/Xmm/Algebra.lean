module

public import Silmaril.X86.Sep.Xmm.Defs
/-!
# Proofs: the algebra of partial maps and of fragments with XMM registers

Behind `Silmaril/Machine/X86/Sep/Xmm/Thms.lean`. `PMap` lemmas are proved once and serve both
components of an `XFrag` (`Sep.Frag`'s operations are `PMap`'s by `rfl`: `frag_union`, …).
`xsep` is associative and commutative with unit `xemp`.

Only `Sep`'s and `Sse9`'s headers are imported; the few `Frag` lemmas needed are re-proved
here for `PMap`, not imported from `Sep`'s proof modules.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Xmm

open Silmaril.X86.Sep

/-! ## Partial maps -/

namespace PMap

variable {α β : Type} {f g k s : PMap α β} {a : α}

theorem union_of_none (h : f a = none) : union f g a = g a := by simp [union, h]

theorem union_of_some {v : β} (h : f a = some v) : union f g a = some v := by simp [union, h]

theorem empty_union (f : PMap α β) : union empty f = f := by funext a; rfl

theorem union_empty (f : PMap α β) : union f empty = f := by
  funext a; simp only [union, empty]; cases f a <;> rfl

theorem union_assoc (f g k : PMap α β) : union (union f g) k = union f (union g k) := by
  funext a; simp only [union]; cases f a <;> rfl

theorem Disjoint.symm (h : Disjoint f g) : Disjoint g f := fun a => (h a).symm

theorem disjoint_comm : Disjoint f g ↔ Disjoint g f := ⟨Disjoint.symm, Disjoint.symm⟩

theorem disjoint_empty_left (f : PMap α β) : Disjoint empty f := fun _ => .inl rfl

theorem disjoint_empty_right (f : PMap α β) : Disjoint f empty := fun _ => .inr rfl

theorem union_comm (h : Disjoint f g) : union f g = union g f := by
  funext a
  simp only [union]
  rcases h a with e | e <;> rw [e] <;> cases (g a) <;> cases (f a) <;> simp_all

theorem union_eq_none : union f g a = none ↔ f a = none ∧ g a = none := by
  simp only [union]; cases f a <;> simp

theorem disjoint_union_left : Disjoint (union f g) k ↔ Disjoint f k ∧ Disjoint g k := by
  constructor
  · intro h
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> rcases h a with e | e
    · exact .inl (union_eq_none.mp e).1
    · exact .inr e
    · exact .inl (union_eq_none.mp e).2
    · exact .inr e
  · rintro ⟨h₁, h₂⟩ a
    rcases h₁ a with e₁ | e₁
    · rcases h₂ a with e₂ | e₂
      · exact .inl (union_eq_none.mpr ⟨e₁, e₂⟩)
      · exact .inr e₂
    · exact .inr e₁

theorem disjoint_union_right : Disjoint f (union g k) ↔ Disjoint f g ∧ Disjoint f k := by
  rw [disjoint_comm, disjoint_union_left, disjoint_comm (f := g), disjoint_comm (f := k)]

theorem Le.refl (f : PMap α β) : Le f f := fun _ _ e => e

theorem le_union_left (f g : PMap α β) : Le f (union f g) := fun _ _ e => union_of_some e

theorem le_union_right (h : Disjoint f g) : Le g (union f g) := by
  intro a v e
  rcases h a with e' | e'
  · rw [union_of_none e', e]
  · simp_all

theorem reval_union (f g s : PMap α β) : reval (union f g) s = union (reval f s) (reval g s) := by
  funext a
  simp only [reval, union]
  rcases Option.eq_none_or_eq_some (f a) with e | ⟨v, e⟩
  · simp [e]
  · simp only [e, Option.isSome_some, ↓reduceIte]
    cases s a <;> simp

theorem reval_disjoint (h : Disjoint f g) (s : PMap α β) : Disjoint (reval f s) (reval g s) := by
  intro a
  rcases h a with e | e <;> simp [reval, e]

theorem reval_le (f s : PMap α β) : Le (reval f s) s := by
  intro a v e
  simp only [reval] at e
  split at e
  · exact e
  · cases e

theorem reval_of_le (hl : Le f s) : reval f s = f := by
  funext a
  simp only [reval]
  cases e : f a with
  | none => rfl
  | some v => simp [hl a v e]

theorem reval_empty (s : PMap α β) : reval empty s = empty := by funext a; rfl

theorem single_apply_self [DecidableEq α] (a : α) (v : β) : single a v a = some v := by
  simp [single]

theorem reval_single [DecidableEq α] (a : α) (v w : β) (hs : s a = some w) :
    reval (single a v) s = single a w := by
  funext a'
  simp only [reval, single]
  by_cases h : a' = a
  · subst h; simp [hs]
  · simp [h]

/-- Outside the domain of `f`, a union with `f` on the left is the right map. -/
theorem union_eq_of_agree {f g g' : PMap α β} (h : ∀ a, f a = none → g a = g' a) :
    union f g = union f g' := by
  funext a
  simp only [union]
  cases e : f a with
  | none => simp [h a e]
  | some v => rfl

end PMap

/-! ## `Sep.Frag` is a `PMap` -/

theorem frag_union (h₁ h₂ : Frag) : Frag.union h₁ h₂ = PMap.union h₁ h₂ := by
  funext l; simp only [Frag.union, PMap.union]; cases h₁ l <;> rfl
theorem frag_disjoint (h₁ h₂ : Frag) : Frag.Disjoint h₁ h₂ = PMap.Disjoint h₁ h₂ := rfl
theorem frag_le (h₁ h₂ : Frag) : Frag.Le h₁ h₂ = PMap.Le h₁ h₂ := rfl
theorem frag_reval (h₁ h₂ : Frag) : Frag.reval h₁ h₂ = PMap.reval h₁ h₂ := by
  funext l; simp only [Frag.reval, PMap.reval]
theorem frag_empty : (Frag.empty : Frag) = PMap.empty := rfl

/-! ## Fragments with XMM registers -/

namespace XFrag

variable {a b c h s : XFrag}

theorem ext' {h₁ h₂ : XFrag} (e₁ : h₁.1 = h₂.1) (e₂ : h₁.2 = h₂.2) : h₁ = h₂ :=
  Prod.ext e₁ e₂

theorem empty_union (h : XFrag) : union empty h = h :=
  Prod.ext (PMap.empty_union h.1) (PMap.empty_union h.2)

theorem union_empty (h : XFrag) : union h empty = h :=
  Prod.ext (PMap.union_empty h.1) (PMap.union_empty h.2)

theorem union_assoc (a b c : XFrag) : union (union a b) c = union a (union b c) :=
  Prod.ext (PMap.union_assoc a.1 b.1 c.1) (PMap.union_assoc a.2 b.2 c.2)

theorem Disjoint.symm (h : Disjoint a b) : Disjoint b a :=
  ⟨PMap.Disjoint.symm h.1, PMap.Disjoint.symm h.2⟩

theorem disjoint_empty_left (h : XFrag) : Disjoint empty h :=
  ⟨PMap.disjoint_empty_left h.1, PMap.disjoint_empty_left h.2⟩

theorem disjoint_empty_right (h : XFrag) : Disjoint h empty :=
  ⟨PMap.disjoint_empty_right h.1, PMap.disjoint_empty_right h.2⟩

theorem union_comm (h : Disjoint a b) : union a b = union b a :=
  Prod.ext (PMap.union_comm h.1) (PMap.union_comm h.2)

theorem disjoint_union_left : Disjoint (union a b) c ↔ Disjoint a c ∧ Disjoint b c := by
  simp only [Disjoint, union]
  rw [PMap.disjoint_union_left, PMap.disjoint_union_left]
  tauto

theorem disjoint_union_right : Disjoint a (union b c) ↔ Disjoint a b ∧ Disjoint a c := by
  simp only [Disjoint, union]
  rw [PMap.disjoint_union_right, PMap.disjoint_union_right]
  tauto

theorem Le.refl (h : XFrag) : Le h h := ⟨fun _ _ e => e, PMap.Le.refl h.2⟩

theorem le_union_left (a b : XFrag) : Le a (union a b) :=
  ⟨PMap.le_union_left a.1 b.1, PMap.le_union_left a.2 b.2⟩

theorem le_union_right (h : Disjoint a b) : Le b (union a b) :=
  ⟨PMap.le_union_right h.1, PMap.le_union_right h.2⟩

theorem reval_union (a b s : XFrag) : reval (union a b) s = union (reval a s) (reval b s) :=
  Prod.ext (PMap.reval_union a.1 b.1 s.1) (PMap.reval_union a.2 b.2 s.2)

theorem reval_disjoint (h : Disjoint a b) (s : XFrag) : Disjoint (reval a s) (reval b s) :=
  ⟨PMap.reval_disjoint h.1 s.1, PMap.reval_disjoint h.2 s.2⟩

theorem reval_le (h s : XFrag) : Le (reval h s) s := ⟨PMap.reval_le h.1 s.1, PMap.reval_le h.2 s.2⟩

theorem reval_of_le (hl : Le h s) : reval h s = h :=
  Prod.ext (PMap.reval_of_le hl.1) (PMap.reval_of_le hl.2)

end XFrag

/-! ## The separation-logic laws -/

theorem xsep_comm (P Q : XSProp) : (P ∗ₓ Q) = (Q ∗ₓ P) := by
  funext h
  apply propext
  constructor <;>
  · rintro ⟨a, b, hd, rfl, ha, hb⟩
    exact ⟨b, a, XFrag.Disjoint.symm hd, XFrag.union_comm hd, hb, ha⟩

theorem xsep_assoc (P Q R : XSProp) : ((P ∗ₓ Q) ∗ₓ R) = (P ∗ₓ (Q ∗ₓ R)) := by
  funext h
  apply propext
  constructor
  · rintro ⟨ab, c, hd, rfl, ⟨a, b, hab, rfl, ha, hb⟩, hc⟩
    rw [XFrag.disjoint_union_left] at hd
    exact ⟨a, XFrag.union b c, XFrag.disjoint_union_right.mpr ⟨hab, hd.1⟩,
      XFrag.union_assoc a b c, ha, b, c, hd.2, rfl, hb, hc⟩
  · rintro ⟨a, bc, hd, rfl, ha, ⟨b, c, hbc, rfl, hb, hc⟩⟩
    rw [XFrag.disjoint_union_right] at hd
    exact ⟨XFrag.union a b, c, XFrag.disjoint_union_left.mpr ⟨hd.2, hbc⟩,
      (XFrag.union_assoc a b c).symm, ⟨a, b, hd.1, rfl, ha, hb⟩, hc⟩

theorem xemp_sep (P : XSProp) : (xemp ∗ₓ P) = P := by
  funext h
  apply propext
  constructor
  · rintro ⟨a, b, -, rfl, rfl, hb⟩
    rwa [XFrag.empty_union]
  · intro hp
    exact ⟨XFrag.empty, h, XFrag.disjoint_empty_left h, (XFrag.empty_union h).symm, rfl, hp⟩

theorem xsep_emp (P : XSProp) : (P ∗ₓ xemp) = P := by
  rw [xsep_comm, xemp_sep]

instance : Std.Associative xsep := ⟨xsep_assoc⟩
instance : Std.Commutative xsep := ⟨xsep_comm⟩
instance : Std.LawfulIdentity xsep xemp where
  left_id := xemp_sep
  right_id := xsep_emp

theorem xsep_left_comm (P Q R : XSProp) : (P ∗ₓ Q ∗ₓ R) = (Q ∗ₓ P ∗ₓ R) := by
  rw [← xsep_assoc, xsep_comm P Q, xsep_assoc]

theorem xentails_refl (P : XSProp) : P ⊢ₓ P := fun _ h => h

theorem xentails_trans {P Q R : XSProp} (h₁ : P ⊢ₓ Q) (h₂ : Q ⊢ₓ R) : P ⊢ₓ R :=
  fun h hp => h₂ h (h₁ h hp)

theorem xsep_mono {P P' Q Q' : XSProp} (hp : P ⊢ₓ P') (hq : Q ⊢ₓ Q') : (P ∗ₓ Q) ⊢ₓ (P' ∗ₓ Q') := by
  rintro h ⟨a, b, hd, rfl, ha, hb⟩
  exact ⟨a, b, hd, rfl, hp a ha, hq b hb⟩

theorem xsexists_sep {α : Sort _} (P : α → XSProp) (Q : XSProp) :
    (xsexists P ∗ₓ Q) = xsexists fun a => P a ∗ₓ Q := by
  funext h
  apply propext
  constructor
  · rintro ⟨a, b, hd, rfl, ⟨x, ha⟩, hb⟩
    exact ⟨x, a, b, hd, rfl, ha, hb⟩
  · rintro ⟨x, a, b, hd, rfl, ha, hb⟩
    exact ⟨a, b, hd, rfl, ⟨x, ha⟩, hb⟩

theorem xspure_sep_apply (φ : Prop) (P : XSProp) (h : XFrag) : (⌜φ⌝ₓ ∗ₓ P) h ↔ φ ∧ P h := by
  constructor
  · rintro ⟨a, b, -, rfl, ⟨rfl, hφ⟩, hb⟩
    rw [XFrag.empty_union]; exact ⟨hφ, hb⟩
  · rintro ⟨hφ, hp⟩
    exact ⟨XFrag.empty, h, XFrag.disjoint_empty_left h, (XFrag.empty_union h).symm, ⟨rfl, hφ⟩, hp⟩

theorem xsep_xspure_apply (φ : Prop) (P : XSProp) (h : XFrag) : (P ∗ₓ ⌜φ⌝ₓ) h ↔ P h ∧ φ := by
  rw [xsep_comm, xspure_sep_apply, and_comm]

/-- **Splitting under a containment**: the two parts of a separating conjunction contained in
`s` are each contained in `s`. -/
theorem xsep_le {P Q : XSProp} {h s : XFrag} (hpq : (P ∗ₓ Q) h) (hl : XFrag.Le h s) :
    ∃ a b, P a ∧ Q b ∧ XFrag.Le a s ∧ XFrag.Le b s ∧ XFrag.Disjoint a b ∧
      h = XFrag.union a b := by
  obtain ⟨a, b, hd, rfl, ha, hb⟩ := hpq
  refine ⟨a, b, ha, hb, ?_, ?_, hd, rfl⟩
  · exact ⟨fun l v e => hl.1 l v (PMap.le_union_left a.1 b.1 l v e),
      fun r v e => hl.2 r v (PMap.le_union_left a.2 b.2 r v e)⟩
  · exact ⟨fun l v e => hl.1 l v (PMap.le_union_right hd.1 l v e),
      fun r v e => hl.2 r v (PMap.le_union_right hd.2 r v e)⟩

/-- Re-valuation distributes over a separating conjunction. -/
theorem xsep_reval {P Q P' Q' : XSProp} {h : XFrag} (s : XFrag) (hpq : (P ∗ₓ Q) h)
    (hp : ∀ a, P a → P' (XFrag.reval a s)) (hq : ∀ b, Q b → Q' (XFrag.reval b s)) :
    (P' ∗ₓ Q') (XFrag.reval h s) := by
  obtain ⟨a, b, hd, rfl, ha, hb⟩ := hpq
  exact ⟨_, _, XFrag.reval_disjoint hd s, XFrag.reval_union a b s, hp a ha, hq b hb⟩

end Silmaril.X86.Sep.Xmm
