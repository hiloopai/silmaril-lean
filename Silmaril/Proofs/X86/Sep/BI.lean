module

public import Silmaril.X86.Sep.BI.Defs
/-!
# Proofs: the BI laws for predicates over a separation algebra, and for `SProp`

Behind `Silmaril/Machine/X86/Sep/BI/Thms.lean`. The statements follow iris-lean's `BI`
(`fb21a8af`, `Iris/Iris/BI/BI.lean`); the proofs here are written for this file (no proof
text is copied from iris-lean's classical heap instance). `later` is the identity, so the
later laws are trivial; the `persistently` laws use only `unit_disjoint` and `unit_union`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.BI

open Silmaril.X86.Sep.BI

universe u

variable {α : Type u} [SepAlg α]

theorem sep_symm {P Q : α → Prop} : entails (sep P Q) (sep Q P) := by
  rintro _ ⟨h₁, h₂, hd, rfl, hp, hq⟩
  exact ⟨h₂, h₁, SepAlg.disjoint_symm hd, SepAlg.union_comm hd, hq, hp⟩

theorem sep_assoc_l {P Q R : α → Prop} : entails (sep (sep P Q) R) (sep P (sep Q R)) := by
  rintro _ ⟨_, h₃, hd, rfl, ⟨h₁, h₂, hd', rfl, hp, hq⟩, hr⟩
  obtain ⟨d₂₃, d₁₂₃⟩ := SepAlg.disjoint_assoc hd' hd
  exact ⟨h₁, SepAlg.union h₂ h₃, d₁₂₃, SepAlg.union_assoc hd' hd, hp, h₂, h₃, d₂₃, rfl, hq, hr⟩

theorem emp_sep {P : α → Prop} : (ops α).BiEntails ((ops α).sep (ops α).emp P) P where
  mp := by
    rintro _ ⟨_, h₂, _, rfl, rfl, hp⟩
    show P (SepAlg.union SepAlg.unit h₂)
    rw [SepAlg.unit_union]; exact hp
  mpr h hp := ⟨SepAlg.unit, h, SepAlg.unit_disjoint, SepAlg.unit_union.symm, rfl, hp⟩

theorem persistently_and_l {P Q : α → Prop} :
    (ops α).Entails ((ops α).and ((ops α).persistently P) Q) ((ops α).sep P Q) :=
  fun h ⟨hp, hq⟩ => ⟨SepAlg.unit, h, SepAlg.unit_disjoint, SepAlg.unit_union.symm, hp, hq⟩

/-- The BI laws for predicates over any separation algebra. -/
theorem laws : Laws (ops α) where
  entails_refl _ h := h
  entails_trans h₁ h₂ x hp := h₂ x (h₁ x hp)
  equiv_iff {P Q} := by
    constructor
    · rintro rfl; exact ⟨fun _ h => h, fun _ h => h⟩
    · rintro ⟨h₁, h₂⟩; funext x; exact propext ⟨h₁ x, h₂ x⟩
  pure_intro hφ _ _ := hφ
  pure_elim' h x hφ := h hφ x trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h₁ h₂ x hp := ⟨h₁ x hp, h₂ x hp⟩
  or_intro_l _ h := Or.inl h
  or_intro_r _ h := Or.inr h
  or_elim h₁ h₂ x h := h.elim (h₁ x) (h₂ x)
  imp_intro h x hp hq := h x ⟨hp, hq⟩
  imp_elim h x hpq := h x hpq.1 hpq.2
  sForall_intro h x hp p hΨ := h p hΨ x hp
  sForall_elim hΨ _ h := h _ hΨ
  sExists_intro hΨ _ h := ⟨_, hΨ, h⟩
  sExists_elim h x := fun ⟨p, hΦ, hp⟩ => h p hΦ x hp
  sep_mono h₁ h₂ := by
    rintro _ ⟨a, b, hd, rfl, hp, hq⟩
    exact ⟨a, b, hd, rfl, h₁ a hp, h₂ b hq⟩
  emp_sep := emp_sep
  sep_symm := sep_symm
  sep_assoc_l := sep_assoc_l
  wand_intro h x hp y hd hq := h _ ⟨x, y, hd, rfl, hp, hq⟩
  wand_elim h := by
    rintro _ ⟨a, b, hd, rfl, hp, hq⟩
    exact h a hp b hd hq
  persistently_mono h _ hp := h _ hp
  persistently_idem_2 _ hp := hp
  persistently_emp_2 _ _ := rfl
  persistently_and_2 _ h := h
  persistently_absorb_l _ := fun ⟨_, _, _, _, hp, _⟩ => hp
  persistently_and_l := persistently_and_l
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 {Φ} x h p hΦ :=
    h ((ops α).imp ((ops α).pure (Φ p)) p) ⟨p, rfl⟩ hΦ
  later_sExists_false {Φ} x := fun ⟨p, hΦ, hp⟩ =>
    Or.inr ⟨(ops α).and ((ops α).pure (Φ p)) p, ⟨p, rfl⟩, hΦ, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := Or.inr fun _ => h

open Silmaril.X86.Sep (SProp Frag Loc Val)

/-- `Frag.union` is the partial-map union (same body, different matcher). -/
theorem frag_union_eq : (Frag.union : Frag → Frag → Frag) = SepAlg.pmapUnion := by
  funext a b l; simp only [Frag.union, SepAlg.pmapUnion]; cases a l <;> rfl

theorem sep_eq : Silmaril.X86.Sep.sep = sep (α := Frag) := by
  unfold Silmaril.X86.Sep.sep sep; rw [frag_union_eq]; rfl

theorem wand_eq : Silmaril.X86.Sep.wand = wand (α := Frag) := by
  unfold Silmaril.X86.Sep.wand wand; rw [frag_union_eq]; rfl

/-- `sprop` is `ops Frag` for the partial-map separation algebra. -/
theorem sprop_eq_ops : sprop = ops Frag := by
  unfold sprop ops; rw [sep_eq, wand_eq]; rfl

theorem sprop_laws : Laws sprop := sprop_eq_ops ▸ laws

theorem spure_eq (φ : Prop) :
    Silmaril.X86.Sep.spure φ = sprop.and sprop.emp (sprop.pure φ) := rfl

theorem not_affine : sprop.emp ≠ (fun _ => True) := by
  intro e
  have : Silmaril.X86.Sep.emp (Frag.single Loc.rip (Val.word 0)) :=
    (congrFun e _).mpr trivial
  have h := congrFun this Loc.rip
  simp [Frag.single, Frag.empty] at h

/-- Pure assertions are persistent (iris's `Persistent ⌜φ⌝`). -/
theorem pure_persistent (φ : Prop) :
    sprop.Entails (sprop.pure φ) (sprop.persistently (sprop.pure φ)) :=
  fun _ h => h

/-- The affine `spure φ` is persistent too. -/
theorem spure_persistent (φ : Prop) :
    sprop.Entails (Silmaril.X86.Sep.spure φ)
      (sprop.persistently (Silmaril.X86.Sep.spure φ)) :=
  fun _ h => ⟨rfl, h.2⟩

end Silmaril.Proofs.X86.Sep.BI
