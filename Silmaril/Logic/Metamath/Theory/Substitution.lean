module

public import Silmaril.Logic.Metamath.Derivation

@[expose] public section

/-!
# Substitution into derivations

A derivation in the frame of `A` can be instantiated into another frame `A'`
along a substitution `τ`, provided every substituted hypothesis of `A` is
derivable in `A'` and `τ` carries the disjointness conditions of `A` into
those of `A'`. This is the argument behind every use of a theorem in a
Metamath proof. Weakening (more hypotheses, more disjointness conditions) and
renaming variables are special cases.

Only pairs of distinct variables matter for disjointness: every node of a
derivation checks `a ≠ b` before using `A.Disjoint a b`.

Dummy variables are handled here as lists: `Dummies.union` and
`Dummies.append` combine the dummies of several derivations in one frame,
keeping one floating hypothesis per dummy.
-/

namespace Silmaril.Logic.Metamath

universe u

variable {C V : Type u}

namespace Subst

/-- Apply `τ` after `σ`. -/
def comp (τ σ : Subst C V) : Subst C V := fun v => Str.subst τ (σ v)

/-- The substitution replacing each variable `v` by the variable `ρ v`. -/
def rename (ρ : V → V) : Subst C V := fun v => [Sym.var (ρ v)]

/-- The identity substitution. -/
abbrev id : Subst C V := rename fun v => v

/-- `τ` carries the disjointness relation `disj` to `disj'`: the images of two
distinct `disj`-disjoint variables share no variable, and their variables are
pairwise `disj'`-disjoint. -/
def DVPreserving (τ : Subst C V) (disj disj' : V → V → Prop) : Prop :=
  ∀ a b, a ≠ b → disj a b →
    ∀ a' ∈ Str.vars (τ a), ∀ b' ∈ Str.vars (τ b), a' ≠ b' ∧ disj' a' b'

@[simp] theorem vars_rename (ρ : V → V) (v : V) :
    Str.vars (rename ρ v : Str C V) = [ρ v] := by
  simp [rename]

end Subst

@[simp] theorem Str.subst_id (s : Str C V) : Str.subst Subst.id s = s := Str.subst_var s

@[simp] theorem Expr.subst_id (e : Expr C V) : e.subst Subst.id = e := Expr.subst_var e

theorem Expr.subst_comp (σ τ : Subst C V) (e : Expr C V) :
    (e.subst σ).subst τ = e.subst (τ.comp σ) :=
  Expr.subst_subst σ τ e

theorem Assertion.Disjoint.mono {A A' : Assertion C V} (h : A.dv ⊆ A'.dv) {x y : V}
    (hxy : A.Disjoint x y) : A'.Disjoint x y :=
  hxy.imp (fun h' => h h') (fun h' => h h')

/-- A disjointness check survives composition with a disjointness-preserving
substitution. -/
theorem Assertion.DVSafe.comp {B : Assertion C V} {σ τ : Subst C V}
    {disj disj' : V → V → Prop} (hσ : B.DVSafe σ disj) (hτ : τ.DVPreserving disj disj') :
    B.DVSafe (τ.comp σ) disj' := by
  intro x y hxy a' ha' b' hb'
  obtain ⟨a, ha, ha'⟩ := Str.mem_vars_subst.1 ha'
  obtain ⟨b, hb, hb'⟩ := Str.mem_vars_subst.1 hb'
  obtain ⟨hab, hd⟩ := hσ x y hxy a ha b hb
  exact hτ a b hab hd a' ha' b' hb'

namespace Hyp

/-- Rename the variables of a hypothesis. -/
def rename (ρ : V → V) : Hyp C V → Hyp C V
  | float tc v => float tc (ρ v)
  | ess e => ess (e.subst (Subst.rename ρ))

@[simp] theorem expr_rename (ρ : V → V) (h : Hyp C V) :
    (h.rename ρ).expr = h.expr.subst (Subst.rename ρ) := by
  cases h <;> simp [rename, Expr.subst, Subst.rename]

theorem mem_vars_expr {h : Hyp C V} {v : V} : v ∈ h.expr.vars ↔ v ∈ h.vars := Iff.rfl

end Hyp

namespace Assertion

/-- Rename the variables of an assertion. -/
def rename (ρ : V → V) (A : Assertion C V) : Assertion C V where
  dv := A.dv.map (Prod.map ρ ρ)
  hyps := A.hyps.map (Hyp.rename ρ)
  concl := A.concl.subst (Subst.rename ρ)

@[simp] theorem hypExprs_rename (ρ : V → V) (A : Assertion C V) :
    (A.rename ρ).hypExprs = A.hypExprs.map (Expr.subst (Subst.rename ρ)) := by
  simp [hypExprs, rename, Function.comp_def]

theorem rename_rename (ρ ρ' : V → V) (A : Assertion C V) :
    (A.rename ρ).rename ρ' = A.rename (ρ' ∘ ρ) := by
  have hs : (Subst.rename ρ').comp (Subst.rename ρ) = (Subst.rename (ρ' ∘ ρ) : Subst C V) := by
    funext v; simp [Subst.comp, Subst.rename]
  have hh : ∀ h : Hyp C V, (h.rename ρ).rename ρ' = h.rename (ρ' ∘ ρ) := by
    intro h
    cases h with
    | float => rfl
    | ess e => simp [Hyp.rename, Expr.subst_comp, hs]
  simp only [rename, List.map_map, Expr.subst_comp, hs, Prod.map_comp_map, Assertion.mk.injEq,
    true_and, and_true]
  exact List.map_congr_left (fun h _ => hh h)

theorem rename_id (A : Assertion C V) : A.rename (fun v => v) = A := by
  have hh : ∀ h : Hyp C V, h.rename (fun v => v) = h := by
    intro h; cases h <;> simp [Hyp.rename]
  cases A
  simp only [rename, Prod.map_id', List.map_id', Expr.subst_id, Assertion.mk.injEq, true_and,
    and_true]
  exact (List.map_congr_left (fun h _ => hh h)).trans (List.map_id' _)

/-- Every variable of a hypothesis is mentioned by the assertion. -/
theorem mem_allVars_of_mem_hypExprs {A : Assertion C V} {e : Expr C V} (he : e ∈ A.hypExprs)
    {v : V} (hv : v ∈ e.vars) : v ∈ A.allVars := by
  simp only [hypExprs, List.mem_map] at he
  obtain ⟨h, hh, rfl⟩ := he
  simp only [allVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨h, hh, hv⟩

theorem mem_allVars_of_mem_concl {A : Assertion C V} {v : V} (hv : v ∈ A.concl.vars) :
    v ∈ A.allVars := List.mem_append_left _ hv

theorem mem_hypExprs_extend {A : Assertion C V} {D : Dummies A} {e : Expr C V} :
    e ∈ (A.extend D).hypExprs ↔ e ∈ A.hypExprs ∨ ∃ p ∈ D.floats, e = ⟨p.1, [Sym.var p.2]⟩ := by
  simp only [hypExprs, extend, List.map_append, List.mem_append, List.map_map, List.mem_map,
    Function.comp_def, Hyp.expr_float]
  constructor
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, rfl⟩

theorem hypExprs_subset_extend (A : Assertion C V) (D : Dummies A) :
    A.hypExprs ⊆ (A.extend D).hypExprs :=
  fun _ h => mem_hypExprs_extend.2 (Or.inl h)

theorem dv_subset_extend (A : Assertion C V) (D : Dummies A) : A.dv ⊆ (A.extend D).dv :=
  List.subset_append_left _ _

theorem allVars_subset_extend (A : Assertion C V) (D : Dummies A) :
    A.allVars ⊆ (A.extend D).allVars := by
  intro v hv
  simp only [allVars, extend, List.mem_append, List.flatMap_append, List.mem_flatMap] at hv ⊢
  rcases hv with hv | ⟨h, hh, hv⟩
  · exact Or.inl hv
  · exact Or.inr (Or.inl ⟨h, hh, hv⟩)

end Assertion

namespace Dummies

variable {A : Assertion C V}

/-- The dummy variables, in order. -/
def vars (D : Dummies A) : List V := D.floats.map Prod.snd

/-- No dummy variable lies in `S`. -/
def Avoids (D : Dummies A) (S : Finset V) : Prop := ∀ v ∈ D.vars, v ∉ S

theorem vars_not_mem_allVars (D : Dummies A) {v : V} (hv : v ∈ D.vars) : v ∉ A.allVars := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
  exact D.fresh p hp

theorem vars_mem_allVars_extend (D : Dummies A) {v : V} (hv : v ∈ D.vars) :
    v ∈ (A.extend D).allVars := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
  simp only [Assertion.allVars, Assertion.extend, List.flatMap_append, List.mem_append,
    List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inr ⟨_, ⟨p, hp, rfl⟩, by simp [Hyp.vars, Expr.vars, Str.vars]⟩)

@[simp] theorem none_vars : (none A).vars = [] := rfl

theorem vars_nodup (D : Dummies A) : D.vars.Nodup := D.nodup

theorem none_avoids (S : Finset V) : (none A).Avoids S := by simp [Avoids]

/-- The dummies of two proofs in the same frame, together, provided they share
no dummy variable. -/
def union (D₁ D₂ : Dummies A) (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) : Dummies A where
  floats := D₁.floats ++ D₂.floats
  dv := D₁.dv ++ D₂.dv
  fresh p hp := (List.mem_append.1 hp).elim (D₁.fresh p) (D₂.fresh p)
  nodup := by
    rw [List.map_append]
    exact List.nodup_append.2 ⟨D₁.nodup, D₂.nodup, fun a ha b hb hab => h a ha (hab ▸ hb)⟩
  dv_dummy p hp := by
    simp only [List.map_append, List.mem_append]
    rcases List.mem_append.1 hp with h | h
    · exact (D₁.dv_dummy p h).imp Or.inl Or.inl
    · exact (D₂.dv_dummy p h).imp Or.inr Or.inr

@[simp] theorem union_vars (D₁ D₂ : Dummies A) (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (D₁.union D₂ h).vars = D₁.vars ++ D₂.vars := by
  simp [union, vars]

/-- Dummies of an extended frame are dummies of the original frame. -/
def append (D₁ : Dummies A) (D₂ : Dummies (A.extend D₁)) : Dummies A where
  floats := D₁.floats ++ D₂.floats
  dv := D₁.dv ++ D₂.dv
  fresh p hp := (List.mem_append.1 hp).elim (D₁.fresh p)
    (fun h hA => D₂.fresh p h (A.allVars_subset_extend D₁ hA))
  nodup := by
    rw [List.map_append]
    refine List.nodup_append.2 ⟨D₁.nodup, D₂.nodup, ?_⟩
    rintro a ha b hb rfl
    exact D₂.vars_not_mem_allVars hb (D₁.vars_mem_allVars_extend ha)
  dv_dummy p hp := by
    simp only [List.map_append, List.mem_append]
    rcases List.mem_append.1 hp with h | h
    · exact (D₁.dv_dummy p h).imp Or.inl Or.inl
    · exact (D₂.dv_dummy p h).imp Or.inr Or.inr

@[simp] theorem append_vars (D₁ : Dummies A) (D₂ : Dummies (A.extend D₁)) :
    (D₁.append D₂).vars = D₁.vars ++ D₂.vars := by
  simp [append, vars]

theorem Avoids.mono {D : Dummies A} {S T : Finset V} (h : D.Avoids T) (hST : S ⊆ T) :
    D.Avoids S := fun v hv hS => h v hv (hST hS)

theorem Avoids.union {D₁ D₂ : Dummies A} {S : Finset V} (h₁ : D₁.Avoids S)
    (h₂ : D₂.Avoids S) (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) : (D₁.union D₂ h).Avoids S := by
  intro v hv
  rw [union_vars, List.mem_append] at hv
  exact hv.elim (h₁ v) (h₂ v)

theorem Avoids.append {D₁ : Dummies A} {D₂ : Dummies (A.extend D₁)} {S : Finset V}
    (h₁ : D₁.Avoids S) (h₂ : D₂.Avoids S) : (D₁.append D₂).Avoids S := by
  intro v hv
  rw [append_vars, List.mem_append] at hv
  exact hv.elim (h₁ v) (h₂ v)

end Dummies

namespace Assertion

theorem extend_append (A : Assertion C V) (D₁ : Dummies A) (D₂ : Dummies (A.extend D₁)) :
    (A.extend D₁).extend D₂ = A.extend (D₁.append D₂) := by
  simp [extend, Dummies.append]

theorem hypExprs_subset_union_left (A : Assertion C V) (D₁ D₂ : Dummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (A.extend D₁).hypExprs ⊆ (A.extend (D₁.union D₂ h)).hypExprs := by
  intro e he
  rcases mem_hypExprs_extend.1 he with h | ⟨p, hp, rfl⟩
  · exact mem_hypExprs_extend.2 (Or.inl h)
  · exact mem_hypExprs_extend.2 (Or.inr ⟨p, List.mem_append_left _ hp, rfl⟩)

theorem hypExprs_subset_union_right (A : Assertion C V) (D₁ D₂ : Dummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (A.extend D₂).hypExprs ⊆ (A.extend (D₁.union D₂ h)).hypExprs := by
  intro e he
  rcases mem_hypExprs_extend.1 he with h | ⟨p, hp, rfl⟩
  · exact mem_hypExprs_extend.2 (Or.inl h)
  · exact mem_hypExprs_extend.2 (Or.inr ⟨p, List.mem_append_right _ hp, rfl⟩)

theorem dv_subset_union_left (A : Assertion C V) (D₁ D₂ : Dummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (A.extend D₁).dv ⊆ (A.extend (D₁.union D₂ h)).dv := by
  intro p hp
  simp only [extend, Dummies.union, List.mem_append] at hp ⊢
  tauto

theorem dv_subset_union_right (A : Assertion C V) (D₁ D₂ : Dummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (A.extend D₂).dv ⊆ (A.extend (D₁.union D₂ h)).dv := by
  intro p hp
  simp only [extend, Dummies.union, List.mem_append] at hp ⊢
  tauto

end Assertion

namespace Derivation

variable {Γ : Set (Assertion C V)} {A A' : Assertion C V}

/-- Transport a derivation along an equality of conclusions. -/
def cast {e e' : Expr C V} (h : e = e') (d : Derivation Γ A e) : Derivation Γ A e' := h ▸ d

/-- Instantiate a derivation in the frame of `A` into the frame of `A'` along
`τ`. Each hypothesis of `A` is replaced by a derivation of its instance, and
every node's substitution is composed with `τ`. -/
def subst (τ : Subst C V) (hyps : ∀ e ∈ A.hypExprs, Derivation Γ A' (e.subst τ))
    (dv : τ.DVPreserving A.Disjoint A'.Disjoint) :
    {e : Expr C V} → Derivation Γ A e → Derivation Γ A' (e.subst τ)
  | _, hyp he => hyps _ he
  | _, app B hB σ premises hσ =>
    (app B hB (τ.comp σ)
      (fun e he => ((premises e he).subst τ hyps dv).cast (Expr.subst_comp σ τ e))
      (hσ.comp dv)).cast (Expr.subst_comp σ τ B.concl).symm

/-- Weakening: a derivation remains valid in a frame with more hypotheses and
more disjointness conditions. -/
def weaken (hh : A.hypExprs ⊆ A'.hypExprs) (hd : A.dv ⊆ A'.dv) :
    {e : Expr C V} → Derivation Γ A e → Derivation Γ A' e
  | _, hyp he => hyp (hh he)
  | _, app B hB σ premises hσ =>
    app B hB σ (fun e he => (premises e he).weaken hh hd)
      (fun x y hxy a ha b hb => (hσ x y hxy a ha b hb).imp_right (Assertion.Disjoint.mono hd))

/-- Add dummy variables to the frame of a derivation. -/
def extend (D : Dummies A) {e : Expr C V} (d : Derivation Γ A e) :
    Derivation Γ (A.extend D) e :=
  d.weaken (A.hypExprs_subset_extend D) (A.dv_subset_extend D)

/-- Rename the variables of a derivation. The renaming must keep distinct
disjoint variables distinct. -/
def rename (ρ : V → V) (hρ : ∀ x y, x ≠ y → A.Disjoint x y → ρ x ≠ ρ y) {e : Expr C V}
    (d : Derivation Γ A e) : Derivation Γ (A.rename ρ) (e.subst (Subst.rename ρ)) :=
  d.subst (Subst.rename ρ)
    (fun e he => hyp (by rw [Assertion.hypExprs_rename]; exact List.mem_map_of_mem he))
    (by
      intro a b hab hd a' ha' b' hb'
      simp only [Subst.vars_rename, List.mem_singleton] at ha' hb'
      subst a' b'
      refine ⟨hρ a b hab hd, ?_⟩
      rcases hd with h | h
      · exact Or.inl (List.mem_map_of_mem (f := Prod.map ρ ρ) h)
      · exact Or.inr (List.mem_map_of_mem (f := Prod.map ρ ρ) h))

end Derivation

end Silmaril.Logic.Metamath
