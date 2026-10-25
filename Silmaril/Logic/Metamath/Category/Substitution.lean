module

public import Silmaril.Logic.Metamath.Grammar.Derivation

@[expose] public section

/-!
# Substitution into tree derivations

The tree analogue of `Silmaril.Logic.Metamath.Theory.Substitution`. A tree
derivation in the frame of `A` can be instantiated into a frame `A'` along a
tree substitution `τ` that is well sorted on the floating variables of `A`,
provided every substituted essential hypothesis of `A` is derivable in `A'` and
`τ` carries the disjointness conditions of `A` into those of `A'`
(`TDerivation.subst`). Weakening is a special case.

Dummy variables are combined as lists: `TDummies.union` and `TDummies.append`
keep one floating hypothesis per dummy.
-/

namespace Silmaril.Logic.Metamath.Grammar

universe u

variable {L C V : Type u}

namespace TExpr

theorem subst_subst (σ τ : V → Tree L V) (e : TExpr L C V) :
    (e.subst σ).subst τ = e.subst fun v => (σ v).subst τ := by
  cases e; simp [subst, Tree.subst_subst]

theorem subst_congr {σ τ : V → Tree L V} {e : TExpr L C V} (h : ∀ v ∈ e.vars, σ v = τ v) :
    e.subst σ = e.subst τ := by
  cases e; simp only [subst, TExpr.mk.injEq, true_and]; exact Tree.subst_congr h

end TExpr

/-- `τ` carries the disjointness relation `disj` to `disj'`: the images of two
distinct `disj`-disjoint variables share no variable, and their variables are
pairwise `disj'`-disjoint. -/
def DVPreserving (τ : V → Tree L V) (disj disj' : V → V → Prop) : Prop :=
  ∀ a b, a ≠ b → disj a b → ∀ a' ∈ (τ a).vars, ∀ b' ∈ (τ b).vars, a' ≠ b' ∧ disj' a' b'

namespace TAssertion

theorem Disjoint.symm {A : TAssertion L C V} {x y : V} (h : A.Disjoint x y) : A.Disjoint y x :=
  Or.symm h

theorem Disjoint.mono {A A' : TAssertion L C V} (h : A.dv ⊆ A'.dv) {x y : V}
    (hxy : A.Disjoint x y) : A'.Disjoint x y :=
  hxy.imp (fun h' => h h') (fun h' => h h')

/-- A disjointness check survives composition with a disjointness-preserving
substitution. -/
theorem DVSafe.comp {B : TAssertion L C V} {σ τ : V → Tree L V} {disj disj' : V → V → Prop}
    (hσ : B.DVSafe σ disj) (hτ : DVPreserving τ disj disj') :
    B.DVSafe (fun v => (σ v).subst τ) disj' := by
  intro x y hxy a' ha' b' hb'
  obtain ⟨a, ha, ha'⟩ := Tree.mem_vars_subst.1 ha'
  obtain ⟨b, hb, hb'⟩ := Tree.mem_vars_subst.1 hb'
  obtain ⟨hab, hd⟩ := hσ x y hxy a ha b hb
  exact hτ a b hab hd a' ha' b' hb'

theorem mem_allVars_of_mem_essentials {A : TAssertion L C V} {e : TExpr L C V}
    (he : e ∈ A.essentials) {v : V} (hv : v ∈ e.vars) : v ∈ A.allVars := by
  simp only [allVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨_, mem_essentials.1 he, hv⟩

theorem mem_allVars_of_mem_concl {A : TAssertion L C V} {v : V} (hv : v ∈ A.concl.vars) :
    v ∈ A.allVars := List.mem_append_left _ hv

theorem dv_subset_extend (A : TAssertion L C V) (D : TDummies A) : A.dv ⊆ (A.extend D).dv :=
  List.subset_append_left _ _

theorem allVars_subset_extend (A : TAssertion L C V) (D : TDummies A) :
    A.allVars ⊆ (A.extend D).allVars := by
  intro v hv
  simp only [allVars, extend, List.mem_append, List.flatMap_append, List.mem_flatMap] at hv ⊢
  rcases hv with hv | ⟨h, hh, hv⟩
  · exact Or.inl hv
  · exact Or.inr (Or.inl ⟨h, hh, hv⟩)

end TAssertion

namespace TDummies

variable {A : TAssertion L C V}

/-- The dummy variables, in order. -/
def vars (D : TDummies A) : List V := D.floats.map Prod.snd

/-- No dummy variable lies in `S`. -/
def Avoids (D : TDummies A) (S : Finset V) : Prop := ∀ v ∈ D.vars, v ∉ S

theorem vars_not_mem_allVars (D : TDummies A) {v : V} (hv : v ∈ D.vars) : v ∉ A.allVars := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
  exact D.fresh p hp

theorem vars_mem_allVars_extend (D : TDummies A) {v : V} (hv : v ∈ D.vars) :
    v ∈ (A.extend D).allVars := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
  exact TAssertion.mem_allVars_of_ctx (s := p.1) (TAssertion.ctx_extend.2 (Or.inr hp))

theorem none_avoids (S : Finset V) : (none A).Avoids S := by simp [Avoids, vars, none]

/-- The dummies of two proofs in the same frame, together, provided they share
no dummy variable. -/
def union (D₁ D₂ : TDummies A) (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) : TDummies A where
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

@[simp] theorem union_vars (D₁ D₂ : TDummies A) (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (D₁.union D₂ h).vars = D₁.vars ++ D₂.vars := by
  simp [union, vars]

/-- Dummies of an extended frame are dummies of the original frame. -/
def append (D₁ : TDummies A) (D₂ : TDummies (A.extend D₁)) : TDummies A where
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

@[simp] theorem append_vars (D₁ : TDummies A) (D₂ : TDummies (A.extend D₁)) :
    (D₁.append D₂).vars = D₁.vars ++ D₂.vars := by
  simp [append, vars]

theorem Avoids.mono {D : TDummies A} {S T : Finset V} (h : D.Avoids T) (hST : S ⊆ T) :
    D.Avoids S := fun v hv hS => h v hv (hST hS)

theorem Avoids.union {D₁ D₂ : TDummies A} {S : Finset V} (h₁ : D₁.Avoids S)
    (h₂ : D₂.Avoids S) (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) : (D₁.union D₂ h).Avoids S := by
  intro v hv
  rw [union_vars, List.mem_append] at hv
  exact hv.elim (h₁ v) (h₂ v)

theorem Avoids.append {D₁ : TDummies A} {D₂ : TDummies (A.extend D₁)} {S : Finset V}
    (h₁ : D₁.Avoids S) (h₂ : D₂.Avoids S) : (D₁.append D₂).Avoids S := by
  intro v hv
  rw [append_vars, List.mem_append] at hv
  exact hv.elim (h₁ v) (h₂ v)

/-- Dummies of `A` that avoid the variables of `A'` are dummies of `A'`. -/
def transfer {A' : TAssertion L C V} (D : TDummies A) (h : ∀ v ∈ D.vars, v ∉ A'.allVars) :
    TDummies A' where
  floats := D.floats
  dv := D.dv
  fresh p hp := h p.2 (List.mem_map_of_mem hp)
  nodup := D.nodup
  dv_dummy := D.dv_dummy

end TDummies

namespace TAssertion

theorem extend_append (A : TAssertion L C V) (D₁ : TDummies A) (D₂ : TDummies (A.extend D₁)) :
    (A.extend D₁).extend D₂ = A.extend (D₁.append D₂) := by
  simp [extend, TDummies.append]

theorem ctx_union_left {A : TAssertion L C V} (D₁ D₂ : TDummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) (v : V) (s : C) (hv : (A.extend D₁).ctx v s) :
    (A.extend (D₁.union D₂ h)).ctx v s := by
  rcases ctx_extend.1 hv with hv | hv
  · exact ctx_extend.2 (Or.inl hv)
  · exact ctx_extend.2 (Or.inr (List.mem_append_left _ hv))

theorem ctx_union_right {A : TAssertion L C V} (D₁ D₂ : TDummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) (v : V) (s : C) (hv : (A.extend D₂).ctx v s) :
    (A.extend (D₁.union D₂ h)).ctx v s := by
  rcases ctx_extend.1 hv with hv | hv
  · exact ctx_extend.2 (Or.inl hv)
  · exact ctx_extend.2 (Or.inr (List.mem_append_right _ hv))

theorem dv_subset_union_left (A : TAssertion L C V) (D₁ D₂ : TDummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (A.extend D₁).dv ⊆ (A.extend (D₁.union D₂ h)).dv := by
  intro p hp
  simp only [extend, TDummies.union, List.mem_append] at hp ⊢
  tauto

theorem dv_subset_union_right (A : TAssertion L C V) (D₁ D₂ : TDummies A)
    (h : ∀ v ∈ D₁.vars, v ∉ D₂.vars) :
    (A.extend D₂).dv ⊆ (A.extend (D₁.union D₂ h)).dv := by
  intro p hp
  simp only [extend, TDummies.union, List.mem_append] at hp ⊢
  tauto

end TAssertion

namespace TDerivation

variable {G : Grammar L C V} {Γ : Set (TAssertion L C V)} {A A' : TAssertion L C V}

/-- Transport a derivation along an equality of conclusions. -/
def cast {e e' : TExpr L C V} (h : e = e') (d : TDerivation G Γ A e) : TDerivation G Γ A e' :=
  h ▸ d

/-- Instantiate a derivation in the frame of `A` into the frame of `A'` along
`τ`. Each essential hypothesis of `A` is replaced by a derivation of its
instance, and every node's substitution is composed with `τ`. -/
def subst (τ : V → Tree L V) (sorted : ∀ v s, A.ctx v s → G.HasSort A'.ctx (τ v) s)
    (hyps : ∀ e ∈ A.essentials, TDerivation G Γ A' (e.subst τ))
    (dv : DVPreserving τ A.Disjoint A'.Disjoint) :
    {e : TExpr L C V} → TDerivation G Γ A e → TDerivation G Γ A' (e.subst τ)
  | _, hyp he => hyps _ he
  | _, app B hB σ hs premises hσ =>
    (app B hB (fun v => (σ v).subst τ) (fun v s h => (hs v s h).subst sorted)
      (fun e he => ((premises e he).subst τ sorted hyps dv).cast (TExpr.subst_subst σ τ e))
      (hσ.comp dv)).cast (TExpr.subst_subst σ τ B.concl).symm

/-- Weakening: a derivation remains valid in a frame with more floating
hypotheses, essential hypotheses and disjointness conditions. -/
def weaken (hc : ∀ v s, A.ctx v s → A'.ctx v s) (hh : A.essentials ⊆ A'.essentials)
    (hd : A.dv ⊆ A'.dv) : {e : TExpr L C V} → TDerivation G Γ A e → TDerivation G Γ A' e
  | _, hyp he => hyp (hh he)
  | _, app B hB σ hs premises hσ =>
    app B hB σ (fun v s h => (hs v s h).mono hc) (fun e he => (premises e he).weaken hc hh hd)
      (fun x y hxy a ha b hb => (hσ x y hxy a ha b hb).imp_right (TAssertion.Disjoint.mono hd))

/-- Add dummy variables to the frame of a derivation. -/
def extend (D : TDummies A) {e : TExpr L C V} (d : TDerivation G Γ A e) :
    TDerivation G Γ (A.extend D) e :=
  d.weaken (TAssertion.ctx_le_extend D) (by rw [TAssertion.essentials_extend])
    (A.dv_subset_extend D)

end TDerivation

end Silmaril.Logic.Metamath.Grammar
